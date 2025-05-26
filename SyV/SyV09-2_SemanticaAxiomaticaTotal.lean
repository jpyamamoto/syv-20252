/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude
import SyV.SyV06_SemanticaOperacional_PasoGrande


/- # Clase 9 (Parte 2): Corrección Total. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace SyV

/- ## Ternas de Hoare para corrección total

La __corrección total__ afirma que un programa no sólo es parcialmente
correcto, sino que también termina con normalidad en todos los casos. Las
ternas de Hoare para corrección total son de la forma

    [P] S [Q]

Que se leé como:

    Si `P` se satisface antes de que se ejecute `S`, la ejecución termina
    con normalidad y `Q` se satisface en el estado final.

Para programas deterministas, se tiene la siguiente formulación equivalente:

    Si `P` se satisface antes de la ejecución de `S`, existe un estado en que
    la ejecución termina con normalidad y `Q` se satisface en tal estado.

Ejemplo:

    `[i ≤ 100] while i ≠ 100 do i := i + 1 [i = 100]`

En el lenguaje WHILE, esto únicamente afecta a los ciclos while, que ahora
deben anotarse con una __variante__ `V` (un número natural que decrementa
con cada iteración):

    [I ∧ B ∧ V = v₀] S [I ∧ V < v₀]
    ——————————————————————————————— While-Var
    [I] while B do S [I ∧ ¬B]

La siguiente definición captura las ternas de Hoare para la corrección total
en los lenguajes deterministas: -/

def TotalHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

macro "[*" P:term " *] " "(" S:term ")" " [* " Q:term " *]" : term =>
  `(TotalHoare $P $S $Q)

namespace TotalHoare

/- Demostración de la regla de consecuencia. -/

theorem consequence {P P' Q Q' S}
    (hS : [* P *] (S) [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
  [* P' *] (S) [* Q' *] := by
  intro s h
  cases hS s (hP s h)
  apply Exists.intro w
  cases h_1
  apply And.intro
  . exact left
  . apply hQ w right

/- Demostración de la regla para `skip`. -/

theorem skip_intro {P} :
  [* P *] (Stmt.skip) [* P *] := by
  intro s h
  apply Exists.intro s
  apply And.intro
  . apply BigStep.skip
  . exact h

/- Demostración de la regla para `assign`. -/

theorem assign_intro {P x a} :
  [* fun s ↦ P (s[x ↦ a s]) *] (Stmt.assign x a) [* P *] := by
  intro s h
  apply Exists.intro (State.update x (a s) s)
  apply And.intro
  . apply BigStep.assign x
  . exact h

/- Demostración de la regla para `comp`. -/

theorem comp_intro {P Q R S T} (hS : [* P *] (S) [* Q *])
  (hT : [* Q *] (T) [* R *]) :
  [* P *] (S; T) [* R *] := by
  intro s h
  cases hS s h
  cases h_1
  cases hT w right
  cases h_1
  apply Exists.intro w_1
  apply And.intro
  . apply BigStep.comp S T s w w_1 left left_1
  . exact right_1

/- Demostración de la regla para `if`–`then`–`else`.

Nota: La demostración requiere un análisis de casos sobre el valor de verdad
de `B s`. -/

theorem if_intro {B P Q S T}
    (hS : [* fun s ↦ P s ∧ B s *] (S) [* Q *])
    (hT : [* fun s ↦ P s ∧ ¬ B s *] (T) [* Q *]) :
  [* P *] (Stmt.ifThenElse B S T) [* Q *] := by
  intro s h
  cases Classical.em (B s)
  . cases hS s (And.intro h h_1)
    cases h_2
    apply Exists.intro w
    apply And.intro
    . apply BigStep.if_true B S T _ _ h_1 left
    . exact right
  . cases hT s (And.intro h h_1)
    cases h_2
    apply Exists.intro w
    apply And.intro
    . apply BigStep.if_false B S T _ _ h_1 left
    . exact right

/- Demostración de la regla para `while`.

Nota: La regla está parametrizada por una invariante de ciclo `I` y una
variante `V` que se decrementa con cada iteración del cuerpo del ciclo.

Antes de demostrar el teorema de interés, introducimos un teorema auxiliar.
Su demostración requiere inducción por emparejamiento de patrones y recursión.
Al utilizar `var_while_intro_aux` como hipótesis de inducción, es recomendable
hacerlo inmediatamente después de demostrar que el argumento es menor a `v₀`:

    have ih : ∃u, (stmt.while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
      have _ : V t < v₀ :=
        …
      var_while_intro_aux I V h_inv (V t) …

De forma similar al `if`--`then`--`else`, la demostración requiere un
análisis de casos sobre el valor de verdad de `B s`. -/

theorem var_while_intro_aux {B} (I : State → Prop) (V : State → ℕ) {S}
  (h_inv : ∀v₀,
     [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
  ∀v₀ s, V s = v₀ → I s → ∃t, (Stmt.whileDo B S, s) ⟹ t ∧ I t ∧ ¬ B t
  | v₀, s, V_eq, hs =>
    by
      cases Classical.em (B s)
      . cases (h_inv v₀) s (And.intro hs (And.intro h V_eq))
        cases h_1
        have ih : ∃u, (Stmt.whileDo B S, w) ⟹ u ∧ I u ∧ ¬ B u :=
          have _ : V w < v₀ := by
            simp at right
            cases right
            exact right_1
          var_while_intro_aux I V h_inv (V w) w rfl (
              by simp at right; apply And.left right
            )
        cases ih
        apply Exists.intro w_1
        apply And.intro
        . cases h_1
          exact BigStep.while_true B S s w w_1 h left left_1
        . cases h_1
          exact right_1
      . apply Exists.intro s
        apply And.intro
        . apply BigStep.while_false B S s
          exact h
        . exact And.intro hs h

theorem var_while_intro {B} (I : State → Prop) (V : State → ℕ) {S}
  (hinv : ∀v₀,
     [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
  [* I *] (Stmt.whileDo B S) [* fun s ↦ I s ∧ ¬ B s *] := by
  intro s t
  simp
  exact var_while_intro_aux I V hinv (V s) s rfl t

end TotalHoare

end SyV
