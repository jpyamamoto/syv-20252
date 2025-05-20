/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import SyV.SyVPrelude
import SyV.SyV06_SemanticaOperacional_PasoGrande


/- # Clase 10: Semántica Denotacional

Una tercera forma de especificar la semántica de un lenguaje de programación
es mediante la Semántica Denotacional. Esta pretende especificar directamente
el significado de un programa.

Si la semántica operacional es un intérprete ideal, y la semántica axiomática
es un verificador, entonces la semántica denotacional se asemeja a un
compilador ideal. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace SyV


/- ## Composicionalidad

Una __semántica denotacional__ define el significado de cada programa
como un objeto matemático:

    `⟦ ⟧ : sintaxis → semantica`

Una propiedad fundamental de la semántica denotacional es su
__composicionalidad__: El significado de un enunciado compuesto debe
definirse únicamente en términos del significado de sus componentes.
Esto descalifica

    `⟦S⟧ = {st | (S, Prod.fst st) ⟹ Prod.snd st}`

(es decir,

    `⟦S⟧ = {(s, t) | (S, s) ⟹ t}`)

porque la semántica operacional no es composicional.

En resumen, se busca algo como

    `⟦S; T⟧               = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if b then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while b do S⟧       = … ⟦S⟧ …`

Una función de evaluación sobre las expresiones aritméticas

    `eval : AExp → ((String → ℤ) → ℤ)`

es una semántica denotacional. Queremos lo mismo para programas
imperativos.


## Una Semántica Denotacional Relacional

Podemos representar la semántica de un programa imperativo como una
función que va de un estado inicial a un estado final; o más general,
como una relación entre estados iniciales y finales: `Set (State × State)`.

Para `skip`, `:=`, `;` y `if then else`, la semántica denotacional
es sencilla: -/

namespace SorryDefs

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.comp S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo b S      => sorry

end SorryDefs

/- Escribimos `⟦S⟧` para `denote S`. Para `while`, quisieramos escribir

    `((denote S ◯ denote (Stmt.whileDo b S)) ⇃ b)`
    `∪ (Id ⇃ (fun s ↦ ¬ b s))`

pero esto no está bien fundamentado debido a la llamada recursiva
en `Stmt.whileDo b S`.

Lo que buscamos es una `X` tal que

    `X = ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (fun s ↦ ¬ b s))`

En otras palabras, buscamos un **punto fijo**.

Para ello, se construirá un operador que retorna el mínimo punto
fijo `lfp` que nos va a permitir definir el caso del `while`:

    `lfp (fun X ↦ ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (fun s ↦ ¬ b s)))`


## Puntos Fijos

Un __punto fijo__ de `f` es una solución para `X` en la ecuación

    `X = f X`

En general, los puntos fijos pueden no existir (por ejemplo,
dado `f := Nat.succ`) o pueden existir muchos puntos fijos (por ejemplo,
dado `f := id`). Pero bajo ciertas condiciones sobre `f`, se puede
garantizar la existencia de un __mínimo punto fijo__ único y un único
__máximo punto fijo__.

Nota la siguiente __ecuación de punto fijo__:

    `X = (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m) X`
      `= (fun n : ℕ ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

donde `X : ℕ → Prop` y
`f := (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m)`.

El ejemplo anterior admite un único punto fijo. La ecuación de punto
fijo especifica de forma única a `X` como el conjunto de los números
pares.

En general, el mayor y el menor punto fijo pueden ser diferentes:

    `X = X`

Aquí, el mínimo punto fijo es `fun _ ↦ False` y el mayor punto fijo
es `fun _ ↦ True`. Como convención, `False < True`, y por lo tanto
`(fun _ ↦ False) < (fun _ ↦ True)`. Similarmente, `∅ < @Set.univ ℕ`.

Para la semántica de lenguajes de programación:

* `X` tendrá tipo `Set (State × State)` (que es isomorfo a
  `State → State → Prop`), representando relaciones entre estados;

* `f` va a corresponder a tomar una iteración más del ciclo (si la
  condición `B` es verdadera) o la identidad (si `B` es falsa).

El mínimo punto fijo corresponde a las ejecuciones finitas de un
programa, que es el único caso que nos interesa.

**Observación importante**:

    Los predicados inductivos corresponden a puntos fijos mínimos,
    pero estos ya están incrustados en la lógica de Lean (el cálculo
    de construcciones inductivas).


## Funciones Monótonas

Sean `α` y `β` tipos con un orden parcial `≤`. Una función `f : α → β`
es __monótona__ si

    `a₁ ≤ a₂ → f a₁ ≤ f a₂`   para todos `a₁`, `a₂`

Muchas operaciones sobre conjuntos (por ejemplo, `∪`), relaciones
(como `◯`), y funciones (por ejemplo, `fun x ↦ x`, `fun _ ↦ k`, `∘`)
son monótonas o preservan monotonía.

Todas las funciones monótonas `f : Set α → Set α` admiten puntos
fijos mínimos y máximos.

**Ejemplo de una función no-monótona**:

    `f A = (if A = ∅ then Set.univ else ∅)`

Suponiendo que el tipo `α` tiene algún término (está habitado), tenemos
que `∅ ⊆ Set.univ`, pero `f ∅ = Set.univ ⊈ ∅ = f Set.univ`. -/

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β]
  (f : α → β) : Prop :=
  ∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] :
  Monotone (fun a : α ↦ a) :=
  by
    intro a₁ a₂ ha
    exact ha

theorem Monotone_const {α β : Type} [PartialOrder α]
    [PartialOrder β] (b : β) :
  Monotone (fun _ : α ↦ b) :=
  by
    intro a₁ a₂ ha
    exact le_refl b

theorem Monotone_union {α β : Type} [PartialOrder α]
    (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
  Monotone (fun a ↦ f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/- We will prove the following two theorems in the exercise. -/

theorem Monotone_comp {α β : Type} [PartialOrder α]
    (f g : α → Set (β × β)) (hf : Monotone f)
    (hg : Monotone g) :
  Monotone (fun a ↦ f a ◯ g a) := by
  intro a₁ a₂ ha
  simp
  simp [comp]
  intro a b c hac hcb
  apply Exists.intro c
  apply And.intro
  . exact hf a₁ a₂ ha hac
  . exact hg a₁ a₂ ha hcb

theorem Monotone_restrict {α β : Type} [PartialOrder α]
    (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
  Monotone (fun a ↦ f a ⇃ P) := by
  intro a₁ a₂ ha
  simp
  simp [restrict]
  intro a b hab hpa
  apply And.intro
  . exact hf a₁ a₂ ha hab
  . exact hpa


/- ## Latices Completas

Para definir un punto fijo mínimo sobre conjuntos, necesitamos de
las operaciones `⊆` y `⋂`. Las latices completas capturan este
concepto de forma abstracta. Una __latiz completa__ es un tipo
ordenado `α` para el cual cada conjunto de tipo `Set α` tiene ínfimo.

Más precisamente, una latiz completa consiste de

* un orden parcial `≤ : α → α → Prop` (es decir, una relación
  reflexiva, antisimétrica y transitiva, y un predicado binario);

* un operador `Inf : Set α → α`, llamado __ínfimo__.

Además, `Inf A` debe satisface estas dos propiedades:

* `Inf A` es una cota inferior de `A`: `Inf A ≤ b` para toda `b ∈ A`;

* `Inf A` es la mayor cota inferior: `b ≤ Inf A` para toda `b` tal que
  `∀a, a ∈ A → b ≤ a`.

**Advertencia:** `Inf A` no es necesariamente un elemento de `A`.

Ejemplos:

* `Set α` es una instancia con respecto a `⊆` y `⋂` para todo tipo `α`;
* `Prop` es una instancia con respecto a `→` y `∀` (`Inf A := ∀a ∈ A, a`);
* `ENat := ℕ ∪ {∞}`;
* `EReal := ℝ ∪ {- ∞, ∞}`;
* `β → α` si `α` es una latiz completa;
* `α × β` si `α`, `β` son latices completas.

Ejemplo finito:

                Z            Inf {}           = Z
              /   \          Inf {Z}          = Z
             A     B         Inf {A, B}       = Y
              \   /          Inf {Z, A}       = A
                Y            Inf {Z, A, B, Y} = Y

Contraejemplos:

* `ℕ`, `ℤ`, `ℚ`, `ℝ`: no hay ínfimo para `∅`, `Inf ℕ`, etc.
* `ERat := ℚ ∪ {- ∞, ∞}`: `Inf {q | 2 < q * q} = sqrt 2` no está en `ERat`. -/

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf    : Set α → α
  Inf_le : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

/- Para conjuntos: -/

instance Set.CompleteLattice {α : Type} :
  CompleteLattice (Set α) :=
  { @Set.PartialOrder α with
    Inf         := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
    Inf_le      := by aesop
    le_Inf      := by aesop }


/- ## Mínimo Punto Fijo -/

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α : Type} [CompleteLattice α] (f : α → α)
    (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α : Type} [CompleteLattice α] (f : α → α)
    (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/- **Teorema de Knaster-Tarski:** Para cualquier función monótona `f`:

* `lfp f` es un punto fijo: `lfp f = f (lfp f)` (teorema `lfp_eq`);
* `lfp f` es más pequeño que cualquier otro punto fijo:
     `X = f X → lfp f ≤ X`. -/

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
    (hf : Monotone f) :
  lfp f = f (lfp f) :=
  by
    have h : f (lfp f) ≤ lfp f :=
      by
        apply le_lfp
        intro a' ha'
        apply le_trans
        { apply hf
          apply lfp_le
          assumption }
        { assumption }
    apply le_antisymm
    { apply lfp_le
      apply hf
      assumption }
    { assumption }


/- ## Continuación, Una Semántica Denotacional Relacional -/

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.comp S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
      ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S

theorem Monotone_while_lfp_arg (S B) :
  Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) :=
  by
    apply Monotone_union
    { apply Monotone_restrict
      apply Monotone_comp
      { exact Monotone_const _ }
      { exact Monotone_id } }
    { apply Monotone_restrict
      exact Monotone_const _ }


/- ## Aplicación a la Equivalencia de Programas

Con base en la semántica denotacional, podemos introducir una noción
de equivalencia de programas: `S₁ ∼ S₂`. -/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

/- Es obvio de la definición que `~` es una relación de equivalencia.

La equivalencia de programas puede ser utilizada para reemplazar
subprogramas por otros subprogramas con la misma semántica. Esto se
logra por las siguientes reglas de congruencia: -/

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
    (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  S₁; T₁ ~ S₂; T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
    (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
    (hS : S₁ ~ S₂) :
  Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

/- En comparación con la equivalencia mediante la semántica operacional
de paso grande, esto es mucho más sencillo.

Probemos la equivalencia de algunos programas. -/

theorem DenoteEquiv.skip_assign_id {x} :
  Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
  Stmt.skip; S ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.seq_skip_right {S} :
  S; Stmt.skip ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.if_seq_while {B S} :
  Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
  ~ Stmt.whileDo B S :=
  by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


end SyV
