-- Prove2me | Definitions.Def_OmegaLogic_Semantics
-- name    : OmegaLogic_Semantics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T16:31:59.622911+00:00
-- url     : https://prove2.me/theorems/3503c84a-05fb-4f01-b5bb-065467fbe420
-- title:
--   Ω-logic I: language of set theory, Boolean-valued models $V^B_\alpha$, Ω-validity
-- statement:
--   This file sets up the semantic side of Ω-logic.
--
--   **Language and two-valued satisfaction.** `setLang` is the first-order language of set theory: one binary relation symbol $\in$ and no function symbols. `Sent` is its set of sentences. For a class $S$ of sets, `Sat S φ` says that the structure $(S, \in)$, with the true membership relation, satisfies $\varphi$. `SatTheory S T` says that it satisfies every sentence of $T$.
--
--   **The Boolean-valued universe.** For a complete Boolean algebra $B$, `BVSet B` is the class $V^B$ of $B$-names. A name $\mathrm{mk}(\iota, x, b)$ has potential elements $x_i$, $i \in \iota$, each belonging to it with Boolean value $b_i$. Boolean values are defined by recursion:
--   $$\|x = y\| = \bigwedge_i \Big(a_i \Rightarrow \bigvee_j b_j \wedge \|x_i = y_j\|\Big) \wedge \bigwedge_j \Big(b_j \Rightarrow \bigvee_i a_i \wedge \|x_i = y_j\|\Big),\qquad \|x \in y\| = \bigvee_j b_j \wedge \|x = y_j\|,$$
--   and membership in $V_\alpha$ as computed in $V^B$ is
--   $$\|x \in V_\alpha\| = \bigvee_{\beta < \alpha} \bigwedge_i \big(a_i \Rightarrow \|x_i \in V_\beta\|\big)\qquad(\text{i.e. } \|\exists \beta < \alpha\ x \subseteq V_\beta\|).$$
--   `bvRealize α φ` is the Boolean value of a formula in $V^B_\alpha$. Connectives are interpreted in $B$, and $\|\forall y\,\psi\| = \bigwedge_{y \in V^B} (\|y \in V_\alpha\| \Rightarrow \|\psi(y)\|)$. `BVModels B α φ` means $V^B_\alpha \models \varphi$, that is, $\|\varphi\| = 1$.
--
--   **Ω-validity** (primer, Definition 1.7). `OmegaValid T φ`, written $T \models_\Omega \varphi$, holds iff for every complete Boolean algebra $B$ (with $0 \neq 1$) and every ordinal $\alpha$,
--   $$V^B_\alpha \models T \ \Longrightarrow\ V^B_\alpha \models \varphi.$$
--
--   **Ω-satisfiability** (primer, Definition 3.1 ii). `OmegaSatisfiable T` holds iff $V^B_\alpha \models T$ for some complete Boolean algebra $B$ and some ordinal $\alpha$.
--
--   The universe of sets is `ZFSet.{u}`. Boolean algebras range over `Type u` and ordinals over `Ordinal.{u}`. For $\alpha = 0$ the structure $V^B_0$ is empty.
-- source:
--   Wikipedia, "Ω-logic" (revision oldid=1336097018), section "Analysis" (definition of Ω-validity); formal definitions from J. Bagaria, N. Castells, P. Larson, "An Ω-logic primer", in Set Theory (Trends in Mathematics), Birkhäuser 2006, pp. 1–28, doi:10.1007/3-7643-7692-9_1; online version https://paulblarson.github.io/omegalogicmaster5.pdf, Definition 1.7 (p. 4) and Definition 3.1 ii (p. 22).

import Mathlib

/-!
# Ω-logic, part 1: the language of set theory and Ω-validity

* `OmegaLogic.setLang` : the first-order language of set theory (one binary relation `∈`).
* `OmegaLogic.Sat S φ` : the class `S ⊆ V` with the true membership relation satisfies `φ`.
* `OmegaLogic.BVSet B` : Boolean-valued names, i.e. the Boolean-valued universe `V^B`.
* `OmegaLogic.BVModels B α φ` : `V^B_α ⊨ φ` (Boolean value `1`).
* `OmegaLogic.OmegaValid T φ` : `T ⊨_Ω φ`.
* `OmegaLogic.OmegaSatisfiable T`.

Source: Bagaria–Castells–Larson, *An Ω-logic primer*, Definition 1.7 and Definition 3.1.
-/

namespace OmegaLogic

universe u

/-- Relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive SetRel : ℕ → Type
  | mem : SetRel 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/
def setLang : FirstOrder.Language := ⟨fun _ => Empty, SetRel⟩

/-- Sentences of the language of set theory. -/
abbrev Sent : Type := setLang.Sentence

/-- A class `S` of (Lean) ZF-sets, viewed as an `∈`-structure with the true membership. -/
instance instStructureSet (S : Set ZFSet.{u}) : setLang.Structure S where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun {_} r xs => match r with
    | .mem => (xs 0).1 ∈ (xs 1).1

/-- `Sat S φ` : the structure `(S, ∈)` satisfies the sentence `φ`. -/
def Sat (S : Set ZFSet.{u}) (φ : Sent) : Prop := φ.Realize S

/-- `SatTheory S T` : the structure `(S, ∈)` satisfies every sentence of `T`. -/
def SatTheory (S : Set ZFSet.{u}) (T : Set Sent) : Prop := ∀ ψ ∈ T, Sat S ψ

/-! ### The Boolean-valued universe `V^B` -/

/-- Boolean-valued sets (`B`-names): `mk ι x b` is the name whose `i`-th potential element
`x i` belongs to it with Boolean value `b i`. For a complete Boolean algebra `B`, these
form the Boolean-valued universe `V^B`. -/
inductive BVSet (B : Type u) : Type (u + 1)
  | mk (ι : Type u) (elt : ι → BVSet B) (bv : ι → B)

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Boolean value `‖x = y‖` in `V^B`. -/
def bvEq : BVSet B → BVSet B → B
  | .mk _ x a, .mk _ y b =>
    (⨅ i, a i ⇨ ⨆ j, b j ⊓ bvEq (x i) (y j)) ⊓ (⨅ j, b j ⇨ ⨆ i, a i ⊓ bvEq (x i) (y j))

/-- Boolean value `‖x ∈ y‖` in `V^B`. -/
def bvMem (x : BVSet B) : BVSet B → B
  | .mk _ y b => ⨆ j, b j ⊓ bvEq x (y j)

/-- Boolean value `‖x ∈ V_α‖` in `V^B`, i.e. `‖∃ β < α, x ⊆ V_β‖`, where `V_α` is computed
inside `V^B` (so this is membership in `V^B_α = (V_α)^{V^B}`). -/
def bvInV : Ordinal.{u} → BVSet B → B
  | α, .mk _ x a => ⨆ (β : Ordinal.{u}) (_ : β < α), ⨅ i, a i ⇨ bvInV β (x i)

/-- Evaluation of a term (necessarily a variable) of the language of set theory. -/
def bvTerm {n : ℕ} (xs : Fin n → BVSet B) : setLang.Term (Empty ⊕ Fin n) → BVSet B
  | .var (.inl e) => e.elim
  | .var (.inr i) => xs i
  | .func f _ => Empty.elim f

/-- Boolean value of a formula in the structure `V^B_α`: quantifiers range over the names
`u` weighted by `‖u ∈ V_α‖`. -/
def bvRealize (α : Ordinal.{u}) :
    {n : ℕ} → setLang.BoundedFormula Empty n → (Fin n → BVSet B) → B
  | _, .falsum, _ => ⊥
  | _, .equal t₁ t₂, xs => bvEq (bvTerm xs t₁) (bvTerm xs t₂)
  | _, .rel (l := 2) .mem ts, xs => bvMem (bvTerm xs (ts 0)) (bvTerm xs (ts 1))
  | _, .imp φ ψ, xs => bvRealize α φ xs ⇨ bvRealize α ψ xs
  | _, .all φ, xs => ⨅ y : BVSet B, bvInV α y ⇨ bvRealize α φ (Fin.snoc xs y)

variable (B) in
/-- `V^B_α ⊨ φ`: the sentence `φ` has Boolean value `1` in `V^B_α`. -/
def BVModels (α : Ordinal.{u}) (φ : Sent) : Prop :=
  bvRealize (B := B) α φ Fin.elim0 = ⊤

/-- **Ω-validity** (primer, Definition 1.7): `T ⊨_Ω φ` iff for every complete Boolean
algebra `B` and every ordinal `α`, if `V^B_α ⊨ T` then `V^B_α ⊨ φ`. -/
def OmegaValid (T : Set Sent) (φ : Sent) : Prop :=
  ∀ (B : Type u) [CompleteBooleanAlgebra B] [Nontrivial B] (α : Ordinal.{u}),
    (∀ ψ ∈ T, BVModels B α ψ) → BVModels B α φ

/-- **Ω-satisfiability** (primer, Definition 3.1 ii): some `V^B_α` satisfies `T`. -/
def OmegaSatisfiable (T : Set Sent) : Prop :=
  ∃ (B : Type u) (_ : CompleteBooleanAlgebra B) (_ : Nontrivial B) (α : Ordinal.{u}),
    ∀ ψ ∈ T, BVModels B α ψ

end OmegaLogic


