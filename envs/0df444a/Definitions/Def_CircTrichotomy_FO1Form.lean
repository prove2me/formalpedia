-- Prove2me | Definitions.Def_CircTrichotomy_FO1Form
-- name    : CircTrichotomy_FO1Form
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:22.89993+00:00
-- url     : https://prove2.me/theorems/f07f4267-79ec-4b18-8d83-c3e4729b0018
-- title:
--   One-variable first-order logic $\mathrm{FO}^1[\Sigma,\tau]$ and definability
-- statement:
--   Formulas of $\mathrm{FO}^1[\Sigma,\tau]$ use the single variable $x$: atoms $P_a(t)$, $R(t_0,\dots,t_{r-1})$ for numerical predicates $R$ of $\tau$, and $t=t'$, where terms are $x$ or constants of $\tau$; they are closed under $\neg,\wedge,\vee$ and the quantifiers $\exists x$, $\forall x$. On a word $w$ positions range over $[0,|w|-1]$. A **sentence** has no free variable; its language is $L(\varphi)=\{w\in\Sigma^+ : w\models\varphi\}$, and $L$ is **definable** if $L=L(\varphi)$ for some sentence.
--
--   With $\tau=\mathrm{arb}$ this is the logic of the $O(1)$-characterization.
--
--   **Formalization Note** Nested quantifiers rebind $x$. A sentence does not depend on the value of $x$; it is evaluated with $x=0$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.5, p.20

import Mathlib
import Definitions.Def_CircTrichotomy_Vocab

set_option autoImplicit false

namespace CircTrichotomy

/-- Formulas of the **one-variable fragment `FO¹[Σ, τ]`** of first-order logic over words
(Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.5, p.20): atomic formulas `P_a(t)`, `R(t₀, …, t_{r−1})` (`R` a numerical predicate) and
`t = t′`, whose terms are the single variable `x` or constants, closed under `¬, ∧, ∨` and the
quantifications `∃x`, `∀x` ("FO¹[τ] is the fragment using only the variable x"). -/
inductive FO1Form (α : Type) where
  /-- the letter predicate `P_a(t)` -/
  | letter (a : α) (t : NTerm)
  /-- a numerical predicate applied to terms -/
  | rel (R : Σ r : ℕ, ℕ → (Fin r → ℕ) → Prop) (args : Fin R.1 → NTerm)
  /-- equality of terms -/
  | eq (t t' : NTerm)
  | neg (φ : FO1Form α)
  | or (φ ψ : FO1Form α)
  | and (φ ψ : FO1Form α)
  /-- `∃x φ` -/
  | ex (φ : FO1Form α)
  /-- `∀x φ` -/
  | all (φ : FO1Form α)

/-- Satisfaction `w, [x ↦ a] ⊨ φ` (§A.5, p.20): positions range over `[0, |w| − 1]`, `P_a(i)` holds
iff the `i`-th letter is `a`, numerical predicates and constants are interpreted at length `|w|`. -/
def FO1Form.Sat {α : Type} (w : List α) : FO1Form α → ℕ → Prop
  | letter a t, x => w[t.eval w.length x]? = some a
  | rel R args, x => R.2 w.length (fun i => (args i).eval w.length x)
  | eq t t', x => t.eval w.length x = t'.eval w.length x
  | neg φ, x => ¬ φ.Sat w x
  | or φ ψ, x => φ.Sat w x ∨ ψ.Sat w x
  | and φ ψ, x => φ.Sat w x ∧ ψ.Sat w x
  | ex φ, _ => ∃ b < w.length, φ.Sat w b
  | all φ, _ => ∀ b < w.length, φ.Sat w b

/-- A term without the variable. -/
def NTerm.IsClosed : NTerm → Prop
  | var => False
  | const _ => True

/-- A term all of whose constants belong to the vocabulary `V`. -/
def NTerm.InVocab (V : Vocab) : NTerm → Prop
  | var => True
  | const c => c ∈ V.consts

/-- `φ` is a sentence: the variable `x` has no free occurrence. -/
def FO1Form.IsSentence {α : Type} : FO1Form α → Prop
  | letter _ t => t.IsClosed
  | rel _ args => ∀ i, (args i).IsClosed
  | eq t t' => t.IsClosed ∧ t'.IsClosed
  | neg φ => φ.IsSentence
  | or φ ψ => φ.IsSentence ∧ ψ.IsSentence
  | and φ ψ => φ.IsSentence ∧ ψ.IsSentence
  | ex _ => True
  | all _ => True

/-- Every constant and numerical predicate of `φ` belongs to the vocabulary `V`. -/
def FO1Form.InVocab {α : Type} (V : Vocab) : FO1Form α → Prop
  | letter _ t => t.InVocab V
  | rel R args => R ∈ V.rels ∧ ∀ i, (args i).InVocab V
  | eq t t' => t.InVocab V ∧ t'.InVocab V
  | neg φ => φ.InVocab V
  | or φ ψ => φ.InVocab V ∧ ψ.InVocab V
  | and φ ψ => φ.InVocab V ∧ ψ.InVocab V
  | ex φ => φ.InVocab V
  | all φ => φ.InVocab V

/-- **`L` is definable in `FO¹[Σ, V]`** (§A.5, p.20): "A sentence is a formula with no free
variable. The language L(φ) of a sentence φ is the set of all words satisfying φ. A language
L ⊆ Σ⁺ is defined by the sentence φ if L(φ) = L."

**Formalization Note** Words are non-empty (a structure has the domain `[0, |w| − 1]`), so
`L(φ) = {w ∈ Σ⁺ | w ⊨ φ}`; a sentence does not depend on the value of `x`, which is set to `0`. -/
def FO1Definable {α : Type} (V : Vocab) (L : Language α) : Prop :=
  ∃ φ : FO1Form α, φ.IsSentence ∧ φ.InVocab V ∧
    L = {w | w ≠ [] ∧ φ.Sat w 0}

end CircTrichotomy


