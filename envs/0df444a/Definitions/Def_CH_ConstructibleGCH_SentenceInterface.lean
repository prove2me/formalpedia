-- Prove2me | Definitions.Def_CH_ConstructibleGCH_SentenceInterface
-- name    : CH_ConstructibleGCH_SentenceInterface
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-25T22:49:50.033264+00:00
-- url     : https://prove2.me/theorems/ccdeaa9b-e12c-418a-a066-10879fc90616
-- title:
--   Interpreting the platform GCH sentence in L
-- statement:
--   The proved hierarchy equivalence gives a membership-structure isomorphism to the reference carrier. This library defines that isomorphism and the precise semantic predicates for the platform GCH sentence, including internally represented injections, bijections, finiteness and power sets.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: ; Platform semantic adapters by Wentao Li (Victor), with OpenAI Codex assistance; Andrew Marks, Set Theory, Lemma 21.3 and Corollary 21.4, printed pp. 90–91, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf.

import Definitions.Def_CH_ConstructibleAC_Library15

import Definitions.Def_CH_ConstructibleGCH_HullIteration
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_SentenceBridge -/
section GCHSource_Work_CUGCH_SentenceBridge
set_option autoImplicit false


/-!
Semantic bridge for the Prove2Me GCH sentence.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

The constructible hierarchy equivalence reuses our checked adaptation of
Zike Liu's Lean 4 constructible-universe formalization, Apache-2.0,
commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open FirstOrder FirstOrder.Language
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000

abbrev M := _root_.Constructible.Model.LCarrier.{0}
abbrev E (x y : M) : Prop := x.val ∈ y.val

instance nativePlatformStructure : setLang.Structure M :=
  membershipStructure _root_.Constructible.L

def carrierIso : Carrier ≃[setLang] M where
  toEquiv := nativeCarrierEquiv
  map_fun' := fun f => Empty.elim f
  map_rel' := fun r _ => by cases r; rfl



def SubsetOf (x y : M) : Prop := ∀ z : M, E z x → E z y
def EmptySet (x : M) : Prop := ∀ z : M, ¬E z x
def SuccessorOf (s z : M) : Prop := ∀ a : M, E a s ↔ E a z ∨ a = z
def InductiveSet (w : M) : Prop :=
  (∃ x : M, EmptySet x ∧ E x w) ∧
    ∀ x : M, E x w → ∃ y : M, SuccessorOf y x ∧ E y w
def Omega (w : M) : Prop :=
  InductiveSet w ∧ ∀ z : M, InductiveSet z → SubsetOf w z
def PowerSetOf (p x : M) : Prop := ∀ z : M, E z p ↔ SubsetOf z x
def SingletonOf (s x : M) : Prop := ∀ z : M, E z s ↔ z = x
def DoubletonOf (s x y : M) : Prop := ∀ z : M, E z s ↔ z = x ∨ z = y
def PairOf (p x y : M) : Prop :=
  ∀ z : M, E z p ↔ SingletonOf z x ∨ DoubletonOf z x y
def PairIn (f x y : M) : Prop := ∃ p : M, PairOf p x y ∧ E p f
def Injection (f x y : M) : Prop :=
  (∀ a : M, E a x → ∃ b : M, E b y ∧ PairIn f a b) ∧
    (∀ a b c : M, (E a x ∧ PairIn f a b ∧ PairIn f a c) → b = c) ∧
    ∀ a a' b : M, (E a x ∧ E a' x ∧ PairIn f a b ∧ PairIn f a' b) → a = a'
def Injects (x y : M) : Prop := ∃ f : M, Injection f x y
def Bijection (f x y : M) : Prop :=
  Injection f x y ∧ ∀ b : M, E b y → ∃ a : M, E a x ∧ PairIn f a b
def Equinumerous (x y : M) : Prop := ∃ f : M, Bijection f x y
def FiniteSet (s : M) : Prop :=
  ∃ w : M, Omega w ∧ ∃ n : M, E n w ∧ Equinumerous n s
def GapGCH : Prop :=
  ∀ s : M, ¬FiniteSet s → ∀ p : M, PowerSetOf p s →
    ∀ t : M, (Injects s t ∧ Injects t p) → Equinumerous t s ∨ Equinumerous t p





@[simp] theorem named_mem (v : ℕ → M) (i j : ℕ) :
    Formula.Realize (SFormula.mem i j) v ↔ E (v i) (v j) := by rfl

@[simp] theorem named_eq (v : ℕ → M) (i j : ℕ) :
    Formula.Realize (SFormula.eq i j) v ↔ v i = v j := by rfl

/-- A parameter name is outside the reserved names through `bound`. -/
def Fresh (bound name : ℕ) : Prop := name < 1000 ∨ bound < name



































end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_SentenceBridge


