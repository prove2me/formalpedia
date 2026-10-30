-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39
-- name    : QAlgorithms_Papers_Independent_Bridge50_P39
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:46:24.80265+00:00
-- url     : https://prove2.me/theorems/a1e7df4a-2cfa-4b6a-bd5b-632c71f40442
-- title:
--   Definitions for Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels
-- statement:
--   The objects the formalized statements of *Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels* (arXiv:1506.02228) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ordinaryRadius`: PDF pp.10-11, (4.28), with distinct input A and comparison B spaces.
--   - `strongConverseExponent`: PDF p.11, (4.29): the entire order optimization stays in the extended reals.
--   - `FeedbackHistory`: PDF pp.6-7: all past classical outcomes, including the initial Bob-to-Alice X0.
--   - `historyTruncate`: PDF pp.6-7: remove only the latest feedback symbol.
--   - `FeedbackCode`: PDF pp.6-7: a physical n-use code, before selecting the uniform message. All families are fixed parts of the code. Alice may condition her encoder on the classical message and the past transcript; Bob's instrument never receives the message. Arbitrary finite memories can change size at every round. Conditioning on past records also covers Alice's local response to feedback. A final Bob instrument is harmless: it is a local operation that can be absorbed into the final POVM.
--   - `FeedbackCode.Valid`: PDF pp.5-7: physical normalization only, with nonempty messages and n>=1. Initial Bob probabilities and conditional seeds are independent of the message. No separability or information bound is assumed here.
--   - `FeedbackCode.prepare`: PDF p.6, (3.9): encode Alice's block and preserve every Bob off-diagonal block.
--   - `FeedbackCode.transmit`: PDF p.6, (3.11): one use of the SAME N, identity on both retained memories.
--   - `FeedbackCode.branchUpdate`: PDF p.7, (3.13): one actual CP branch of Bob's classical feedback instrument.
--   - `FeedbackCode.branchState`: PDF pp.6-7, (3.7)-(3.14): unnormalized state computed along the complete classical transcript. Zero-probability transcripts stay zero, without division. The only correlation initially shared is Bob's classical X0, not entanglement.
--   - `FeedbackCode.receiver`: PDF pp.7,11: Bob's actual final state, including all classical records. Alice alone is traced out. Different transcripts have no coherent cross terms.
--   - `FeedbackCode.success`: PDF p.11, (4.31): average uniform-message decoding success of this executed code.
--   - `FeedbackCode.error`: PDF pp.11,16: average decoding error, not private or entanglement fidelity.
--   - `uniformMessageRate`: PDF p.14: available uniform-message rate, in bits per individual forward use. Distinct from Gap48.P33.messageRate: its first argument is an integer bit count, whereas L here is an arbitrary message cardinality and log2(L) need not be integral.
--   - `FullySeparablePositive`: PDF p.7, (3.12): the fully separable positive cone on Alice memory, current input, and Bob memory, in that order. For a normalized operator this is exactly a convex mixture of three normalized product states. For an unnormalized branch the coefficient sum is its trace; the zero branch is allowed.
--   - `FeedbackCode.SeparableInputs`: PDF pp.6-7,12-13: in the arbitrary-channel alternative, the ACTUAL encoded state is fully separable in every message/transcript branch, before every use. The record is retained in the branch index; a separable averaged marginal is insufficient. This restriction is never imposed on the EB-channel alternative.
--   - `FeedbackAchievable`: PDF pp.2,18: a vanishing-error code sequence with eventual rate at least R. The index k denotes blocklength k+1. The Bool selects the single-use separable-input restriction, not separability only at boundaries of larger entangled blocks.
--   - `singleUseFeedbackCapacity`: PDF pp.2,18: operational capacity as an extended nonnegative supremum. The definition uses executed codes and vanishing error, independently of entropy. Distinct from Dependency50.P09.feedbackCapacity: that interface has no per-use separable-input selector and uses a worst-message-distribution error criterion. The Bool here selects precisely the single-use input restriction of this paper.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, https://arxiv.org/abs/1506.02228v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

/-!
Ding and Wilde, arXiv:1506.02228v4. Page numbers are PDF pages; logarithms are in bits.
Only pinned accepted libraries are imported. The local code executes each individual
forward use, includes initial classical feedback X0, and retains every classical record.
No norm inequality, information-radius equality, or converse is built into code validity.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal
open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)
open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)
open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)
open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)
open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

/-- PDF pp.10-11, (4.28), with distinct input A and comparison B spaces. -/
def ordinaryRadius {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : EReal :=
  ⨅ sigma : {X : Matrix B B ℂ // IsDensityMatrix X},
    ⨆ rho : {X : Matrix A A ℂ // IsDensityMatrix X}, relativeD (N rho.1) sigma.1

/-- PDF p.11, (4.29): the entire order optimization stays in the extended reals. -/
def strongConverseExponent {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) (R : ℝ) : EReal :=
  ⨆ a : {a : ℝ // 1 < a},
    (((a.1 - 1) / a.1 : ℝ) : EReal) * ((R : EReal) - channelInformation true a.1 N)

/-- PDF pp.6-7: all past classical outcomes, including the initial Bob-to-Alice X0. -/
abbrev FeedbackHistory (initialOutcomes : ℕ) (outcomes : ℕ → ℕ) (j : ℕ) :=
  Fin initialOutcomes × ((t : Fin j) → Fin (outcomes t.val))

/-- PDF pp.6-7: remove only the latest feedback symbol. -/
def historyTruncate {x0 : ℕ} {outcomes : ℕ → ℕ} {j : ℕ}
    (h : FeedbackHistory x0 outcomes (j + 1)) : FeedbackHistory x0 outcomes j :=
  (h.1, fun t => h.2 ⟨t.val, Nat.lt_trans t.isLt (Nat.lt_succ_self j)⟩)

/-- PDF pp.6-7: a physical n-use code, before selecting the uniform message.
All families are fixed parts of the code. Alice may condition her encoder on the
classical message and the past transcript; Bob's instrument never receives the message.
Arbitrary finite memories can change size at every round. Conditioning on past records
also covers Alice's local response to feedback. A final Bob instrument is harmless:
it is a local operation that can be absorbed into the final POVM. -/
structure FeedbackCode (A B : Type) [Fintype A] [Fintype B] (n L : ℕ) where
  aliceDim : ℕ → ℕ
  bobDim : ℕ → ℕ
  initialOutcomes : ℕ
  initialProb : Fin initialOutcomes → ℝ
  aliceInitial : Fin L → Matrix (Fin (aliceDim 0)) (Fin (aliceDim 0)) ℂ
  bobInitial : Fin initialOutcomes → Matrix (Fin (bobDim 0)) (Fin (bobDim 0)) ℂ
  outcomes : ℕ → ℕ
  rank : ℕ → ℕ
  encoder : (j : ℕ) → Fin L → FeedbackHistory initialOutcomes outcomes j →
    Superop (Fin (aliceDim j)) (Fin (aliceDim (j + 1)) × A)
  bobKraus : (j : ℕ) → FeedbackHistory initialOutcomes outcomes j →
    Fin (outcomes j) → Fin (rank j) →
      Matrix (Fin (bobDim (j + 1))) (Fin (bobDim j) × B) ℂ
  decoder : Fin L → Matrix
    (FeedbackHistory initialOutcomes outcomes n × Fin (bobDim n))
    (FeedbackHistory initialOutcomes outcomes n × Fin (bobDim n)) ℂ

/-- PDF pp.5-7: physical normalization only, with nonempty messages and n>=1.
Initial Bob probabilities and conditional seeds are independent of the message.
No separability or information bound is assumed here. -/
def FeedbackCode.Valid {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    {n L : ℕ} (P : FeedbackCode A B n L) : Prop :=
  0 < n ∧ 0 < L ∧ 0 < P.initialOutcomes ∧
  (∀ j ≤ n, 0 < P.aliceDim j ∧ 0 < P.bobDim j) ∧
  (∀ x, 0 ≤ P.initialProb x) ∧ (∑ x, P.initialProb x) = 1 ∧
  (∀ m, IsDensityMatrix (P.aliceInitial m)) ∧
  (∀ x, IsDensityMatrix (P.bobInitial x)) ∧ IsPOVM P.decoder ∧
  ∀ j < n,
    0 < P.outcomes j ∧
    (∀ m h, IsChannel (P.encoder j m h)) ∧
    ∀ h, (∑ x, ∑ k, (P.bobKraus j h x k)ᴴ * P.bobKraus j h x k) = 1

/-- PDF p.6, (3.9): encode Alice's block and preserve every Bob off-diagonal block. -/
def FeedbackCode.prepare {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (j : ℕ) (m : Fin L)
    (h : FeedbackHistory P.initialOutcomes P.outcomes j)
    (X : Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ) :
    Matrix ((Fin (P.aliceDim (j + 1)) × A) × Fin (P.bobDim j))
      ((Fin (P.aliceDim (j + 1)) × A) × Fin (P.bobDim j)) ℂ :=
  tensorAction (P.encoder j m h) id X

/-- PDF p.6, (3.11): one use of the SAME N, identity on both retained memories. -/
def FeedbackCode.transmit {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) (j : ℕ) (m : Fin L)
    (h : FeedbackHistory P.initialOutcomes P.outcomes j)
    (X : Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ) :
    Matrix (Fin (P.aliceDim (j + 1)) × (Fin (P.bobDim j) × B))
      (Fin (P.aliceDim (j + 1)) × (Fin (P.bobDim j) × B)) ℂ :=
  fun u v => N (fun a b => P.prepare j m h X ((u.1, a), u.2.1)
    ((v.1, b), v.2.1)) u.2.2 v.2.2

/-- PDF p.7, (3.13): one actual CP branch of Bob's classical feedback instrument. -/
def FeedbackCode.branchUpdate {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) (j : ℕ) (m : Fin L)
    (h : FeedbackHistory P.initialOutcomes P.outcomes j) (x : Fin (P.outcomes j))
    (X : Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ) :
    Matrix (Fin (P.aliceDim (j + 1)) × Fin (P.bobDim (j + 1)))
      (Fin (P.aliceDim (j + 1)) × Fin (P.bobDim (j + 1))) ℂ :=
  tensorAction id (krausApply (P.bobKraus j h x)) (P.transmit N j m h X)

/-- PDF pp.6-7, (3.7)-(3.14): unnormalized state computed along the complete
classical transcript. Zero-probability transcripts stay zero, without division.
The only correlation initially shared is Bob's classical X0, not entanglement. -/
def FeedbackCode.branchState {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) (m : Fin L) :
    (j : ℕ) → FeedbackHistory P.initialOutcomes P.outcomes j →
      Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
        (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ
  | 0, h => (P.initialProb h.1 : ℂ) •
      Matrix.kronecker (P.aliceInitial m) (P.bobInitial h.1)
  | j + 1, h => P.branchUpdate N j m (historyTruncate h)
      (h.2 ⟨j, Nat.lt_succ_self j⟩) (P.branchState N m j (historyTruncate h))

/-- PDF pp.7,11: Bob's actual final state, including all classical records.
Alice alone is traced out. Different transcripts have no coherent cross terms. -/
def FeedbackCode.receiver {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) (m : Fin L) :
    Matrix (FeedbackHistory P.initialOutcomes P.outcomes n × Fin (P.bobDim n))
      (FeedbackHistory P.initialOutcomes P.outcomes n × Fin (P.bobDim n)) ℂ :=
  fun u v => if u.1 = v.1 then
    ∑ a, P.branchState N m n u.1 (a, u.2) (a, v.2) else 0

/-- PDF p.11, (4.31): average uniform-message decoding success of this executed code. -/
def FeedbackCode.success {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) : ℝ :=
  (L : ℝ)⁻¹ * ∑ m, effectProb (P.decoder m) (P.receiver N m)

/-- PDF pp.11,16: average decoding error, not private or entanglement fidelity. -/
def FeedbackCode.error {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) : ℝ :=
  1 - P.success N

/-- PDF p.14: available uniform-message rate, in bits per individual forward use.
Distinct from Gap48.P33.messageRate: its first argument is an integer bit count,
whereas L here is an arbitrary message cardinality and log2(L) need not be integral. -/
def uniformMessageRate (n L : ℕ) : ℝ := Real.logb 2 (L : ℝ) / (n : ℝ)

/-- PDF p.7, (3.12): the fully separable positive cone on Alice memory,
current input, and Bob memory, in that order. For a normalized operator this is
exactly a convex mixture of three normalized product states. For an unnormalized
branch the coefficient sum is its trace; the zero branch is allowed. -/
def FullySeparablePositive {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (X : Matrix ((U × V) × W) ((U × V) × W) ℂ) : Prop :=
  ∃ q : ℕ, ∃ weight : Fin q → ℝ,
    ∃ a : Fin q → Matrix U U ℂ, ∃ b : Fin q → Matrix V V ℂ,
    ∃ c : Fin q → Matrix W W ℂ,
      (∀ t, 0 ≤ weight t) ∧
      (∀ t, IsDensityMatrix (a t) ∧ IsDensityMatrix (b t) ∧ IsDensityMatrix (c t)) ∧
      X = ∑ t, (weight t : ℂ) • Matrix.kronecker (Matrix.kronecker (a t) (b t)) (c t)

/-- PDF pp.6-7,12-13: in the arbitrary-channel alternative, the ACTUAL encoded
state is fully separable in every message/transcript branch, before every use.
The record is retained in the branch index; a separable averaged marginal is
insufficient. This restriction is never imposed on the EB-channel alternative. -/
def FeedbackCode.SeparableInputs {A B : Type} [Fintype A] [Fintype B]
    {n L : ℕ} (P : FeedbackCode A B n L) (N : Superop A B) : Prop :=
  ∀ j < n, ∀ m h,
    FullySeparablePositive (P.prepare j m h (P.branchState N m j h))

/-- PDF pp.2,18: a vanishing-error code sequence with eventual rate at least R.
The index k denotes blocklength k+1. The Bool selects the single-use separable-input
restriction, not separability only at boundaries of larger entangled blocks. -/
def FeedbackAchievable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : Superop A B) (separable : Bool) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ messages : ℕ → ℕ,
    ∃ codes : (k : ℕ) → FeedbackCode A B (k + 1) (messages k),
      (∀ k, (codes k).Valid ∧ (separable = true → (codes k).SeparableInputs N)) ∧
      Tendsto (fun k => (codes k).error N) atTop (nhds 0) ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop,
        R - delta ≤ uniformMessageRate (k + 1) (messages k)

/-- PDF pp.2,18: operational capacity as an extended nonnegative supremum.
The definition uses executed codes and vanishing error, independently of entropy.
Distinct from Dependency50.P09.feedbackCapacity: that interface has no per-use
separable-input selector and uses a worst-message-distribution error criterion.
The Bool here selects precisely the single-use input restriction of this paper. -/
def singleUseFeedbackCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : Superop A B) (separable : Bool) : ℝ≥0∞ :=
  sSup {r | ∃ R : ℝ, FeedbackAchievable N separable R ∧ r = ENNReal.ofReal R}

-- Sanity checks of new definitions, rather than proofs of source results.
example {x0 : ℕ} {o : ℕ → ℕ} {j : ℕ}
    (h : FeedbackHistory x0 o (j + 1)) : (historyTruncate h).1 = h.1 := rfl

example {A B : Type} [Fintype A] [Fintype B] {n L : ℕ}
    (P : FeedbackCode A B n L) (N : Superop A B) (m : Fin L)
    (h : FeedbackHistory P.initialOutcomes P.outcomes 0) :
    P.branchState N m 0 h = (P.initialProb h.1 : ℂ) •
      Matrix.kronecker (P.aliceInitial m) (P.bobInitial h.1) := rfl

example {A B : Type} [Fintype A] [Fintype B] {n L : ℕ}
    (P : FeedbackCode A B n L) (N : Superop A B) (m : Fin L)
    (u v : FeedbackHistory P.initialOutcomes P.outcomes n × Fin (P.bobDim n))
    (h : u.1 ≠ v.1) : P.receiver N m u v = 0 := by
  simp [FeedbackCode.receiver, h]

example {A B : Type} [Fintype A] [Fintype B] {n L : ℕ}
    (P : FeedbackCode A B n L) (N : Superop A B) :
    P.error N = 1 - P.success N := rfl

example (n : ℕ) : uniformMessageRate n 1 = 0 := by simp [uniformMessageRate, Real.logb]

example {U V W : Type} [Fintype U] [Fintype V] [Fintype W] :
    FullySeparablePositive (0 : Matrix ((U × V) × W) ((U × V) × W) ℂ) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro t; exact Fin.elim0 t
  · intro t; exact Fin.elim0 t
  · simp

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    {L : ℕ} (P : FeedbackCode A B 0 L) : ¬ P.Valid := by
  intro h
  exact (Nat.lt_irrefl 0) h.1

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

end QAlgorithms.Papers.Independent.Bridge50.P39


