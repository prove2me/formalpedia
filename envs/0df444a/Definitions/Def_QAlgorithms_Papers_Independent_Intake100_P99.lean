-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P99
-- name    : QAlgorithms_Papers_Independent_Intake100_P99
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T16:11:06.250763+00:00
-- url     : https://prove2.me/theorems/21781654-2271-4369-b3e7-812ad0549f41
-- title:
--   Definitions for Security of quantum key distribution with imperfect devices
-- statement:
--   The objects the formalized statements of *Security of quantum key distribution with imperfect devices* (arXiv:quant-ph/0212066) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ExponentiallySmall`: PDF pp.5,9,11: a failure probability is exponentially small in the family index. For the standalone coin results that index is the number of coins, n. Constants may depend on the state family and the fixed positive accuracy slack.
--   - `entropyGap`: PDF p.11, (20): the nonnegative entropy-gap branch. On [0,1/2] the set is nonempty, compact and a singleton, by continuity and strict monotonicity of binary entropy on [0,1/2]. Outside that source domain the explicit default is zero and no result below uses that default.
--   - `densityEvent`: PDF pp.10--11: probability of an event in a computational-basis measurement of a density matrix. Every use in the theorems carries trace-one positivity.
--   - `coinXFailure`: PDF pp.9--11: probability of the complement of the strict event NX < n delta. Hadamard conjugation converts X measurement into the fixed computational basis.
--   - `coinZFailure`: PDF p.11, (19): probability of the complement of |n/2 - NZ| < n(f(delta)+epsilon), in the Z measurement of the same state.
--   - `PairBits`: PDF pp.9--11: Alice's n qubits first, Bob's n qubits second.
--   - `PairCoinBits`: PDF pp.9--11: pair registers followed by their n virtual basis coins.
--   - `bellChange`: PDF p.10, (10)--(11): columns are product Bell states labelled by their bit-error string b and phase-error string p. The amplitude at (u,v) is zero unless v=u xor b, and otherwise is 2^(-n/2) (-1)^(u dot p).
--   - `controlledBilateralHadamard`: PDF p.9, (9): the actual final bilateral Hadamards controlled by the matching coins. These act AFTER the state whose X-coin disturbance is bounded.
--   - `phaseBitGapFailure`: PDF pp.10--11, (13),(24): full Bell-measurement tail after the final coin-controlled bilateral Hadamards. The counts are joint random variables, not expectations. The coins are also measured in Z and their result discarded.
--   - `retainedMinusCount`: PDF p.12, (32): number of X-minus coins whose corresponding signals survive an actual removal mask. A true mask bit denotes a lost signal.
--   - `retainedMinusFraction`: PDF p.12, (32): the disturbed fraction of the retained coins, computed from the same measurement outcome and mask. The denominator is positive on supported masks for positive n and loss < 1; its n=0 default is never used asymptotically.
--   - `LossBudget`: PDF p.12, (32): the removal mask deletes at most the specified fraction of signals. The first register contains all original virtual coins, the second the classical loss flags. Zero marginal weight excludes every excessive mask; the joint state may otherwise correlate the mask with the coins arbitrarily.
--   - `retainedLossFailure`: PDF p.12, (32): tail of the surviving disturbed fraction, measured jointly with the loss flags. The event uses delta/(1-loss), not a free new disturbance parameter. No conditioning on a rare block-acceptance event is introduced.
-- source:
--   Security of quantum key distribution with imperfect devices, arXiv:quant-ph/0212066v3, https://arxiv.org/abs/quant-ph/0212066v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

/-!
Gottesman--Lo--Lutkenhaus--Preskill, arXiv:quant-ph/0212066v3.
PDF pages are used throughout. Only standalone results with complete experiment
semantics are stated here. Operational extraction results are individually deferred
in HARD.md and GAPS.json; no numerical rate certificate replaces their conclusions.
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P99

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P69 (diamond)
open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation receiver)

/-- PDF pp.5,9,11: a failure probability is exponentially small in the family
index. For the standalone coin results that index is the number of coins, n.
Constants may depend on the state family and the fixed positive accuracy slack. -/
def ExponentiallySmall (p : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    p n ≤ Real.exp (-C * (n : ℝ))

/-- PDF p.11, (20): the nonnegative entropy-gap branch. On [0,1/2] the
set is nonempty, compact and a singleton, by continuity and strict monotonicity
of binary entropy on [0,1/2]. Outside that source domain the explicit default
is zero and no result below uses that default. -/
def entropyGap (delta : ℝ) : ℝ :=
  if 0 ≤ delta ∧ delta ≤ 1 / 2 then
    sInf {f : ℝ | 0 ≤ f ∧ f ≤ 1 / 2 ∧
      binEntropy2 (1 / 2 - f) + binEntropy2 delta = 1}
  else 0

/-- PDF pp.10--11: probability of an event in a computational-basis measurement
of a density matrix. Every use in the theorems carries trace-one positivity. -/
def densityEvent {A : Type*} [Fintype A] (rho : Matrix A A ℂ) (P : A → Prop) : ℝ :=
  ∑ x, if P x then densityProb rho x else 0

/-- PDF pp.9--11: probability of the complement of the strict event NX < n delta.
Hadamard conjugation converts X measurement into the fixed computational basis. -/
def coinXFailure {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ) (delta : ℝ) : ℝ :=
  densityEvent (hadamardN n * rho * (hadamardN n).conjTranspose)
    (fun x => (n : ℝ) * delta ≤ (hammingWeight x : ℝ))

/-- PDF p.11, (19): probability of the complement of
|n/2 - NZ| < n(f(delta)+epsilon), in the Z measurement of the same state. -/
def coinZFailure {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (delta epsilon : ℝ) : ℝ :=
  densityEvent rho (fun z => (n : ℝ) * (entropyGap delta + epsilon) ≤
    |(n : ℝ) / 2 - (hammingWeight z : ℝ)|)

/-- PDF pp.9--11: Alice's n qubits first, Bob's n qubits second. -/
abbrev PairBits (n : ℕ) := Qubits n × Qubits n

/-- PDF pp.9--11: pair registers followed by their n virtual basis coins. -/
abbrev PairCoinBits (n : ℕ) := PairBits n × Qubits n

/-- PDF p.10, (10)--(11): columns are product Bell states labelled by their
bit-error string b and phase-error string p. The amplitude at (u,v) is zero
unless v=u xor b, and otherwise is 2^(-n/2) (-1)^(u dot p). -/
def bellChange (n : ℕ) : Matrix (PairBits n) (PairBits n) ℂ :=
  fun uv bp => ∏ i : Fin n,
    if uv.2 i = Bool.xor (uv.1 i) (bp.1 i) then
      if (uv.1 i && bp.2 i) then -((Real.sqrt 2)⁻¹ : ℂ)
      else ((Real.sqrt 2)⁻¹ : ℂ)
    else 0

/-- PDF p.9, (9): the actual final bilateral Hadamards controlled by the
matching coins. These act AFTER the state whose X-coin disturbance is bounded. -/
def controlledBilateralHadamard (n : ℕ) :
    Matrix (PairCoinBits n) (PairCoinBits n) ℂ :=
  fun x y => if x.2 = y.2 then
    ∏ i : Fin n,
      (if x.2 i then hadamard (x.1.1 i) (y.1.1 i)
        else if x.1.1 i = y.1.1 i then 1 else 0) *
      (if x.2 i then hadamard (x.1.2 i) (y.1.2 i)
        else if x.1.2 i = y.1.2 i then 1 else 0)
    else 0

/-- PDF pp.10--11, (13),(24): full Bell-measurement tail after the final
coin-controlled bilateral Hadamards. The counts are joint random variables,
not expectations. The coins are also measured in Z and their result discarded. -/
def phaseBitGapFailure {n : ℕ}
    (rho : Matrix (PairCoinBits n) (PairCoinBits n) ℂ) (delta epsilon : ℝ) : ℝ :=
  let B := Matrix.kronecker (bellChange n) (1 : Matrix (Qubits n) (Qubits n) ℂ)
  let H := controlledBilateralHadamard n
  densityEvent (B.conjTranspose * H * rho * H.conjTranspose * B)
    (fun z => 2 * (entropyGap delta + epsilon) ≤
      |(hammingWeight z.1.2 : ℝ) / (n : ℝ) -
        (hammingWeight z.1.1 : ℝ) / (n : ℝ)|)

/-- PDF p.12, (32): number of X-minus coins whose corresponding signals survive
an actual removal mask. A true mask bit denotes a lost signal. -/
def retainedMinusCount {n : ℕ} (mask x : Qubits n) : ℕ :=
  (Finset.univ.filter fun i => mask i = false ∧ x i = true).card

/-- PDF p.12, (32): the disturbed fraction of the retained coins, computed from
the same measurement outcome and mask. The denominator is positive on supported
masks for positive n and loss < 1; its n=0 default is never used asymptotically. -/
def retainedMinusFraction {n : ℕ} (mask x : Qubits n) : ℝ :=
  (retainedMinusCount mask x : ℝ) / ((n : ℝ) - (hammingWeight mask : ℝ))

/-- PDF p.12, (32): the removal mask deletes at most the specified fraction of
signals. The first register contains all original virtual coins, the second the
classical loss flags. Zero marginal weight excludes every excessive mask; the
joint state may otherwise correlate the mask with the coins arbitrarily. -/
def LossBudget {n : ℕ}
    (rho : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) (loss : ℝ) : Prop :=
  ∀ mask : Qubits n, loss * (n : ℝ) < (hammingWeight mask : ℝ) →
    densityProb (traceLeft rho) mask = 0

/-- PDF p.12, (32): tail of the surviving disturbed fraction, measured jointly
with the loss flags. The event uses delta/(1-loss), not a free new disturbance
parameter. No conditioning on a rare block-acceptance event is introduced. -/
def retainedLossFailure {n : ℕ}
    (rho : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (delta loss : ℝ) : ℝ :=
  let B := Matrix.kronecker (hadamardN n) (1 : Matrix (Qubits n) (Qubits n) ℂ)
  densityEvent (B * rho * B.conjTranspose)
    (fun z => delta / (1 - loss) ≤ retainedMinusFraction z.2 z.1)

/-! Small sanity checks; these are definition checks, not proofs of the targets. -/

example : ExponentiallySmall (fun _ => 0) := by
  exact ⟨1, by norm_num, 0, fun n _ => (Real.exp_pos _).le⟩

example : binEntropy2 0 = 0 := by
  simp [binEntropy2]

example (delta : ℝ) (h : ¬ (0 ≤ delta ∧ delta ≤ 1 / 2)) : entropyGap delta = 0 := by
  unfold entropyGap
  rw [if_neg h]

example : entropyGap 0 = 0 := by
  have hhalf : binEntropy2 (1 / 2) = 1 := by
    rw [binEntropy2, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hz : (0 : ℝ) ∈ {f : ℝ | 0 ≤ f ∧ f ≤ 1 / 2 ∧
      binEntropy2 (1 / 2 - f) + binEntropy2 0 = 1} := by
    refine ⟨le_rfl, by norm_num, ?_⟩
    simpa only [sub_zero, show binEntropy2 0 = 0 by simp [binEntropy2], add_zero]
      using hhalf
  unfold entropyGap
  rw [if_pos (by norm_num : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 / 2)]
  apply le_antisymm
  · exact csInf_le ⟨0, fun f hf => hf.1⟩ hz
  · exact le_csInf ⟨0, hz⟩ (fun f hf => hf.1)

example {A : Type*} [Fintype A] (rho : Matrix A A ℂ) :
    densityEvent rho (fun _ => False) = 0 := by
  simp [densityEvent]

example : bellChange 0 = (1 : Matrix (PairBits 0) (PairBits 0) ℂ) := by
  ext x y
  have h : x = y := Subsingleton.elim _ _
  subst y
  simp [bellChange]

example : bellChange 1 (fun _ => false, fun _ => false)
    (fun _ => false, fun _ => true) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [bellChange]

example {n : ℕ} (x : Qubits n) :
    retainedMinusCount (fun _ => true) x = 0 := by
  simp [retainedMinusCount]

example : controlledBilateralHadamard 0 =
    (1 : Matrix (PairCoinBits 0) (PairCoinBits 0) ℂ) := by
  ext x y
  have h : x = y := Subsingleton.elim _ _
  subst y
  simp [controlledBilateralHadamard]

example : bellChange 1 (fun _ => true, fun _ => true)
    (fun _ => false, fun _ => true) = -((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [bellChange]

-- The frozen predicate records isometry; its frozen receiver records the channel.
example : IsDilation (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  simp [IsDilation]

example (X : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    receiver (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) X = traceRight X := by
  simp [receiver]

end QAlgorithms.Papers.Independent.Intake100.P99


