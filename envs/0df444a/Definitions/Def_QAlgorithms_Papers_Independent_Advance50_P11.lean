-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11
-- name    : QAlgorithms_Papers_Independent_Advance50_P11
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:24:34.143763+00:00
-- url     : https://prove2.me/theorems/565f323b-2848-47df-bd5e-c1e8fa66744e
-- title:
--   Definitions for Single-shot Quantum State Merging
-- statement:
--   The objects the formalized statements of *Single-shot Quantum State Merging* (arXiv:0912.4495) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `optimizedMin`: PDF p.10, (3.5): optimize the fixed-reference min entropy over normalized densities.
--   - `optimizedMax`: PDF p.10, (3.6): historical support-rank max entropy, with normalized reference optimization.
--   - `normalizedBall`: PDF p.14, Definition 3.12: the closed ball contains only normalized density matrices. For eps >= 0 it contains rho whenever rho is a density; radii >= 1 remain meaningful.
--   - `normalizedSmoothFixedMin`: PDF p.14, (3.32): supremum smoothing with sigma fixed over NORMALIZED states at HALF trace-norm distance. The frozen Gap20.P03.smoothFixedMin uses a subnormalized full-radius ball, so it is a different source concept.
--   - `smoothFixedMax`: PDF p.14, (3.33): infimum smoothing of the historical rank-max entropy.
--   - `normalizedSmoothMin`: PDF p.14, (3.34): outer reference supremum, after normalized min smoothing. This is quantum density smoothing, distinct from frozen Gap20.P03.smoothMin, which is worst-case classical entropy under event deletion.
--   - `normalizedSmoothRankMax`: PDF p.14, (3.35): outer supremum after the inner normalized rank-max INFIMUM. The frozen Information100.P71.smoothMax is a channel max-relative divergence; it is not this historical conditional rank entropy.
--   - `weightedOperator`: PDF pp.10,15: weighting on the reference tensor factor. Negative powers are inverse-on-support and vanish on the kernel, as required by Remark 3.6.
--   - `collisionEntropy`: PDF p.15, (3.40): raw collision entropy with the stated generalized inverse. Zero collision mass gives +infinity. Comparisons and decoupling require support inclusion.
--   - `referenceLast`: PDF pp.11,14: tensor-factor permutation, moving the first factor to the end. This is basis transport, not a partial trace.
--   - `tensorRegroup`: PDF p.11, (3.9)--(3.10): regroup AA':BB' after taking the tensor product.
--   - `inputKet`: PDF p.16, Definition 4.1: single-copy input with the whole independent rank-K Bell resource. Register order is R:((Alice A,A0),(Bob B,B0)).
--   - `targetKet`: PDF p.16, (4.1): complete pure target, including the rank-L Bell resource. Bob's A is the fixed copy Bprime; the reference is unchanged.
--   - `Merges`: PDF p.16, Definition 4.1: actual finite adaptive LOCC and full target error. K,L are positive natural Schmidt ranks. No entropy or decoupling conclusion is an input.
--   - `ancillaryInput`: PDF p.25, Remark 4.11: independent normalized Alice ancilla at the input. It is not added to, or identified with, the inaccessible source reference R.
--   - `retainedKrausBranch`: PDF pp.6,23: a fine-grained local branch retaining its quantum output and R. Reuse the frozen single-Kraus conjugation, with identity on the actual reference. Dependency50.P07.measurementBranch instead traces Alice out and cannot be used here.
--   - `flaggedOutput`: PDF p.23, (4.31): actual outcome-flagged state, grouped as A:(R X). Each outcome retains its single measurement operator, including zero-weight branches.
--   - `outcomeState`: PDF p.23: the classical flag marginal is computed from actual branch traces.
--   - `aliceResourceMarginal`: PDF pp.17--18: Alice's rank-K input resource is maximally mixed in the AR marginal.
--   - `decouplingSum`: PDF pp.17--18, (4.5): the weighted decoupling sum, without division by a zero outcome probability. For each positive branch this equals p_j times its normalized trace-norm error.
--   - `compressedState`: PDF p.19: the actual unnormalized compressed state for a Haar unitary U.
--   - `rankOnePinching`: PDF pp.25--26: the frozen rank-one pinching, extended to the first factor. Dependency50.P35.pinch sums the column-projector sandwiches. The frozen mapFirst retains every reference block, including off-diagonal blocks. Thus no local basis projector or duplicate pinching definition is needed.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, https://arxiv.org/abs/0912.4495v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Mario Berta, Single-shot Quantum State Merging, arXiv:0912.4495v1.
All page numbers are PDF pages and logarithms are binary. The historical
max entropy is the support-rank entropy. Smoothing uses normalized states
and HALF trace-norm distance; protocol errors use the FULL trace norm.
Only definitions from the pinned accepted library are reused. New definitions
are local to this paper. Source defects and intentionally omitted nodes are
recorded in HARD.md; no operational converse with positive error is asserted.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)
open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)
open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, (3.5): optimize the fixed-reference min entropy over normalized densities. -/
def optimizedMin {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨆ sigma : {s : Matrix B B ℂ // IsDensityMatrix s}, conditionalMin rho sigma.1

/-- PDF p.10, (3.6): historical support-rank max entropy, with normalized reference optimization. -/
def optimizedMax {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨆ sigma : {s : Matrix B B ℂ // IsDensityMatrix s}, conditionalMax rho sigma.1

/-- PDF p.14, Definition 3.12: the closed ball contains only normalized density matrices.
For eps >= 0 it contains rho whenever rho is a density; radii >= 1 remain meaningful. -/
def normalizedBall {I : Type} [Fintype I] [DecidableEq I]
    (eps : ℝ) (rho : Matrix I I ℂ) : Set (Matrix I I ℂ) :=
  {tau | IsDensityMatrix tau ∧ (1 / 2 : ℝ) * traceNorm (tau - rho) ≤ eps}

/-- PDF p.14, (3.32): supremum smoothing with sigma fixed over NORMALIZED states
at HALF trace-norm distance. The frozen Gap20.P03.smoothFixedMin uses a
subnormalized full-radius ball, so it is a different source concept. -/
def normalizedSmoothFixedMin {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (eps : ℝ) (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) : EReal :=
  ⨆ tau : normalizedBall eps rho, conditionalMin tau.1 sigma

/-- PDF p.14, (3.33): infimum smoothing of the historical rank-max entropy. -/
def smoothFixedMax {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (eps : ℝ) (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) : EReal :=
  ⨅ tau : normalizedBall eps rho, conditionalMax tau.1 sigma

/-- PDF p.14, (3.34): outer reference supremum, after normalized min smoothing.
This is quantum density smoothing, distinct from frozen Gap20.P03.smoothMin,
which is worst-case classical entropy under event deletion. -/
def normalizedSmoothMin {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (eps : ℝ) (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨆ sigma : {s : Matrix B B ℂ // IsDensityMatrix s}, normalizedSmoothFixedMin eps rho sigma.1

/-- PDF p.14, (3.35): outer supremum after the inner normalized rank-max INFIMUM.
The frozen Information100.P71.smoothMax is a channel max-relative divergence;
it is not this historical conditional rank entropy. -/
def normalizedSmoothRankMax {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (eps : ℝ) (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨆ sigma : {s : Matrix B B ℂ // IsDensityMatrix s}, smoothFixedMax eps rho sigma.1

/-- PDF pp.10,15: weighting on the reference tensor factor. Negative powers are
inverse-on-support and vanish on the kernel, as required by Remark 3.6. -/
def weightedOperator {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (t : ℝ) :=
  Matrix.kronecker (1 : Matrix A A ℂ) (supportPower sigma t) * rho *
    Matrix.kronecker (1 : Matrix A A ℂ) (supportPower sigma t)

/-- PDF p.15, (3.40): raw collision entropy with the stated generalized inverse.
Zero collision mass gives +infinity. Comparisons and decoupling require support inclusion. -/
def collisionEntropy {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) : EReal :=
  -elog (tr (weightedOperator rho sigma (-1 / 4) ^ 2))

/-- PDF pp.11,14: tensor-factor permutation, moving the first factor to the end.
This is basis transport, not a partial trace. -/
def referenceLast {A R : Type} (rho : Matrix (R × A) (R × A) ℂ) :
    Matrix (A × R) (A × R) ℂ := fun p q => rho (p.2, p.1) (q.2, q.1)

/-- PDF p.11, (3.9)--(3.10): regroup AA':BB' after taking the tensor product. -/
def tensorRegroup {A B C D : Type}
    (rho : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × D) (C × D) ℂ) :
    Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ :=
  fun p q => rho (p.1.1, p.2.1) (q.1.1, q.2.1) *
    tau (p.1.2, p.2.2) (q.1.2, q.2.2)

/-- PDF p.16, Definition 4.1: single-copy input with the whole independent rank-K Bell resource.
Register order is R:((Alice A,A0),(Bob B,B0)). -/
def inputKet {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B))) (K : ℕ) :
    EuclideanSpace ℂ (R × ((A × Fin K) × (B × Fin K))) :=
  WithLp.toLp 2 fun p => psi (p.1, (p.2.1.1, p.2.2.1)) *
    bell (Fin K) (p.2.1.2, p.2.2.2)

/-- PDF p.16, (4.1): complete pure target, including the rank-L Bell resource.
Bob's A is the fixed copy Bprime; the reference is unchanged. -/
def targetKet {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B))) (L : ℕ) :
    EuclideanSpace ℂ (R × (Fin L × ((A × B) × Fin L))) :=
  WithLp.toLp 2 fun p => psi (p.1, p.2.2.1) * bell (Fin L) (p.2.1, p.2.2.2)

/-- PDF p.16, Definition 4.1: actual finite adaptive LOCC and full target error.
K,L are positive natural Schmidt ranks. No entropy or decoupling conclusion is an input. -/
def Merges {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (K L : ℕ)
    (M : Superop ((A × Fin K) × (B × Fin K)) (Fin L × ((A × B) × Fin L)))
    (eps : ℝ) : Prop :=
  0 < K ∧ 0 < L ∧ IsLOCC M ∧
    traceNorm (idTensorSuperop M (pureDensity (inputKet psi K)) -
      pureDensity (targetKet psi L)) ≤ eps

/-- PDF p.25, Remark 4.11: independent normalized Alice ancilla at the input.
It is not added to, or identified with, the inaccessible source reference R. -/
def ancillaryInput {A B R C : Type}
    (psi : EuclideanSpace ℂ (R × (A × B))) (eta : Matrix C C ℂ) (K : ℕ) :
    Matrix (R × (((A × Fin K) × C) × (B × Fin K)))
      (R × (((A × Fin K) × C) × (B × Fin K))) ℂ :=
  fun p q => pureDensity (inputKet psi K)
    (p.1, (p.2.1.1, p.2.2)) (q.1, (q.2.1.1, q.2.2)) * eta p.2.1.2 q.2.1.2

/-- PDF pp.6,23: a fine-grained local branch retaining its quantum output and R.
Reuse the frozen single-Kraus conjugation, with identity on the actual reference.
Dependency50.P07.measurementBranch instead traces Alice out and cannot be used here. -/
def retainedKrausBranch {A C R : Type} [Fintype A] [Fintype R] [DecidableEq R]
    (M : Matrix C A ℂ) (rho : Matrix (A × R) (A × R) ℂ) :
    Matrix (C × R) (C × R) ℂ :=
  conjSuperop (Matrix.kronecker M (1 : Matrix R R ℂ)) rho

/-- PDF p.23, (4.31): actual outcome-flagged state, grouped as A:(R X).
Each outcome retains its single measurement operator, including zero-weight branches. -/
def flaggedOutput {A R X : Type} [Fintype A] [Fintype R] [DecidableEq R] [DecidableEq X]
    (M : X → Matrix A A ℂ) (rho : Matrix (A × R) (A × R) ℂ) :
    Matrix (A × (R × X)) (A × (R × X)) ℂ :=
  fun p q => if p.2.2 = q.2.2 then
    retainedKrausBranch (M p.2.2) rho (p.1, p.2.1) (q.1, q.2.1) else 0

/-- PDF p.23: the classical flag marginal is computed from actual branch traces. -/
def outcomeState {A R X : Type} [Fintype A] [Fintype R] [DecidableEq R] [DecidableEq X]
    (M : X → Matrix A A ℂ) (rho : Matrix (A × R) (A × R) ℂ) : Matrix X X ℂ :=
  Matrix.diagonal fun x => (retainedKrausBranch (M x) rho).trace

/-- PDF pp.17--18: Alice's rank-K input resource is maximally mixed in the AR marginal. -/
def aliceResourceMarginal {A R : Type} [Fintype A] [Fintype R]
    (rho : Matrix (A × R) (A × R) ℂ) (K : ℕ) :
    Matrix ((A × Fin K) × R) ((A × Fin K) × R) ℂ :=
  fun p q => rho (p.1.1, p.2) (q.1.1, q.2) * mixed (Fin K) p.1.2 q.1.2

/-- PDF pp.17--18, (4.5): the weighted decoupling sum, without division by a zero outcome probability.
For each positive branch this equals p_j times its normalized trace-norm error. -/
def decouplingSum {A B R X : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype X]
    (psi : EuclideanSpace ℂ (R × (A × B))) (K L : ℕ)
    (M : X → Matrix (Fin L) (A × Fin K) ℂ) : ℝ :=
  let rho := aliceResourceMarginal (marginalAR (pureDensity psi)) K
  let target := Matrix.kronecker (mixed (Fin L)) (traceRight (pureDensity psi))
  ∑ x, traceNorm (retainedKrausBranch (M x) rho -
    (retainedKrausBranch (M x) rho).trace • target)

/-- PDF p.19: the actual unnormalized compressed state for a Haar unitary U. -/
def compressedState {d L : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (rho : Matrix (Fin d × R) (Fin d × R) ℂ) (P : Matrix (Fin L) (Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin L × R) (Fin L × R) ℂ :=
  retainedKrausBranch (P * (U : Matrix (Fin d) (Fin d) ℂ)) rho

/-- PDF pp.25--26: the frozen rank-one pinching, extended to the first factor.
Dependency50.P35.pinch sums the column-projector sandwiches. The frozen mapFirst
retains every reference block, including off-diagonal blocks. Thus no local basis
projector or duplicate pinching definition is needed. -/
def rankOnePinching {A R : Type} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R]
    (U : Matrix.unitaryGroup A ℂ) (rho : Matrix (A × R) (A × R) ℂ) :=
  QAlgorithms.Papers.Independent.Information100.P67.mapFirst
    (QAlgorithms.Papers.Independent.Dependency50.P35.pinch (U : Matrix A A ℂ)) rho

/-! Sanity examples pinning domain, zero outcomes, factor order and the full target. -/

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps : 0 ≤ eps) :
    rho ∈ normalizedBall eps rho := by
  simpa [normalizedBall, traceNorm, cfc_zero] using And.intro hrho heps

example {A R : Type} [Fintype A] [Fintype R] [DecidableEq R]
    (rho : Matrix (A × R) (A × R) ℂ) : retainedKrausBranch (0 : Matrix A A ℂ) rho = 0 := by
  simp [retainedKrausBranch, conjSuperop]

example {A R : Type} (rho : Matrix (R × A) (R × A) ℂ) :
    referenceLast (referenceLast rho) = rho := rfl

example {A B : Type} (psi : EuclideanSpace ℂ (Unit × (A × B))) (a : A) (b : B) :
    targetKet psi 1 ((), (0, ((a, b), 0))) = psi ((), (a, b)) := by
  simp [targetKet, bell]

example {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (K L : ℕ)
    (M : Superop ((A × Fin K) × (B × Fin K)) (Fin L × ((A × B) × Fin L)))
    (h : Merges psi K L M 0) : IsLOCC M := h.2.2.1

end QAlgorithms.Papers.Independent.Advance50.P11


