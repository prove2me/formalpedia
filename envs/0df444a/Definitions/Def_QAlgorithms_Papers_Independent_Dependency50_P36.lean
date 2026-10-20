-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
-- name    : QAlgorithms_Papers_Independent_Dependency50_P36
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:32:09.257576+00:00
-- url     : https://prove2.me/theorems/a5d99431-a291-4f14-b1da-da63bc718243
-- title:
--   Definitions for Non-asymptotic entanglement distillation
-- statement:
--   The objects the formalized statements of *Non-asymptotic entanglement distillation* (arXiv:1706.06221) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pptPrime`: arXiv:1706.06221v3, PDF p.6, Eq.(33): finite PPT-prime, without a trace-one constraint.
--   - `target`: arXiv:1706.06221v3, PDF pp.3–4: rank-k maximally entangled projector. Only positive k is used in operational definitions.
--   - `canonicalMatrix`: arXiv:1706.06221v3, PDF p.2: relabel a finite product basis by canonical indices. This coordinate bijection preserves Alice and Bob separately.
--   - `isOneWay`: arXiv:1706.06221v3, PDF pp.2–3: one-way Alice-to-Bob operations. Refine Alice's instrument to single Kraus outcomes; Bob's conditional maps are channels.
--   - `isSEP`: arXiv:1706.06221v3, PDF p.3: product-Kraus SEP channels, equivalent to separable Choi matrices across input-A/output-A : input-B/output-B.
--   - `isPPT`: arXiv:1706.06221v3, PDF p.3, Eq.(14): completely PPT-preserving CPTP maps. The Bob-transpose conjugate must also be a channel, not merely preserve PPT states.
--   - `OperationClass`: arXiv:1706.06221v3, PDF pp.2–3: the four operation classes in Theorem 7.
--   - `allowed`: arXiv:1706.06221v3, PDF pp.2–3: concrete class membership. For LOCC the optimal fidelity is the supremum over finite adaptive protocols.
--   - `distillationFidelity`: arXiv:1706.06221v3, PDF p.3, Definition 1: optimal squared fidelity to Psi_k. Supremum includes limits of finite LOCC protocols. On states all overlaps lie in [0,1], and product-state preparation makes the feasible set nonempty for positive k.
--   - `oneShot`: arXiv:1706.06221v3, PDF p.4, Definition 2: integer-rank one-shot entanglement. Extended reals avoid a false finite value on an unbounded feasible rank set.
--   - `pptAchievableRate`: arXiv:1706.06221v3, PDF p.1, Eq.(1): vanishing trace-norm error at fixed rate. Ceil(2^(nr)) gives an integer target. Channels are chosen separately at each n; no existence of the double limit printed in Eq.(6) is assumed.
--   - `pptDistillable`: arXiv:1706.06221v3, PDF p.1, Eq.(1): supremum of operationally achievable PPT rates.
--   - `supportIncluded`: arXiv:1706.06221v3, PDF p.6: support inclusion as reversed kernel inclusion.
--   - `relativeEntropyFinite`: arXiv:1706.06221v3, PDF p.6: finite Umegaki expression in bits. Interpret as relative entropy only on PSD pairs with support inclusion.
--   - `relativeEntropy`: arXiv:1706.06221v3, PDF p.6, Eq.(33): extended relative entropy, infinity on support failure. Theorems impose PSD; no trace normalization is imposed on sigma.
--   - `rains`: arXiv:1706.06221v3, PDF p.6, Eq.(33): finite-dimensional Rains infimum in bits.
--   - `pairInformationVariance`: arXiv:1706.06221v3, PDF p.7: information variance in bits squared, for PSD support-included pairs. Zero eigenvalues of rho contribute zero under its trace. The accepted P63.informationVariance is a ONE-state spectral variance; this TWO-operator relative-information variance is a different source concept.
--   - `stateCoherentInformationBits`: arXiv:1706.06221v3, PDF pp.7–9: state coherent information in bits. Reuse the accepted order-one state coherent information in nats and divide by ln(2). This is S(B)-S(AB)=+D(rho||I_A tensor rho_B), as printed on p.7.
--   - `coherentVariance`: arXiv:1706.06221v3, PDF p.7: coherent information variance.
--   - `accepts`: arXiv:1706.06221v3, PDF pp.3,6: feasible hypothesis-testing effects.
--   - `testingEntropy`: arXiv:1706.06221v3, PDF p.3: Hermitian-extended testing entropy; beta<=0 gives +infinity, not Lean's default log zero.
--   - `testingRains`: arXiv:1706.06221v3, PDF p.6, Eq.(25), and p.17, Eq.(65): Hermitian unit-ball optimization. With positiveOnly=true this is OPT2 instead of OPT1.
--   - `roundingGap`: arXiv:1706.06221v3, PDF p.6: constructed correction, not a freely chosen slack.
--   - `pptSDPFeasible`: arXiv:1706.06221v3, PDF pp.4–5, Eqs.(7),(24): SDP feasibility. Loewner inequalities are encoded by PSD differences.
--   - `secondOrderExpansion`: arXiv:1706.06221v3, PDF pp.7–10: eventual absolute O(log n) remainder for total entanglement. C,N may depend on all parameters fixed before this predicate.
--   - `maximallyCorrelated`: arXiv:1706.06221v3, PDF p.9, Eq.(50): finite maximally correlated embedding.
--   - `sourceBellVector`: arXiv:1706.06221v3, PDF p.9, Eq.(48): the two Bell vectors on 01 and 10. Reuse the accepted maximally entangled vector, flip Bob's bit, and apply the relative minus sign on Alice's 1 coordinate when requested.
--   - `bellMixture`: arXiv:1706.06221v3, PDF p.9, Eq.(48): two-Bell-state mixture, 0<p<1.
--   - `overlapIsotropic`: arXiv:1706.06221v3, PDF p.10, Eq.(52): isotropic state by target overlap F. The accepted isotropic state uses depolarizing weight p, with F=p+(1-p)/d^2. For d>=2 convert explicitly: p=(d^2 F-1)/(d^2-1). This retains F=0 and F=1.
--   - `isotropicCoefficient`: arXiv:1706.06221v3, PDF p.10, Eq.(54): exact isotropic LP coefficients. The Icc interval enforces m<=i,k and i+k-n<=m before any natural subtraction.
--   - `isotropicLPFeasible`: arXiv:1706.06221v3, PDF p.10, Eq.(53): linear feasibility before nonlinear reciprocal/floor/log postprocessing.
--   - `appendixState`: arXiv:1706.06221v3, PDF p.18: Appendix-A state 3/4 |phi1><phi1|+1/4 |10><10|.
--   - `crossEntropyFinite`: arXiv:1706.06221v3, PDF pp.18–19, Eq.(69): finite cross entropy in nats. The extended version below guards singular support; this expression alone does not.
--   - `crossEntropy`: arXiv:1706.06221v3, PDF pp.18–19: cross entropy, infinity on support failure.
--   - `crossEntropyOptimum`: arXiv:1706.06221v3, PDF p.18, Eq.(69): unshifted optimum in nats, not R in bits.
--   - `TangentPoint`: arXiv:1706.06221v3, PDF p.19, Eqs.(70)–(74): a feasible interior tangent point with a unitary diagonalization and positive eigenvalues. Interior is taken in the real Hermitian subspace; the PSD cone has empty interior in all complex matrices.
--   - `logDividedDifference`: arXiv:1706.06221v3, PDF p.19, Eq.(71): divided difference of natural log; equal positive eigenvalues use 1/lambda, including repeated eigenvalues.
--   - `tangentGradient`: arXiv:1706.06221v3, PDF p.19, Eq.(73): positive-sign gradient E; the derivative of cross entropy is -Tr(E Delta).
--   - `cuttingPlaneOptimum`: arXiv:1706.06221v3, PDF p.19, Eq.(74), with optional previous lower bound (75). Bottom recovers Eq.(74). Slacks are explicit and nonnegative.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, https://arxiv.org/abs/1706.06221v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

-- These declarations come from the pinned accepted-library catalogue.
open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)
open QAlgorithms.Papers.Independent.Information100.P04 (copies)
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)
open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)
open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:1706.06221v3, PDF p.6, Eq.(33): finite PPT-prime, without a trace-one constraint. -/
def pptPrime {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) : Prop :=
  X.PosSemidef ∧ traceNorm (partialTransposeB X) ≤ 1

/-- arXiv:1706.06221v3, PDF pp.3–4: rank-k maximally entangled projector.
Only positive k is used in operational definitions. -/
def target (k : ℕ) : Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (k : ℂ)⁻¹ else 0

/-- arXiv:1706.06221v3, PDF p.2: relabel a finite product basis by canonical indices.
This coordinate bijection preserves Alice and Bob separately. -/
def canonicalMatrix {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (Fin (Fintype.card A) × Fin (Fintype.card B))
      (Fin (Fintype.card A) × Fin (Fintype.card B)) ℂ :=
  fun p q => rho ((Fintype.equivFin A).symm p.1, (Fintype.equivFin B).symm p.2)
    ((Fintype.equivFin A).symm q.1, (Fintype.equivFin B).symm q.2)

/-- arXiv:1706.06221v3, PDF pp.2–3: one-way Alice-to-Bob operations.
Refine Alice's instrument to single Kraus outcomes; Bob's conditional maps are channels. -/
def isOneWay {a b c d : ℕ} (Phi : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  ∃ m l : ℕ, ∃ A : Fin m → Matrix (Fin c) (Fin a) ℂ,
    ∃ B : Fin m → Fin l → Matrix (Fin d) (Fin b) ℂ,
    IsKrausFamily A ∧ (∀ i, IsKrausFamily (B i)) ∧
    ∀ X, Phi X = ∑ i, ∑ j, conjSuperop (Matrix.kronecker (A i) (B i j)) X

/-- arXiv:1706.06221v3, PDF p.3: product-Kraus SEP channels, equivalent to
separable Choi matrices across input-A/output-A : input-B/output-B. -/
def isSEP {a b c d : ℕ} (Phi : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin c) (Fin a) ℂ,
    ∃ B : Fin m → Matrix (Fin d) (Fin b) ℂ,
    IsKrausFamily (fun i => Matrix.kronecker (A i) (B i)) ∧
    ∀ X, Phi X = krausApply (fun i => Matrix.kronecker (A i) (B i)) X

/-- arXiv:1706.06221v3, PDF p.3, Eq.(14): completely PPT-preserving CPTP maps.
The Bob-transpose conjugate must also be a channel, not merely preserve PPT states. -/
def isPPT {a b c d : ℕ} (Phi : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  IsChannel Phi ∧ IsChannel (fun X => partialTransposeB (Phi (partialTransposeB X)))

/-- arXiv:1706.06221v3, PDF pp.2–3: the four operation classes in Theorem 7. -/
inductive OperationClass where
  | oneWay | locc | sep | ppt
  deriving DecidableEq

/-- arXiv:1706.06221v3, PDF pp.2–3: concrete class membership.
For LOCC the optimal fidelity is the supremum over finite adaptive protocols. -/
def allowed (Omega : OperationClass) {a b c d : ℕ}
    (Phi : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  match Omega with
  | .oneWay => isOneWay Phi
  | .locc => FiniteLOCC Phi
  | .sep => isSEP Phi
  | .ppt => isPPT Phi

/-- arXiv:1706.06221v3, PDF p.3, Definition 1: optimal squared fidelity to Psi_k.
Supremum includes limits of finite LOCC protocols. On states all overlaps lie in [0,1],
and product-state preparation makes the feasible set nonempty for positive k. -/
def distillationFidelity {A B : Type} [Fintype A] [Fintype B]
    (Omega : OperationClass) (rho : Matrix (A × B) (A × B) ℂ) (k : ℕ) : ℝ :=
  sSup {v | ∃ Phi : Superop
    (Fin (Fintype.card A) × Fin (Fintype.card B)) (Fin k × Fin k),
    allowed Omega Phi ∧ v = (Phi (canonicalMatrix rho) * target k).trace.re}

/-- arXiv:1706.06221v3, PDF p.4, Definition 2: integer-rank one-shot entanglement.
Extended reals avoid a false finite value on an unbounded feasible rank set. -/
def oneShot {A B : Type} [Fintype A] [Fintype B]
    (Omega : OperationClass) (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : EReal :=
  sSup {e | ∃ k : ℕ, 0 < k ∧ 1 - epsilon ≤ distillationFidelity Omega rho k ∧
    e = (log2 k : EReal)}

/-- arXiv:1706.06221v3, PDF p.1, Eq.(1): vanishing trace-norm error at fixed rate.
Ceil(2^(nr)) gives an integer target. Channels are chosen separately at each n;
no existence of the double limit printed in Eq.(6) is assumed. -/
def pptAchievableRate {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ tolerance : ℝ, 0 < tolerance → ∃ N : ℕ, ∀ n ≥ N,
    let k := Nat.ceil (Real.rpow 2 ((n : ℝ) * r))
    ∃ Phi : Superop
      (Fin (Fintype.card (Fin n → A)) × Fin (Fintype.card (Fin n → B))) (Fin k × Fin k),
      isPPT Phi ∧ traceNorm (Phi (canonicalMatrix (copies rho n)) - target k) ≤ tolerance

/-- arXiv:1706.06221v3, PDF p.1, Eq.(1): supremum of operationally achievable PPT rates. -/
def pptDistillable {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {e | ∃ r : ℝ, pptAchievableRate rho r ∧ e = (r : EReal)}

/-- arXiv:1706.06221v3, PDF p.6: support inclusion as reversed kernel inclusion. -/
def supportIncluded {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- arXiv:1706.06221v3, PDF p.6: finite Umegaki expression in bits.
Interpret as relative entropy only on PSD pairs with support inclusion. -/
def relativeEntropyFinite {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) rho - rho * cfc Real.log sigma).trace.re / Real.log 2

/-- arXiv:1706.06221v3, PDF p.6, Eq.(33): extended relative entropy, infinity on
support failure. Theorems impose PSD; no trace normalization is imposed on sigma. -/
def relativeEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : EReal :=
  if supportIncluded rho sigma then (relativeEntropyFinite rho sigma : EReal) else ⊤

/-- arXiv:1706.06221v3, PDF p.6, Eq.(33): finite-dimensional Rains infimum in bits. -/
def rains {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {e | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    pptPrime sigma ∧ e = relativeEntropy rho sigma}

/-- arXiv:1706.06221v3, PDF p.7: information variance in bits squared, for PSD
support-included pairs. Zero eigenvalues of rho contribute zero under its trace.
The accepted P63.informationVariance is a ONE-state spectral variance; this
TWO-operator relative-information variance is a different source concept. -/
def pairInformationVariance {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  let L := cfc log2 rho - cfc log2 sigma
  (rho * (L * L)).trace.re - (relativeEntropyFinite rho sigma) ^ 2

/-- arXiv:1706.06221v3, PDF pp.7–9: state coherent information in bits.
Reuse the accepted order-one state coherent information in nats and divide by ln(2).
This is S(B)-S(AB)=+D(rho||I_A tensor rho_B), as printed on p.7. -/
def stateCoherentInformationBits {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P39.coherentInformation 1 rho / Real.log 2

/-- arXiv:1706.06221v3, PDF p.7: coherent information variance. -/
def coherentVariance {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  pairInformationVariance rho (Matrix.kronecker (1 : Matrix A A ℂ) (traceLeft rho))

/-- arXiv:1706.06221v3, PDF pp.3,6: feasible hypothesis-testing effects. -/
def accepts {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (epsilon : ℝ) (M : Matrix I I ℂ) : Prop :=
  IsEffect M ∧ 1 - epsilon ≤ (rho * M).trace.re

/-- arXiv:1706.06221v3, PDF p.3: Hermitian-extended testing entropy;
beta<=0 gives +infinity, not Lean's default log zero. -/
def testingEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (rho G : Matrix I I ℂ) (epsilon : ℝ) : EReal :=
  if 0 < testingBeta epsilon rho G then (-log2 (testingBeta epsilon rho G) : EReal) else ⊤

/-- arXiv:1706.06221v3, PDF p.6, Eq.(25), and p.17, Eq.(65): Hermitian
unit-ball optimization. With positiveOnly=true this is OPT2 instead of OPT1. -/
def testingRains {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) (positiveOnly : Bool := false) : EReal :=
  sInf {e | ∃ G : Matrix (A × B) (A × B) ℂ,
    G.IsHermitian ∧ traceNorm (partialTransposeB G) ≤ 1 ∧
    (positiveOnly = true → G.PosSemidef) ∧ e = testingEntropy rho G epsilon}

/-- arXiv:1706.06221v3, PDF p.6: constructed correction, not a freely chosen slack. -/
def roundingGap (L : ℝ) : ℝ := L - log2 (Nat.floor (Real.rpow 2 L))

/-- arXiv:1706.06221v3, PDF pp.4–5, Eqs.(7),(24): SDP feasibility.
Loewner inequalities are encoded by PSD differences. -/
def pptSDPFeasible {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (epsilon eta : ℝ)
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  accepts rho epsilon M ∧
    (partialTransposeB M + (eta : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)).PosSemidef ∧
    ((eta : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) - partialTransposeB M).PosSemidef

/-- arXiv:1706.06221v3, PDF pp.7–10: eventual absolute O(log n) remainder for
total entanglement. C,N may depend on all parameters fixed before this predicate. -/
def secondOrderExpansion (E : ℕ → EReal) (a v epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
    let f := (n : ℝ) * a + Real.sqrt ((n : ℝ) * v) * normalQuantile epsilon
    ((f - C * log2 n : ℝ) : EReal) ≤ E n ∧
      E n ≤ ((f + C * log2 n : ℝ) : EReal)

/-- arXiv:1706.06221v3, PDF p.9, Eq.(50): finite maximally correlated embedding. -/
def maximallyCorrelated {d : ℕ} (rhoTilde : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then rhoTilde p.1 q.1 else 0

/-- arXiv:1706.06221v3, PDF p.9, Eq.(48): the two Bell vectors on 01 and 10.
Reuse the accepted maximally entangled vector, flip Bob's bit, and apply the
relative minus sign on Alice's 1 coordinate when requested. -/
def sourceBellVector (minus : Bool) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p =>
    (if minus = true ∧ p.1 = 1 then (-1 : ℂ) else 1) *
      QAlgorithms.Papers.Independent.Information100.P08.bellVector 2
        (p.1, if p.2 = 0 then 1 else 0)

/-- arXiv:1706.06221v3, PDF p.9, Eq.(48): two-Bell-state mixture, 0<p<1. -/
def bellMixture (p : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (p : ℂ) • pureDensity (sourceBellVector false) + (1 - p : ℂ) • pureDensity (sourceBellVector true)

/-- arXiv:1706.06221v3, PDF p.10, Eq.(52): isotropic state by target overlap F.
The accepted isotropic state uses depolarizing weight p, with F=p+(1-p)/d^2.
For d>=2 convert explicitly: p=(d^2 F-1)/(d^2-1). This retains F=0 and F=1. -/
def overlapIsotropic (d : ℕ) (F : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  QAlgorithms.Papers.Independent.Information100.P60.isotropic d
    (((d : ℝ) ^ 2 * F - 1) / ((d : ℝ) ^ 2 - 1))

/-- arXiv:1706.06221v3, PDF p.10, Eq.(54): exact isotropic LP coefficients.
The Icc interval enforces m<=i,k and i+k-n<=m before any natural subtraction. -/
def isotropicCoefficient (d n i k : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc (i + k - n) (min i k),
    (k.choose m : ℝ) * ((n - k).choose (i - m) : ℝ) *
      (-1 : ℝ) ^ (i - m) * (d - 1 : ℝ) ^ (k - m) *
      (d + 1 : ℝ) ^ (n - k + m - i)) / (d : ℝ) ^ n

/-- arXiv:1706.06221v3, PDF p.10, Eq.(53): linear feasibility before nonlinear
reciprocal/floor/log postprocessing. -/
def isotropicLPFeasible (d n : ℕ) (F epsilon eta : ℝ) (m : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ m i ∧ m i ≤ 1) ∧
  1 - epsilon ≤ ∑ i : Fin (n + 1),
    (n.choose i.val : ℝ) * F ^ i.val * (1 - F) ^ (n - i.val) * m i ∧
  ∀ k : Fin (n + 1),
    -eta ≤ ∑ i : Fin (n + 1), isotropicCoefficient d n i.val k.val * m i ∧
    (∑ i : Fin (n + 1), isotropicCoefficient d n i.val k.val * m i) ≤ eta

/-- arXiv:1706.06221v3, PDF p.18: Appendix-A state 3/4 |phi1><phi1|+1/4 |10><10|. -/
def appendixState (theta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let phi : EuclideanSpace ℂ (Fin 2 × Fin 2) := WithLp.toLp 2 fun p =>
    if p = (0, 0) then (Real.cos theta : ℂ)
    else if p = (1, 1) then (Real.sin theta : ℂ) else 0
  (3 / 4 : ℂ) • pureDensity phi + (1 / 4 : ℂ) • Matrix.single (1, 0) (1, 0) 1

/-- arXiv:1706.06221v3, PDF pp.18–19, Eq.(69): finite cross entropy in nats.
The extended version below guards singular support; this expression alone does not. -/
def crossEntropyFinite {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ := -(rho * cfc Real.log sigma).trace.re

/-- arXiv:1706.06221v3, PDF pp.18–19: cross entropy, infinity on support failure. -/
def crossEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : EReal :=
  if supportIncluded rho sigma then (crossEntropyFinite rho sigma : EReal) else ⊤

/-- arXiv:1706.06221v3, PDF p.18, Eq.(69): unshifted optimum in nats, not R in bits. -/
def crossEntropyOptimum {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {e | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    pptPrime sigma ∧ e = crossEntropy rho sigma}

/-- arXiv:1706.06221v3, PDF p.19, Eqs.(70)–(74): a feasible interior tangent point
with a unitary diagonalization and positive eigenvalues. Interior is taken in the
real Hermitian subspace; the PSD cone has empty interior in all complex matrices. -/
structure TangentPoint (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] where
  sigma : Matrix (A × B) (A × B) ℂ
  unitary : Matrix (A × B) (A × B) ℂ
  eigenvalue : A × B → ℝ
  unitary_left : unitary.conjTranspose * unitary = 1
  unitary_right : unitary * unitary.conjTranspose = 1
  eigenvalue_pos : ∀ i, 0 < eigenvalue i
  spectral : sigma = unitary * Matrix.diagonal (fun i => (eigenvalue i : ℂ)) * unitary.conjTranspose
  hermitian : sigma.IsHermitian
  feasible : pptPrime sigma
  isInterior : (⟨sigma, hermitian⟩ : {X : Matrix (A × B) (A × B) ℂ // X.IsHermitian}) ∈
    interior {X : {X : Matrix (A × B) (A × B) ℂ // X.IsHermitian} | pptPrime X.val}

/-- arXiv:1706.06221v3, PDF p.19, Eq.(71): divided difference of natural log;
equal positive eigenvalues use 1/lambda, including repeated eigenvalues. -/
def logDividedDifference (x y : ℝ) : ℝ :=
  if x = y then x⁻¹ else (Real.log x - Real.log y) / (x - y)

/-- arXiv:1706.06221v3, PDF p.19, Eq.(73): positive-sign gradient E;
the derivative of cross entropy is -Tr(E Delta). -/
def tangentGradient {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (P : TangentPoint A B) : Matrix (A × B) (A × B) ℂ :=
  P.unitary * Matrix.of (fun i j =>
    (logDividedDifference (P.eigenvalue i) (P.eigenvalue j) : ℂ) *
      (P.unitary.conjTranspose * rho * P.unitary) i j) * P.unitary.conjTranspose

/-- arXiv:1706.06221v3, PDF p.19, Eq.(74), with optional previous lower bound (75).
Bottom recovers Eq.(74). Slacks are explicit and nonnegative. -/
def cuttingPlaneOptimum {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {m : ℕ}
    (rho : Matrix (A × B) (A × B) ℂ) (P : Fin m → TangentPoint A B)
    (previous : EReal := ⊥) : EReal :=
  sInf {v | ∃ sigma : Matrix (A × B) (A × B) ℂ, ∃ t : ℝ, ∃ s : Fin m → ℝ,
    pptPrime sigma ∧ previous ≤ (t : EReal) ∧ (∀ i, 0 ≤ s i) ∧
    (∀ i, (tangentGradient rho (P i) * sigma).trace.re + t - s i =
      crossEntropyFinite rho (P i).sigma +
        (tangentGradient rho (P i) * (P i).sigma).trace.re) ∧ v = (t : EReal)}

/-! Sanity examples for the new definition layer. -/

example : log2 1 = 0 := by simp [log2]

example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) :
    partialTransposeB (partialTransposeB X) = X := rfl

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    pptPrime (0 : Matrix (A × B) (A × B) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, ?_⟩
  have h : partialTransposeB (0 : Matrix (A × B) (A × B) ℂ) = 0 := rfl
  rw [h]
  simp [traceNorm, cfc_zero]

example : target 1 (0, 0) (0, 0) = 1 := by simp [target]

example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ)
    (p q : (Fin 0 → A) × (Fin 0 → B)) : copies rho 0 p q = 1 := by simp [copies]

example {I : Type*} [Fintype I] [DecidableEq I]
    (rho G : Matrix I I ℂ) (epsilon : ℝ) (h : testingBeta epsilon rho G ≤ 0) :
    testingEntropy rho G epsilon = ⊤ := by simp [testingEntropy, not_lt.mpr h]

example : roundingGap 0 = 0 := by simp [roundingGap, log2]

example {I : Type*} [DecidableEq I] (X : Matrix I I ℂ) :
    dephasing (dephasing X) = dephasing X := by ext i j; simp [dephasing, Matrix.diagonal]

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    maximallyCorrelated rho (i, i) (j, j) = rho i j := by simp [maximallyCorrelated]

example (x : ℝ) : logDividedDifference x x = x⁻¹ := by simp [logDividedDifference]

example : sourceBellVector true (1, 0) = -sourceBellVector false (1, 0) := by
  simp [sourceBellVector]

example : overlapIsotropic 2 1 =
    pureDensity (QAlgorithms.Papers.Independent.Information100.P60.omega 2) := by
  norm_num [overlapIsotropic, QAlgorithms.Papers.Independent.Information100.P60.isotropic]

end QAlgorithms.Papers.Independent.Dependency50.P36


