-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
-- name    : QAlgorithms_Papers_Independent_Dependency50_P28
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:45:46.694746+00:00
-- url     : https://prove2.me/theorems/5a259703-3ea9-4f0d-bec2-e96743cad6dc
-- title:
--   Definitions for Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies
-- statement:
--   The objects the formalized statements of *Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies* (arXiv:1309.3228) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tr`: PDF p.3: the real trace of a Hermitian operator.
--   - `LE`: PDF p.3: Loewner order, not entrywise order.
--   - `SupportLE`: PDF p.4: for Hermitian matrices, support inclusion is reverse kernel inclusion.
--   - `scalarPower`: PDF p.4: zero eigenvalues contribute zero even at exponent zero or negative exponents.
--   - `pinch`: PDF p.4, (13): sum over DISTINCT eigenvalues, including the zero eigenspace. The off-domain value at a non-Hermitian reference is zero and is never used.
--   - `logNonnegativeExtended`: PDF p.4: extended logarithm on nonnegative quantities, log(0)=-infinity. Negative arguments are also sent to bottom but are excluded at every use.
--   - `Q`: PDF p.7: RAW sandwiched trace, without a support-failure infinity branch.
--   - `F`: PDF p.4, (17): logarithm of the raw sandwiched trace. Includes rho=0.
--   - `Dnew`: PDF p.2, (6): normalized sandwiched divergence. Used only for alpha>0, alpha≠1, and Tr rho>0. Support failure gives infinity when alpha>1.
--   - `Dold`: PDF p.2, (3): normalized Petz divergence, with the same domain restrictions as Dnew.
--   - `relativeEntropy`: PDF p.2, (4): normalized Umegaki entropy; the finite spectral log uses log(0)=0 only inside a trace against rho, where kernel terms vanish under SupportLE.
--   - `Dmax`: PDF p.10, (47): extended infimum of the exponential domination parameters. The empty infimum is +infinity; at rho=0 the infimum is -infinity.
--   - `POVM`: PDF p.3: an arbitrary finite POVM; outcome count may vary with copy number.
--   - `measuredF`: PDF p.4, (18): the measured raw logarithmic trace.
--   - `measuredD`: PDF p.6, (32): measured divergence, including +infinity on measured support failure.
--   - `maxMeasuredF`: PDF p.6: extended supremum over EVERY finite outcome cardinality. The attainability theorems separately assert that this supremum is a maximum.
--   - `maxMeasuredD`: PDF p.6: extended measurement optimum; attainment is an explicit conclusion below.
--   - `Positive`: PDF pp.3,7: positive, complex-linear maps. Complete positivity is a separate condition.
--   - `TP`: PDF pp.3,7: trace preservation on all matrices, not just on states.
--   - `CPTP`: PDF p.7: CPTP in the accepted arbitrary-ancilla definition.
--   - `TensorPositive`: PDF p.8, Remark III.18: every positive-degree tensor power is positive; piSuperop acts on arbitrary inputs, including entangled matrices.
--   - `npTest`: PDF p.10, (46): the specific strict Neyman-Pearson test.
--   - `typeI`: PDF p.8, (36): type-I rejection probability.
--   - `accept`: PDF pp.8-9: success/acceptance probability for the stated input operator.
--   - `scaled`: PDF pp.9-19: positive-index logarithmic normalization; uses n+1 to avoid 0 times infinity.
--   - `TestSequence`: PDF pp.8-9: a sequence of effects on exactly n+1 copies.
--   - `strongExponent`: PDF p.9, (42): infimum over test sequences, with limsup beta constraint and NEGATIVE LIMINF success. No exchange of limsup and liminf is made.
--   - `Hstar`: PDF p.3, (8): extended converse Hoeffding divergence.
--   - `psi`: PDF p.10, (48): real-valued psi, used on state pairs with nested supports, where its EReal precursor is finite in a neighborhood of s≥0.
--   - `phi`: PDF p.10, (49): phi retains its possible +infinity value.
--   - `rmax`: PDF p.14, (77): rmax is extended real, including the boundary value of phi.
--   - `psiTilde`: PDF p.14, (78): perspective transform of psi, used on 0≤u<1.
--   - `minTypeI`: PDF p.18: finite-n constrained type-I optimum; existence of a minimizer is asserted below. At density inputs the feasible set contains zero and has values in [0,1].
--   - `CutoffBound`: PDF p.18, (95): the bound must hold for EVERY positive rate.
--   - `cutoff`: PDF p.18: extended infimum defining cutoff; IV.18 also asserts its leastness/attainment.
--   - `Divergence`: Appendix A, pp.20-25: a divergence family over ALL finite dimensions. No additivity, basis invariance, or monotonicity is silently imposed.
--   - `newFamily`: Appendix A: the new finite-order divergence family; only positive orders unequal to one are used.
--   - `oldFamily`: Appendix A: the old finite-order divergence family.
--   - `maxFamily`: Appendix A, p.24: the infinite-order divergence is Dmax.
--   - `CommutingRangeMeasurement`: Appendix A, p.21: measurements are positive TP maps whose ENTIRE ranges commute. Output spaces may have any finite dimension; no fixed outcome bound is imposed.
--   - `MON`: Appendix A, p.20: MON is monotonicity under every CPTP map.
--   - `EPPMON`: Appendix A, p.21: monotonicity under every tensor-stable positive TP map.
--   - `MMON`: Appendix A, p.21: measurement monotonicity, for maps with commuting full range.
--   - `PMON`: Appendix A, p.21: reference-state pinching monotonicity.
--   - `AAP`: Appendix A, p.21: reference-state pinching attainability on actual tensor powers.
--   - `AAM`: Appendix A, p.21: there exists a sequence of measurements attaining the regularized value.
--   - `AM`: Appendix A, p.23: exact SINGLE-SHOT measurement attainment.
--   - `Sufficiency`: Appendix A, p.24, (A5)-(A6): sufficiency quantifies over every channel and demands one CPTP recovery map recovering BOTH states exactly.
--   - `PTPMON`: Appendix A, p.23, (A4): all positive TP maps; complete positivity is not required.
--   - `hilbertSchmidtDual`: Appendix A, p.21: Hilbert-Schmidt adjoint in matrix-unit coordinates, conjugate-linear in the FIRST inner-product slot.
--   - `Schwarz`: Appendix A, p.21: Schwarz inequality in Loewner order.
--   - `basisTranspose`: Appendix A, p.21: transpose in an arbitrary orthonormal basis.
--   - `SchwarzStochastic`: Appendix A, p.21: source's stochastic maps are convex combinations of two TP maps; the first dual is Schwarz, the second is Schwarz composed with a basis transpose.
--   - `SMON`: Appendix A, p.21: SMON includes positivity and TP, as stipulated above the list.
--   - `ClassicalOrder`: Appendix A, p.24: extended classical orders include zero, one and infinity.
--   - `classicalD`: Appendix A, p.24: classical Renyi entropy of finite probability laws. At order zero it is -log q(supp p); order one is relative entropy; infinity is the extended maximum log likelihood ratio.
--   - `allMeasuredValues`: Appendix A, p.24: the set of all measured classical Renyi values at all orders.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, https://arxiv.org/abs/1309.3228v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-! Mosonyi and Ogawa, arXiv:1309.3228v5. Natural logarithms, support-restricted
spectral powers, and extended-real asymptotic rates. Accepted definitions are imported;
new definitions are paper-local.
The four source-level deferrals are recorded in the assigned unit's HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators
open Filter QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.3: the real trace of a Hermitian operator. -/
def tr (A : Mat I) : ℝ := A.trace.re

/-- PDF p.3: Loewner order, not entrywise order. -/
def LE (A B : Mat I) : Prop := (B - A).PosSemidef

/-- PDF p.4: for Hermitian matrices, support inclusion is reverse kernel inclusion. -/
def SupportLE (rho sigma : Mat I) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- PDF p.4: zero eigenvalues contribute zero even at exponent zero or negative exponents. -/
def scalarPower (x t : ℝ) : ℝ := if 0 < x then Real.rpow x t else 0

/-- PDF p.4, (13): sum over DISTINCT eigenvalues, including the zero eigenspace.
The off-domain value at a non-Hermitian reference is zero and is never used. -/
def pinch (sigma A : Mat I) : Mat I :=
  if h : sigma.IsHermitian then
    ∑ l ∈ Finset.univ.image h.eigenvalues,
      let P : Mat I := cfc (fun x : ℝ => if x = l then 1 else 0) sigma
      P * A * P
  else 0

/-- PDF p.4: extended logarithm on nonnegative quantities, log(0)=-infinity.
Negative arguments are also sent to bottom but are excluded at every use. -/
def logNonnegativeExtended (x : ℝ) : EReal := if 0 < x then (Real.log x : EReal) else ⊥

/-- PDF p.7: RAW sandwiched trace, without a support-failure infinity branch. -/
def Q (alpha : ℝ) (rho sigma : Mat I) : ℝ :=
  let S := supportPower sigma ((1 - alpha) / (2 * alpha))
  tr (supportPower (S * rho * S) alpha)

/-- PDF p.4, (17): logarithm of the raw sandwiched trace. Includes rho=0. -/
def F (alpha : ℝ) (rho sigma : Mat I) : EReal := logNonnegativeExtended (Q alpha rho sigma)

/-- PDF p.2, (6): normalized sandwiched divergence. Used only for alpha>0, alpha≠1,
and Tr rho>0. Support failure gives infinity when alpha>1. -/
def Dnew (alpha : ℝ) (rho sigma : Mat I) : EReal :=
  if SupportLE rho sigma ∨ alpha < 1 then
    (((alpha - 1)⁻¹ : ℝ) : EReal) * (F alpha rho sigma - logNonnegativeExtended (tr rho))
  else ⊤

/-- PDF p.2, (3): normalized Petz divergence, with the same domain restrictions as Dnew. -/
def Dold (alpha : ℝ) (rho sigma : Mat I) : EReal :=
  if SupportLE rho sigma ∨ alpha < 1 then
    (((alpha - 1)⁻¹ : ℝ) : EReal) *
      (logNonnegativeExtended (tr (supportPower rho alpha * supportPower sigma (1 - alpha))) - logNonnegativeExtended (tr rho))
  else ⊤

/-- PDF p.2, (4): normalized Umegaki entropy; the finite spectral log uses log(0)=0
only inside a trace against rho, where kernel terms vanish under SupportLE. -/
def relativeEntropy (rho sigma : Mat I) : EReal :=
  if SupportLE rho sigma then
    ((tr (rho * (cfc Real.log rho - cfc Real.log sigma)) / tr rho : ℝ) : EReal)
  else ⊤

/-- PDF p.10, (47): extended infimum of the exponential domination parameters.
The empty infimum is +infinity; at rho=0 the infimum is -infinity. -/
def Dmax (rho sigma : Mat I) : EReal :=
  sInf {v | ∃ a : ℝ, v = (a : EReal) ∧ LE rho ((Real.exp a : ℂ) • sigma)}

/-- PDF p.3: an arbitrary finite POVM; outcome count may vary with copy number. -/
structure POVM (I : Type) [Fintype I] [DecidableEq I] where
  size : ℕ
  effect : Fin size → Mat I
  valid : IsPOVM effect

/-- PDF p.4, (18): the measured raw logarithmic trace. -/
def measuredF (alpha : ℝ) (rho sigma : Mat I) (M : POVM I) : EReal :=
  logNonnegativeExtended (∑ x, scalarPower (effectProb (M.effect x) rho) alpha * scalarPower (effectProb (M.effect x) sigma) (1 - alpha))

/-- PDF p.6, (32): measured divergence, including +infinity on measured support failure. -/
def measuredD (alpha : ℝ) (rho sigma : Mat I) (M : POVM I) : EReal :=
  Dnew alpha (Matrix.diagonal (fun x => (effectProb (M.effect x) rho : ℂ)))
    (Matrix.diagonal (fun x => (effectProb (M.effect x) sigma : ℂ)))

/-- PDF p.6: extended supremum over EVERY finite outcome cardinality.
The attainability theorems separately assert that this supremum is a maximum. -/
def maxMeasuredF (alpha : ℝ) (rho sigma : Mat I) : EReal :=
  sSup (Set.range (measuredF alpha rho sigma))

/-- PDF p.6: extended measurement optimum; attainment is an explicit conclusion below. -/
def maxMeasuredD (alpha : ℝ) (rho sigma : Mat I) : EReal :=
  sSup (Set.range (measuredD alpha rho sigma))

/-- PDF pp.3,7: positive, complex-linear maps. Complete positivity is a separate condition. -/
def Positive (Phi : Mat I →ₗ[ℂ] Mat J) : Prop :=
  ∀ A, A.PosSemidef → (Phi A).PosSemidef

/-- PDF pp.3,7: trace preservation on all matrices, not just on states. -/
def TP (Phi : Mat I →ₗ[ℂ] Mat J) : Prop := ∀ A, (Phi A).trace = A.trace

/-- PDF p.7: CPTP in the accepted arbitrary-ancilla definition. -/
def CPTP (Phi : Mat I →ₗ[ℂ] Mat J) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive Phi ∧ TP Phi

/-- PDF p.8, Remark III.18: every positive-degree tensor power is positive;
piSuperop acts on arbitrary inputs, including entangled matrices. -/
def TensorPositive (Phi : Mat I →ₗ[ℂ] Mat J) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A : Mat (Fin n → I), A.PosSemidef →
    (piSuperop (fun _ : Fin n => (Phi : Mat I → Mat J)) A).PosSemidef

/-- PDF p.10, (46): the specific strict Neyman-Pearson test. -/
def npTest (rho sigma : Mat I) (n : ℕ) (a : ℝ) : Mat (Fin n → I) :=
  positiveProjection (copies n rho - (Real.exp ((n : ℝ) * a) : ℂ) • copies n sigma)

/-- PDF p.8, (36): type-I rejection probability. -/
def typeI (rho : Mat I) (n : ℕ) (T : Mat (Fin n → I)) : ℝ :=
  tr (copies n rho * (1 - T))

/-- PDF pp.8-9: success/acceptance probability for the stated input operator. -/
def accept (rho : Mat I) (n : ℕ) (T : Mat (Fin n → I)) : ℝ := tr (copies n rho * T)

/-- PDF pp.9-19: positive-index logarithmic normalization; uses n+1 to avoid 0 times infinity. -/
def scaled (n : ℕ) (v : EReal) : EReal := ((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * v

/-- PDF pp.8-9: a sequence of effects on exactly n+1 copies. -/
def TestSequence (I : Type) [Fintype I] [DecidableEq I] :=
  ∀ n : ℕ, {T : Mat (Fin (n + 1) → I) // IsEffect T}

/-- PDF p.9, (42): infimum over test sequences, with limsup beta constraint and
NEGATIVE LIMINF success. No exchange of limsup and liminf is made. -/
def strongExponent (rho sigma : Mat I) (r : ℝ) : EReal :=
  sInf {v | ∃ T : TestSequence I,
    Filter.limsup (fun n => scaled n (logNonnegativeExtended (accept sigma (n + 1) (T n).1))) atTop ≤ -(r : EReal) ∧
    v = -Filter.liminf (fun n => scaled n (logNonnegativeExtended (accept rho (n + 1) (T n).1))) atTop}

/-- PDF p.3, (8): extended converse Hoeffding divergence. -/
def Hstar (rho sigma : Mat I) (r : ℝ) : EReal :=
  sSup {v | ∃ alpha : ℝ, 1 < alpha ∧
    v = (((alpha - 1) / alpha : ℝ) : EReal) * ((r : EReal) - Dnew alpha rho sigma)}

/-- PDF p.10, (48): real-valued psi, used on state pairs with nested supports,
where its EReal precursor is finite in a neighborhood of s≥0. -/
def psi (rho sigma : Mat I) (s : ℝ) : ℝ := (F (s + 1) rho sigma).toReal

/-- PDF p.10, (49): phi retains its possible +infinity value. -/
def phi (rho sigma : Mat I) (a : ℝ) : EReal :=
  sSup {v | ∃ s : ℝ, 0 ≤ s ∧ v = ((a * s - psi rho sigma s : ℝ) : EReal)}

/-- PDF p.14, (77): rmax is extended real, including the boundary value of phi. -/
def rmax (rho sigma : Mat I) : EReal :=
  phi rho sigma (Dmax rho sigma).toReal + Dmax rho sigma

/-- PDF p.14, (78): perspective transform of psi, used on 0≤u<1. -/
def psiTilde (rho sigma : Mat I) (u : ℝ) : ℝ := (1 - u) * psi rho sigma (u / (1 - u))

/-- PDF p.18: finite-n constrained type-I optimum; existence of a minimizer is asserted below.
At density inputs the feasible set contains zero and has values in [0,1]. -/
def minTypeI (rho sigma : Mat I) (n : ℕ) (r : ℝ) : ℝ :=
  sInf {v | ∃ T : Mat (Fin n → I), IsEffect T ∧
    accept sigma n T ≤ Real.exp (-(n : ℝ) * r) ∧ v = typeI rho n T}

/-- PDF p.18, (95): the bound must hold for EVERY positive rate. -/
def CutoffBound (rho sigma : Mat I) (kappa r0 : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r →
    Filter.limsup (fun n => scaled n (logNonnegativeExtended (1 - minTypeI rho sigma (n + 1) r))) atTop ≤
      ((-kappa * (r - r0) : ℝ) : EReal)

/-- PDF p.18: extended infimum defining cutoff; IV.18 also asserts its leastness/attainment. -/
def cutoff (rho sigma : Mat I) (kappa : ℝ) : EReal :=
  sInf {v | ∃ r0 : ℝ, v = (r0 : EReal) ∧ CutoffBound rho sigma kappa r0}

/-- PDF p.4 convention, checked also at the exponent zero. -/
example : scalarPower 0 0 = 0 := by simp [scalarPower]

/-- PDF p.4 convention at a negative exponent. -/
example : scalarPower 0 (-1) = 0 := by simp [scalarPower]

/-- PDF p.4: a zero trace has logarithm -infinity. -/
example : logNonnegativeExtended 0 = ⊥ := by simp [logNonnegativeExtended]

/-- Natural logarithms, PDF p.4. -/
example : logNonnegativeExtended 1 = 0 := by simp [logNonnegativeExtended]

/-- Tensor product empty case; asymptotic sequences themselves start at one copy. -/
example (A : Mat I) (x y : Fin 0 → I) : copies 0 A x y = 1 := by simp [copies]

/-- Support inclusion is reflexive, including the zero matrix. -/
example (A : Mat I) : SupportLE A A := le_rfl

/-- PDF p.2: support failure has the required infinity branch at alpha>1. -/
example (rho sigma : Mat I) (alpha : ℝ) (ha : 1 < alpha) (h : ¬ SupportLE rho sigma) :
    Dnew alpha rho sigma = ⊤ := by
  simp [Dnew, h, not_lt.mpr (le_of_lt ha)]

/-- The identity map preserves trace without a state restriction. -/
example : TP (LinearMap.id : Mat I →ₗ[ℂ] Mat I) := by intro A; rfl

/-- Appendix A, pp.20-25: a divergence family over ALL finite dimensions.
No additivity, basis invariance, or monotonicity is silently imposed. -/
abbrev Divergence := ∀ (K : Type) [Fintype K] [DecidableEq K], Mat K → Mat K → EReal

/-- Appendix A: the new finite-order divergence family; only positive orders unequal to one are used. -/
def newFamily (alpha : ℝ) : Divergence := fun _ _ _ rho sigma => Dnew alpha rho sigma

/-- Appendix A: the old finite-order divergence family. -/
def oldFamily (alpha : ℝ) : Divergence := fun _ _ _ rho sigma => Dold alpha rho sigma

/-- Appendix A, p.24: the infinite-order divergence is Dmax. -/
def maxFamily : Divergence := fun _ _ _ rho sigma => Dmax rho sigma

/-- Appendix A, p.21: measurements are positive TP maps whose ENTIRE ranges commute.
Output spaces may have any finite dimension; no fixed outcome bound is imposed. -/
structure CommutingRangeMeasurement (I : Type) [Fintype I] [DecidableEq I] where
  out : Type
  [finite : Fintype out]
  [decidable : DecidableEq out]
  map : Mat I →ₗ[ℂ] Mat out
  positive : Positive map
  tracePreserving : TP map
  commuting : ∀ A B, Commute (map A) (map B)

attribute [instance] CommutingRangeMeasurement.finite CommutingRangeMeasurement.decidable

/-- Appendix A, p.20: MON is monotonicity under every CPTP map. -/
def MON (d : Divergence) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (rho sigma : Mat I), IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ Phi : Mat I →ₗ[ℂ] Mat J, CPTP Phi → d J (Phi rho) (Phi sigma) ≤ d I rho sigma

/-- Appendix A, p.21: monotonicity under every tensor-stable positive TP map. -/
def EPPMON (d : Divergence) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (rho sigma : Mat I), IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ Phi : Mat I →ₗ[ℂ] Mat J, TP Phi → TensorPositive Phi →
      d J (Phi rho) (Phi sigma) ≤ d I rho sigma

/-- Appendix A, p.21: measurement monotonicity, for maps with commuting full range. -/
def MMON (d : Divergence) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ (rho sigma : Mat I),
    IsDensityMatrix rho → IsDensityMatrix sigma → ∀ M : CommutingRangeMeasurement I,
      d M.out (M.map rho) (M.map sigma) ≤ d I rho sigma

/-- Appendix A, p.21: reference-state pinching monotonicity. -/
def PMON (d : Divergence) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ (rho sigma : Mat I),
    IsDensityMatrix rho → IsDensityMatrix sigma → d I (pinch sigma rho) sigma ≤ d I rho sigma

/-- Appendix A, p.21: reference-state pinching attainability on actual tensor powers. -/
def AAP (d : Divergence) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ (rho sigma : Mat I),
    IsDensityMatrix rho → IsDensityMatrix sigma →
    Tendsto (fun n => scaled n (d (Fin (n + 1) → I)
      (pinch (copies (n + 1) sigma) (copies (n + 1) rho)) (copies (n + 1) sigma)))
      atTop (nhds (d I rho sigma))

/-- Appendix A, p.21: there exists a sequence of measurements attaining the regularized value. -/
def AAM (d : Divergence) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ (rho sigma : Mat I),
    IsDensityMatrix rho → IsDensityMatrix sigma →
    ∃ M : ∀ n : ℕ, CommutingRangeMeasurement (Fin (n + 1) → I),
      Tendsto (fun n => scaled n (d (M n).out
        ((M n).map (copies (n + 1) rho)) ((M n).map (copies (n + 1) sigma))))
        atTop (nhds (d I rho sigma))

/-- Appendix A, p.23: exact SINGLE-SHOT measurement attainment. -/
def AM (d : Divergence) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ (rho sigma : Mat I),
    IsDensityMatrix rho → IsDensityMatrix sigma → ∃ M : CommutingRangeMeasurement I,
      d M.out (M.map rho) (M.map sigma) = d I rho sigma

/-- Appendix A, p.24, (A5)-(A6): sufficiency quantifies over every channel and demands
one CPTP recovery map recovering BOTH states exactly. -/
def Sufficiency (d : Divergence) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (rho sigma : Mat I), IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ Phi : Mat I →ₗ[ℂ] Mat J, CPTP Phi →
    d J (Phi rho) (Phi sigma) = d I rho sigma →
      ∃ Psi : Mat J →ₗ[ℂ] Mat I, CPTP Psi ∧ Psi (Phi rho) = rho ∧ Psi (Phi sigma) = sigma

/-- Appendix A, p.23, (A4): all positive TP maps; complete positivity is not required. -/
def PTPMON (d : Divergence) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (rho sigma : Mat I), IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ Phi : Mat I →ₗ[ℂ] Mat J, Positive Phi → TP Phi →
      d J (Phi rho) (Phi sigma) ≤ d I rho sigma

/-- Appendix A, p.21: Hilbert-Schmidt adjoint in matrix-unit coordinates, conjugate-linear
in the FIRST inner-product slot. -/
def hilbertSchmidtDual (Phi : Mat I →ₗ[ℂ] Mat J) (B : Mat J) : Mat I :=
  fun i j => ∑ k, ∑ l, conj ((Phi (Matrix.single i j 1)) k l) * B k l

/-- Appendix A, p.21: Schwarz inequality in Loewner order. -/
def Schwarz (Phi : Mat I → Mat J) : Prop :=
  ∀ A, LE ((Phi A)ᴴ * Phi A) (Phi (Aᴴ * A))

/-- Appendix A, p.21: transpose in an arbitrary orthonormal basis. -/
def basisTranspose (U : Matrix.unitaryGroup I ℂ) (A : Mat I) : Mat I :=
  (U : Mat I) * ((U : Mat I)ᴴ * A * (U : Mat I))ᵀ * (U : Mat I)ᴴ

/-- Appendix A, p.21: source's stochastic maps are convex combinations of two TP maps;
the first dual is Schwarz, the second is Schwarz composed with a basis transpose. -/
def SchwarzStochastic (Phi : Mat I →ₗ[ℂ] Mat J) : Prop :=
  ∃ p : ℝ, ∃ Phi1 Phi2 : Mat I →ₗ[ℂ] Mat J,
    0 ≤ p ∧ p ≤ 1 ∧ TP Phi1 ∧ TP Phi2 ∧ Schwarz (hilbertSchmidtDual Phi1) ∧
    (∃ U : Matrix.unitaryGroup J ℂ, Schwarz (fun A => hilbertSchmidtDual Phi2 (basisTranspose U A))) ∧
    ∀ A, Phi A = (p : ℂ) • Phi1 A + ((1 - p : ℝ) : ℂ) • Phi2 A

/-- Appendix A, p.21: SMON includes positivity and TP, as stipulated above the list. -/
def SMON (d : Divergence) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (rho sigma : Mat I), IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ Phi : Mat I →ₗ[ℂ] Mat J, Positive Phi → TP Phi → SchwarzStochastic Phi →
      d J (Phi rho) (Phi sigma) ≤ d I rho sigma

/-- Appendix A, p.24: extended classical orders include zero, one and infinity. -/
inductive ClassicalOrder where
  | finite (alpha : ℝ) (nonnegative : 0 ≤ alpha)
  | infinity

/-- Appendix A, p.24: classical Renyi entropy of finite probability laws.
At order zero it is -log q(supp p); order one is relative entropy;
infinity is the extended maximum log likelihood ratio. -/
def classicalD {X : Type} [Fintype X] (order : ClassicalOrder) (p q : X → ℝ) : EReal :=
  match order with
  | .infinity => sSup {v | ∃ x, 0 < p x ∧
      v = if 0 < q x then logNonnegativeExtended (p x / q x) else ⊤}
  | .finite alpha _ =>
    if alpha = 0 then -logNonnegativeExtended (∑ x, if 0 < p x then q x else 0)
    else if alpha = 1 then
      if ∀ x, 0 < p x → 0 < q x then
        ((∑ x, if 0 < p x then p x * Real.log (p x / q x) else 0 : ℝ) : EReal)
      else ⊤
    else if (∀ x, 0 < p x → 0 < q x) ∨ alpha < 1 then
      (((alpha - 1)⁻¹ : ℝ) : EReal) *
        logNonnegativeExtended (∑ x, scalarPower (p x) alpha * scalarPower (q x) (1 - alpha))
    else ⊤

/-- Appendix A, p.24: the set of all measured classical Renyi values at all orders. -/
def allMeasuredValues (rho sigma : Mat I) : Set EReal :=
  {v | ∃ order : ClassicalOrder, ∃ M : POVM I,
    v = classicalD order (fun x => effectProb (M.effect x) rho) (fun x => effectProb (M.effect x) sigma)}

/-- The support-power convention applies to a zero matrix at exponent zero. -/
example : supportPower (0 : Mat I) 0 = 0 := by simp [supportPower, scalarPower, cfc_zero]

/-- Basis transpose agrees with computational transpose at the identity basis. -/
example (A : Mat I) : basisTranspose 1 A = Aᵀ := by simp [basisTranspose]

/-- The Hilbert-Schmidt dual of the zero map is zero. -/
example (B : Mat J) : hilbertSchmidtDual (0 : Mat I →ₗ[ℂ] Mat J) B = 0 := by
  funext i j
  change (∑ k, ∑ l,
    conj (((0 : Mat I →ₗ[ℂ] Mat J) (Matrix.single i j 1)) k l) * B k l) = 0
  simp

/-- One-copy logarithmic scaling is the identity, including either infinity. -/
example (v : EReal) : scaled 0 v = v := by simp [scaled]

/-- Scalar powers preserve the unit eigenvalue at every order. -/
example (t : ℝ) : scalarPower 1 t = 1 := by simp [scalarPower]

/-- PDF p.3: the positive part of the zero Hermitian operator is zero. -/
example : positivePart (0 : Mat I) = 0 := by simp [QAlgorithms.Papers.Independent.Information100.P07.positivePart, cfc_zero]

/-- PDF p.3: a zero eigenvalue is excluded from the strict positive spectral projector. -/
example : positiveProjection (0 : Mat I) = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P07.positiveProjection, QAlgorithms.Papers.Independent.Information100.P07.positivePart, cfc_zero,
    QAlgorithms.Papers.Independent.Information100.P07.support, QAlgorithms.Papers.Independent.Information100.P07.projection, QAlgorithms.Papers.Independent.Information100.P07.operatorRange,
    Submodule.starProjection_bot]

/-- PDF p.4: the support of the zero operator is the zero projection. -/
example : support (0 : Mat I) = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P07.support, QAlgorithms.Papers.Independent.Information100.P07.projection, QAlgorithms.Papers.Independent.Information100.P07.operatorRange,
    Submodule.starProjection_bot]

/-- PDF p.24: zero-order classical entropy vanishes for identical one-point laws. -/
example : classicalD (.finite 0 (by norm_num)) (fun _ : Fin 1 => 1) (fun _ => 1) = 0 := by
  simp [classicalD, logNonnegativeExtended]

/- SOURCE STATEMENTS BEGIN: proofs intentionally deferred. -/

end QAlgorithms.Papers.Independent.Dependency50.P28


