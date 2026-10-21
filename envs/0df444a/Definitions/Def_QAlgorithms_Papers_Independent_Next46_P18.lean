-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
-- name    : QAlgorithms_Papers_Independent_Next46_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T15:07:45.223375+00:00
-- url     : https://prove2.me/theorems/23919b97-040d-4b67-8bf9-4a7f4da11800
-- title:
--   Definitions for Gaussian classical-quantum channels: gain of entanglement-assistance
-- statement:
--   The objects the formalized statements of *Gaussian classical-quantum channels: gain of entanglement-assistance* (arXiv:1211.4774) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MinimalNoise`: PDF p.5: minimal solution of the physical covariance inequality (15).
--   - `DualChannel`: PDF pp.2-3: genuine CPTP predual and its full bounded-observable dual. Duality is required on every trace-class operator, not just densities or Weyls. The source's regular irreducible Weyl systems are supplied separately.
--   - `GaussianChannel`: PDF p.3, (3)-(4): centered Gaussian dual law and exact CP half factor. K has input rows and output columns. The dual acts on every bounded observable; its normality and complete positivity follow from the CPTP predual and duality.
--   - `IsCQ`: PDF p.5: commuting images of ALL pairs of bounded output observables.
--   - `dilationOutput`: PDF pp.3-4, (12): actual receiver from the AD to BE unitary split.
--   - `weakOutput`: PDF p.4, (13): the weak complement uses the SAME unitary and environment. This remains a weak complement when the environment state is mixed.
--   - `GaussianDilation`: PDF pp.3-6, (5)-(13): minimal MODE Gaussian dilation, s_D=t, s_E=s. The joint Weyl identity specifies the actual canonical implementer on full trace class, independently of the channel's partial traces. No determinant of L, entropy inequality, pure environment or Stinespring minimality is assumed.
--   - `quadraticRaw`: PDF pp.6-7: closed quadratic-form value of R K epsilon K^t R^t. The jth derivative is i R K sqrt(epsilon)e_j applied to u. Infinity denotes failure to lie in the common form domain. This definition uses the genuine strongly continuous Weyl groups, never bounded canonical quadratures.
--   - `quadraticObservable`: PDF pp.6-7: positive self-adjoint realization of the specified closed form. The fallback is exposed: every theorem using this definition concludes the form-realization identity, so a missing realization cannot make its cost vacuous. No compactness or Gibbs trace assumption is imposed.
--   - `kTwo`: PDF p.11: Example 1 coupling, input (q1,p1,q2,p2), output (q,p).
--   - `kOne`: PDF p.13: Example 2 coupling K=diag(1,0).
--   - `squeezedNoise`: PDF p.13: v denotes sigma squared, and is positive in every theorem.
--   - `diagonalCovariance`: PDF pp.14,16: diagonal covariance with position variance E and momentum P.
--   - `deltaOne`: PDF p.14: the deficit is a scalar function, not a definition of mutual information.
--   - `deltaTwo`: PDF p.16: Etilde_1=P+1/2+E/4, with the printed square-root parentheses.
--   - `fOne`: PDF p.17: f1 is a named scalar logarithm, not the unassisted capacity.
--   - `fTwo`: PDF p.17: f2 is the scalar entropy comparison function, including x=1.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, https://arxiv.org/abs/1211.4774v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

/-!
Holevo, arXiv:1211.4774v1. Full separable Hilbert spaces, hbar=1, nats.
Only pinned accepted modules are imported. All new interfaces are paper-local.
The three false operational separation claims are inventoried in HARD.md;
no receiver restriction replaces them. Spectral objects are constructed in
the conclusions of the two realization theorems, never assumed as hypotheses.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)
open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

namespace QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-! Use frozen QuadratureIndex and physicalCommutationMatrix s 1 directly.
Entrywise complexification is Mathlib's Matrix.map Complex.ofReal.
The frozen quantumCovariance uses V+i Delta >= 0; applying it to 2 • gamma
is exactly gamma plus or minus i Delta/2 >= 0 for real gamma. Hermiticity supplies
real symmetry and complex conjugation supplies the other sign. -/

/-- PDF p.5: minimal solution of the physical covariance inequality (15). -/
def MinimalNoise {s : ℕ} (alpha : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ) : Prop :=
  quantumCovariance ((2 : ℝ) • alpha) ∧ ∀ beta : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
    quantumCovariance ((2 : ℝ) • beta) → (alpha - beta).PosSemidef → beta = alpha

/-- PDF pp.2-3: genuine CPTP predual and its full bounded-observable dual.
Duality is required on every trace-class operator, not just densities or Weyls.
The source's regular irreducible Weyl systems are supplied separately. -/
structure DualChannel (I J : Type) where
  predual : Channel I J
  dual : (Hilbert J →L[ℂ] Hilbert J) →L[ℂ] (Hilbert I →L[ℂ] Hilbert I)
  pairing : ∀ X, IsTraceClass X → ∀ B : Hilbert J →L[ℂ] Hilbert J,
    tracePair (predual.val X) (operatorCoeff B) =
      tracePair X (operatorCoeff (dual B))

/-- PDF p.3, (3)-(4): centered Gaussian dual law and exact CP half factor.
K has input rows and output columns. The dual acts on every bounded observable;
its normality and complete positivity follow from the CPTP predual and duality. -/
def GaussianChannel {I J : Type} {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) : Prop :=
  alpha.transpose = alpha ∧
    ((alpha.map Complex.ofReal) - (Complex.I / 2) •
      (((physicalCommutationMatrix t 1) - K.transpose * (physicalCommutationMatrix s 1) * K).map Complex.ofReal)).PosSemidef ∧
    ((alpha.map Complex.ofReal) + (Complex.I / 2) •
      (((physicalCommutationMatrix t 1) - K.transpose * (physicalCommutationMatrix s 1) * K).map Complex.ofReal)).PosSemidef ∧
    ∀ z, Phi.dual (WB.operator z) =
      Complex.exp (((-dotProduct z (alpha.mulVec z) / 2 : ℝ) : ℂ)) •
        WA.operator (K.mulVec z)

/-- PDF p.5: commuting images of ALL pairs of bounded output observables. -/
def IsCQ {I J : Type} (Phi : DualChannel I J) : Prop :=
  ∀ B C : Hilbert J →L[ℂ] Hilbert J,
    (Phi.dual B).comp (Phi.dual C) = (Phi.dual C).comp (Phi.dual B)

/-- PDF pp.3-4, (12): actual receiver from the AD to BE unitary split. -/
def dilationOutput {I J D F : Type}
    (U : Hilbert (I × D) ≃ₗᵢ[ℂ] Hilbert (J × F)) (env : State D)
    (X : Matrix I I ℂ) : Matrix J J ℂ :=
  traceSecond (boundedConjugation U.toLinearIsometry.toContinuousLinearMap
    (productCoeff X env.coefficients))

/-- PDF p.4, (13): the weak complement uses the SAME unitary and environment.
This remains a weak complement when the environment state is mixed. -/
def weakOutput {I J D F : Type}
    (U : Hilbert (I × D) ≃ₗᵢ[ℂ] Hilbert (J × F)) (env : State D)
    (X : Matrix I I ℂ) : Matrix F F ℂ :=
  traceFirst (boundedConjugation U.toLinearIsometry.toContinuousLinearMap
    (productCoeff X env.coefficients))

/-- PDF pp.3-6, (5)-(13): minimal MODE Gaussian dilation, s_D=t, s_E=s.
The joint Weyl identity specifies the actual canonical implementer on full
trace class, independently of the channel's partial traces. No determinant of
L, entropy inequality, pure environment or Stinespring minimality is assumed. -/
structure GaussianDilation {I J : Type} {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (D F : Type) where
  WD : ScaledWeylRepresentation D t 1
  WE : ScaledWeylRepresentation F s 1
  environment : State D
  beta : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ
  physical : quantumCovariance ((2 : ℝ) • beta)
  gaussian : ∀ z, weylTraceCharacteristic WD environment.coefficients z =
    gaussianFunction 0 beta z
  KD : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ
  L : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ
  LD : Matrix (QuadratureIndex t) (QuadratureIndex s) ℝ
  noise : alpha = KD.transpose * beta * KD
  blockBB : (physicalCommutationMatrix t 1) = K.transpose * (physicalCommutationMatrix s 1) * K + KD.transpose * (physicalCommutationMatrix t 1) * KD
  blockBE : K.transpose * (physicalCommutationMatrix s 1) * L + KD.transpose * (physicalCommutationMatrix t 1) * LD = 0
  blockEE : (physicalCommutationMatrix s 1) = L.transpose * (physicalCommutationMatrix s 1) * L + LD.transpose * (physicalCommutationMatrix t 1) * LD
  unitary : Hilbert (I × D) ≃ₗᵢ[ℂ] Hilbert (J × F)
  canonical : ∀ X : Matrix (I × D) (I × D) ℂ, IsTraceClass X →
    ∀ (z : InterleavedPhase t) (w : InterleavedPhase s),
    tracePair (boundedConjugation unitary.toLinearIsometry.toContinuousLinearMap X)
      (productCoeff (operatorCoeff (WB.operator z)) (operatorCoeff (WE.operator w))) =
    tracePair X (productCoeff
      (operatorCoeff (WA.operator (K.mulVec z + L.mulVec w)))
      (operatorCoeff (WD.operator (KD.mulVec z + LD.mulVec w))))
  receiver : ∀ X, IsTraceClass X →
    Phi.predual.val X = dilationOutput unitary environment X

/-- PDF pp.6-7: closed quadratic-form value of R K epsilon K^t R^t.
The jth derivative is i R K sqrt(epsilon)e_j applied to u. Infinity denotes
failure to lie in the common form domain. This definition uses the genuine
strongly continuous Weyl groups, never bounded canonical quadratures. -/
def quadraticRaw {I : Type} {s t : ℕ} (WA : ScaledWeylRepresentation I s 1)
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ) (epsilon : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ)
    (u : Hilbert I) : ℝ≥0∞ :=
  ∑ j : QuadratureIndex t,
    let orbit : ℝ → Hilbert I := fun r =>
      WA.operator (r • (fun i => (K * cfc Real.sqrt epsilon) i j)) u
    if DifferentiableAt ℝ orbit 0 then ENNReal.ofReal (‖deriv orbit 0‖ ^ 2) else ⊤

/-- PDF pp.6-7: positive self-adjoint realization of the specified closed form.
The fallback is exposed: every theorem using this definition concludes the
form-realization identity, so a missing realization cannot make its cost vacuous.
No compactness or Gibbs trace assumption is imposed. -/
def quadraticObservable {I : Type} {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (epsilon : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) : PositiveObservable I :=
  if h : ∃ F : PositiveObservable I, F.form = quadraticRaw WA K epsilon
    then Classical.choose h else zeroObservable I

/-- PDF p.11: Example 1 coupling, input (q1,p1,q2,p2), output (q,p). -/
def kTwo : Matrix (QuadratureIndex 2) (QuadratureIndex 1) ℝ :=
  fun i j => if i.2 = 0 ∧ i.1.val = j.2.val then 1 else 0

/-- PDF p.13: Example 2 coupling K=diag(1,0). -/
def kOne : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ :=
  fun i j => if i.2 = 0 ∧ j.2 = 0 then 1 else 0

/-- PDF p.13: v denotes sigma squared, and is positive in every theorem. -/
def squeezedNoise (v : ℝ) : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ :=
  Matrix.diagonal (fun i => if i.2 = 0 then v else 1 / (4 * v))

/-- PDF pp.14,16: diagonal covariance with position variance E and momentum P. -/
def diagonalCovariance (s : ℕ) (E P : ℝ) : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ :=
  Matrix.diagonal (fun i => if i.2 = 0 then E else P)

/-- PDF p.14: the deficit is a scalar function, not a definition of mutual information. -/
def deltaOne (E v P : ℝ) : ℝ :=
  g (Real.sqrt (E * P + E / (4 * v)) - 1 / 2) -
    g (Real.sqrt (E * P) - 1 / 2)

/-- PDF p.16: Etilde_1=P+1/2+E/4, with the printed square-root parentheses. -/
def deltaTwo (E P : ℝ) : ℝ :=
  g (Real.sqrt E * (Real.sqrt (P + 1 / 2 + E / 4) + Real.sqrt E / 2) - 1 / 2) +
  g (Real.sqrt E * (Real.sqrt (P + 1 / 2 + E / 4) - Real.sqrt E / 2) - 1 / 2) -
    2 * g (Real.sqrt (E * P) - 1 / 2)

/-- PDF p.17: f1 is a named scalar logarithm, not the unassisted capacity. -/
def fOne (x : ℝ) : ℝ := Real.log x

/-- PDF p.17: f2 is the scalar entropy comparison function, including x=1. -/
def fTwo (x : ℝ) : ℝ :=
  ((x + 1) / 2) * Real.log ((x + 1) / 2) -
    ((x - 1) / 2) * Real.log ((x - 1) / 2)

/-! Sanity examples pin the phase sign, coordinates, entropy units and zero cases. -/

example : (physicalCommutationMatrix 1 1) (0, 0) (0, 1) = 1 := by norm_num [physicalCommutationMatrix]

example : (physicalCommutationMatrix 1 1) (0, 1) (0, 0) = -1 := by norm_num [physicalCommutationMatrix]

example : g 0 = 0 := by norm_num [g]

example : fOne 1 = fTwo 1 := by norm_num [fOne, fTwo]

example : kTwo (0, 0) (0, 0) = 1 ∧ kTwo (1, 0) (0, 1) = 1 ∧
    kTwo (0, 1) (0, 0) = 0 := by norm_num [kTwo]

example (v : ℝ) : squeezedNoise v (0, 1) (0, 1) = 1 / (4 * v) := by
  simp [squeezedNoise]

example {s t : ℕ} (gamma : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ) :
    (0 : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ).transpose * gamma *
      (0 : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ) =
      (0 : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) := by simp

example {I : Type} {s t : ℕ} (WA : ScaledWeylRepresentation I s 1)
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ) (epsilon : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ)
    (h : ∃ F : PositiveObservable I, F.form = quadraticRaw WA K epsilon) :
    (quadraticObservable WA K epsilon).form = quadraticRaw WA K epsilon := by
  simp only [quadraticObservable, dif_pos h]
  exact (Classical.choose_spec h)

end QAlgorithms.Papers.Independent.Next46.P18


