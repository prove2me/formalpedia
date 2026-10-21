-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13
-- name    : QAlgorithms_Papers_Independent_Next46_P13
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:06:20.141896+00:00
-- url     : https://prove2.me/theorems/cc653b07-a555-4335-99f0-0a75099825ca
-- title:
--   Definitions for Geometric inequalities from phase space translations
-- statement:
--   The objects the formalized statements of *Geometric inequalities from phase space translations* (arXiv:1606.08603) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CompletedOperator`: PDF p.8: bounded operators; unbounded quadratures are represented through Weyl matrices.
--   - `coordinateBasis`: PDF p.8: canonical complete number basis.
--   - `IsNormalizedOperator`: PDF p.9: normalized positive trace-class operator, using the accepted state subtype.
--   - `HasTrivialKernel`: PDF p.9: full rank means trivial kernel, not a bounded inverse.
--   - `NumberLabels`: PDF p.8: d-mode number labels.
--   - `InterleavedPhaseVector`: PDF p.8: interleaved real phase coordinates (q_1,p_1,...,q_d,p_d).
--   - `HasMatrix`: Complete coefficient realization, PDF pp.8–10.
--   - `fromMatrix`: Select the unique bounded operator with these coefficients. Every use below concludes realization and integral/sum convergence, excluding the zero fallback.
--   - `sourceWeylArgument`: PDF p.8, (19): a=(Q+iP)/sqrt(2) gives W(xi)=D(-sqrt(pi)(xi_q+i xi_p)).
--   - `weylMatrix`: PDF pp.8–9, (19)–(20): the actual tensor product of canonical Fock Weyl coefficients.
--   - `phaseSpaceWeyl`: PDF p.8, (19): canonical multimode Weyl displacement, computed from all coefficients.
--   - `WeylRealized`: PDF pp.8–9: realization/normalization of the canonical Weyl operators.
--   - `translated`: PDF p.9, (21): displacement conjugation; Mathlib inner is conjugate-linear first.
--   - `ProbabilityDensity`: PDF pp.6–7,10: Lebesgue probability densities, including their measurability.
--   - `FullSupport`: PDF p.11: full support of the associated probability measure, including densities which vanish at isolated points. Every nonempty open set has positive mass.
--   - `densityTranslate`: PDF p.7, (16): f^(theta)(xi)=f(xi-theta).
--   - `hybridIntegrand`: PDF p.10, (26): scalar matrix coefficients of the weak displacement integral.
--   - `hybridConvolution`: PDF p.10, (26): canonical hybrid convolution, with its nonsingular t=0 value.
--   - `HybridRealized`: Convergence and physical output for (26); these are conclusions, not input regularity.
--   - `quantumD`: PDF p.9: extended Umegaki relative entropy from the accepted finite-projection formula. The fallback is infinity; all theorem arguments are actual trace-class states.
--   - `classicalRelativeEntropy`: PDF p.6, (13): extended classical KL, with natural logs, never toReal(infinity).
--   - `standardGaussian`: PDF p.10, (27): standard Gaussian density on R^(2d).
--   - `gaussianHeatFlow`: PDF p.10, (25): canonical heat flow, including t=0.
--   - `classicalHeat`: PDF pp.14–15, (43): Gaussian convolution of variance s; s=0 is the identity.
--   - `passive`: PDF p.20, Definition 3: computed decreasing-eigenvalue Fock rearrangement.
--   - `photonMeanExtended`: PDF p.21, Lemma 7: extended expectation, even when the mean is infinite.
--   - `entropyReal`: Used only with finite entropy established in the Gaussian conclusions.
--   - `thermalEntropyPower`: PDF p.14, (42), in one mode, on the finite-entropy domain certified below.
--   - `attenuator`: PDF p.18, (52): canonical attenuator, transmissivity exp(-t), vacuum environment. This reuses the accepted full Fock thermal-channel dilation.
--   - `amplifierFlow`: PDF pp.23,32, (82): canonical amplifier with gain exp(t).
--   - `ThermalChannelRealized`: Convergence and actual output of the accepted attenuator/thermal dilation.
--   - `AmplifierOutputRealized`: Convergence and actual amplifier output; no unsupported sum/default value.
--   - `displaced`: PDF pp.9–10: single-mode phase-space displacement in the source's normalization.
--   - `heatIntegrand`: PDF p.10, (25): scalar coefficients of the one-mode Gaussian heat integral.
--   - `heatOne`: PDF p.10, (25): single-mode canonical heat, with nonsingular zero time.
--   - `HeatOneRealized`: Convergence and physical output for the single-mode heat integral.
--   - `displacementD`: PDF p.9, (22): coordinate displacement-relative-entropy family.
--   - `FiniteDisplacementC2`: Finite local C2 displacement family. This is a CONCLUSION only for thermal states below, never an invented input regularity assumption for the all-state nodes.
--   - `fisher`: PDF p.9, (22): trace of the actual displacement Hessian. The thermal theorem concludes finite local C2 and the actual derivative value, preventing deriv defaults.
--   - `ouDampingRate`: PDF pp.4,23: zeta is the fixed generator parameter mu^2-lambda^2.
--   - `stationaryMean`: PDF pp.4,23: constructed stationary mean occupation.
--   - `ou`: PDF pp.4,23: actual qOU channel as an attenuator with the stationary thermal environment. Its intensity transmissivity is exp(-(mu^2-lambda^2)t); differentiating the dilation gives exactly mu^2 L_minus + lambda^2 L_plus, without negative-time maps.
--   - `stationaryState`: PDF pp.4,23: fixed point computed from the generator parameters.
--   - `Stationary`: PDF pp.4,23: stationarity for the whole semigroup, only at nonnegative times.
--   - `quadratureCovariance`: PDF p.31: covariance M=tr(rho {R_j,R_k}), for centered states and [Q,P]=i. The accepted complex covariance uses C=(Var Q+Var P)/2, B=<a^2>-<a>^2.
--   - `oneModeSymplecticMatrix`: PDF p.32: the standard one-mode symplectic form.
--   - `OrthogonalSymplectic`: PDF p.32: both orthogonal and symplectic, without deleting rotations.
--   - `squeeze`: PDF p.32: the squeezing diagonal, z>=1 in the theorem.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, https://arxiv.org/abs/1606.08603v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

/-!
Statements from Geometric inequalities from phase space translations,
arXiv:1606.08603v2. Full completed oscillator spaces; natural logarithms.
Analytically unpinned all-state claims are recorded in HARD.md, never replaced
by Gaussian specializations or by assumed output differentiability.
Real entropy/relative-entropy derivatives below carry finiteness and existence
in their conclusions on the explicit Gaussian domain. All time derivatives at
zero are right derivatives. Mechanical compilation is pending batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

namespace D
export QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive State operatorTrace relativeEntropy)
end D

namespace B
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad IsDensity operatorOfMatrix HasFockMatrix
   displacementMatrix displacement krausTerm amplifierKraus amplifierMatrix
   AmplifierRealized ThermalRealized thermalMatrix)
end B

namespace C
export QAlgorithms.Papers.Independent.Claimed50.P39
  (g photonMeanThermalState thermalProbability eigenvalue fockEntropyNats
   IsGaussian meanA covarianceC covarianceB thermal thermalOutputMatrix thermalTerm)
end C

/-- PDF p.8: bounded operators; unbounded quadratures are represented through Weyl matrices. -/
abbrev CompletedOperator (I : Type*) := QAlgorithms.RealRegisters.Hilbert I →L[ℂ] QAlgorithms.RealRegisters.Hilbert I

/-- PDF p.8: canonical complete number basis. -/
def coordinateBasis (I : Type*) : HilbertBasis I ℂ (QAlgorithms.RealRegisters.Hilbert I) :=
  ⟨LinearIsometryEquiv.refl ℂ (QAlgorithms.RealRegisters.Hilbert I)⟩

/-- PDF p.9: normalized positive trace-class operator, using the accepted state subtype. -/
def IsNormalizedOperator {I : Type*} (X : CompletedOperator I) : Prop :=
  ∃ rho : D.State (coordinateBasis I), rho.val.val = X

/-- PDF p.9: full rank means trivial kernel, not a bounded inverse. -/
def HasTrivialKernel {I : Type*} (X : CompletedOperator I) : Prop := Function.Injective X

/-- PDF p.8: d-mode number labels. -/
abbrev NumberLabels (d : ℕ) := Fin d → ℕ

/-- PDF p.8: interleaved real phase coordinates (q_1,p_1,...,q_d,p_d). -/
abbrev InterleavedPhaseVector (d : ℕ) := (Fin d × Fin 2) → ℝ

/-- Complete coefficient realization, PDF pp.8–10. -/
def HasMatrix {I : Type*} (X : CompletedOperator I) (K : I → I → ℂ) : Prop :=
  ∀ i j, (X (coordinateBasis I j)) i = K i j

/-- Select the unique bounded operator with these coefficients. Every use below
concludes realization and integral/sum convergence, excluding the zero fallback. -/
def fromMatrix {I : Type*} (K : I → I → ℂ) : CompletedOperator I :=
  if h : ∃ X : CompletedOperator I, HasMatrix X K then Classical.choose h else 0

/-- PDF p.8, (19): a=(Q+iP)/sqrt(2) gives W(xi)=D(-sqrt(pi)(xi_q+i xi_p)). -/
def sourceWeylArgument {d : ℕ} (xi : InterleavedPhaseVector d) (k : Fin d) : ℂ :=
  -(Real.sqrt Real.pi : ℂ) * ((xi (k, 0) : ℂ) + Complex.I * (xi (k, 1) : ℂ))

/-- PDF pp.8–9, (19)–(20): the actual tensor product of canonical Fock Weyl coefficients. -/
def weylMatrix {d : ℕ} (xi : InterleavedPhaseVector d) (i j : NumberLabels d) : ℂ :=
  ∏ k, B.displacementMatrix (sourceWeylArgument xi k) (i k) (j k)

/-- PDF p.8, (19): canonical multimode Weyl displacement, computed from all coefficients. -/
def phaseSpaceWeyl {d : ℕ} (xi : InterleavedPhaseVector d) : CompletedOperator (NumberLabels d) := fromMatrix (weylMatrix xi)

/-- PDF pp.8–9: realization/normalization of the canonical Weyl operators. -/
def WeylRealized (d : ℕ) : Prop :=
  ∀ xi : InterleavedPhaseVector d, HasMatrix (phaseSpaceWeyl xi) (weylMatrix xi) ∧
    (phaseSpaceWeyl xi).adjoint.comp (phaseSpaceWeyl xi) = 1 ∧ (phaseSpaceWeyl xi).comp (phaseSpaceWeyl xi).adjoint = 1

/-- PDF p.9, (21): displacement conjugation; Mathlib inner is conjugate-linear first. -/
def translated {d : ℕ} (xi : InterleavedPhaseVector d) (X : CompletedOperator (NumberLabels d)) : CompletedOperator (NumberLabels d) :=
  (phaseSpaceWeyl xi).comp (X.comp (phaseSpaceWeyl xi).adjoint)

/-- PDF pp.6–7,10: Lebesgue probability densities, including their measurability. -/
def ProbabilityDensity {d : ℕ} (f : InterleavedPhaseVector d → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x) = 1

/-- PDF p.11: full support of the associated probability measure, including densities
which vanish at isolated points. Every nonempty open set has positive mass. -/
def FullSupport {d : ℕ} (f : InterleavedPhaseVector d → ℝ) : Prop :=
  ∀ U : Set (InterleavedPhaseVector d), IsOpen U → U.Nonempty →
    0 < (volume.withDensity (fun x => ENNReal.ofReal (f x))) U

/-- PDF p.7, (16): f^(theta)(xi)=f(xi-theta). -/
def densityTranslate {d : ℕ} (theta : InterleavedPhaseVector d) (f : InterleavedPhaseVector d → ℝ) : InterleavedPhaseVector d → ℝ :=
  fun xi => f (xi - theta)

/-- PDF p.10, (26): scalar matrix coefficients of the weak displacement integral. -/
def hybridIntegrand {d : ℕ} (f : InterleavedPhaseVector d → ℝ) (t : ℝ) (X : CompletedOperator (NumberLabels d))
    (i j : NumberLabels d) (xi : InterleavedPhaseVector d) : ℂ :=
  (f xi : ℂ) * (translated (Real.sqrt t • xi) X (coordinateBasis (NumberLabels d) j)) i

/-- PDF p.10, (26): canonical hybrid convolution, with its nonsingular t=0 value. -/
def hybridConvolution {d : ℕ} (f : InterleavedPhaseVector d → ℝ) (t : ℝ) (X : CompletedOperator (NumberLabels d)) : CompletedOperator (NumberLabels d) :=
  if t = 0 then X else fromMatrix (fun i j => ∫ xi, hybridIntegrand f t X i j xi)

/-- Convergence and physical output for (26); these are conclusions, not input regularity. -/
def HybridRealized {d : ℕ} (f : InterleavedPhaseVector d → ℝ) (t : ℝ) (X : CompletedOperator (NumberLabels d)) : Prop :=
  (∀ i j, Integrable (hybridIntegrand f t X i j)) ∧
    HasMatrix (hybridConvolution f t X) (fun i j => ∫ xi, hybridIntegrand f t X i j xi) ∧
    IsNormalizedOperator (hybridConvolution f t X)

/-- PDF p.9: extended Umegaki relative entropy from the accepted finite-projection
formula. The fallback is infinity; all theorem arguments are actual trace-class states. -/
def quantumD {I : Type*} (X Y : CompletedOperator I) : ℝ≥0∞ :=
  if h : D.IsTraceClass X ∧ D.IsTraceClass Y then
    D.relativeEntropy ⟨X, h.1⟩ ⟨Y, h.2⟩ else ⊤

/-- PDF p.6, (13): extended classical KL, with natural logs, never toReal(infinity). -/
def classicalRelativeEntropy {d : ℕ} (f g : InterleavedPhaseVector d → ℝ) : ℝ≥0∞ :=
  InformationTheory.klDiv (volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (volume.withDensity (fun x => ENNReal.ofReal (g x)))

/-- PDF p.10, (27): standard Gaussian density on R^(2d). -/
def standardGaussian (d : ℕ) (xi : InterleavedPhaseVector d) : ℝ :=
  Real.exp (-(∑ j, xi j ^ 2) / 2) / (2 * Real.pi) ^ d

/-- PDF p.10, (25): canonical heat flow, including t=0. -/
def gaussianHeatFlow {d : ℕ} (t : ℝ) (X : CompletedOperator (NumberLabels d)) : CompletedOperator (NumberLabels d) :=
  hybridConvolution (standardGaussian d) t X

/-- PDF pp.14–15, (43): Gaussian convolution of variance s; s=0 is the identity. -/
def classicalHeat {d : ℕ} (s : ℝ) (f : InterleavedPhaseVector d → ℝ) : InterleavedPhaseVector d → ℝ :=
  if s = 0 then f else fun x => ∫ y, f y *
    (Real.exp (-(∑ j, (x j - y j) ^ 2) / (2 * s)) / (2 * Real.pi * s) ^ d)

example {d : ℕ} (f : InterleavedPhaseVector d → ℝ) (X : CompletedOperator (NumberLabels d)) : hybridConvolution f 0 X = X := by
  simp [hybridConvolution]

example {d : ℕ} (f : InterleavedPhaseVector d → ℝ) : classicalHeat 0 f = f := by
  simp [classicalHeat]

/-- PDF p.20, Definition 3: computed decreasing-eigenvalue Fock rearrangement. -/
def passive (X : B.FockOperator) : B.FockOperator :=
  B.operatorOfMatrix (fun m n => if m = n then (C.eigenvalue X n : ℂ) else 0)

/-- PDF p.21, Lemma 7: extended expectation, even when the mean is infinite. -/
def photonMeanExtended (X : B.FockOperator) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (X (B.fockKet n) n).re

/-- Used only with finite entropy established in the Gaussian conclusions. -/
def entropyReal (X : B.FockOperator) : ℝ := (C.fockEntropyNats X).toReal

/-- PDF p.14, (42), in one mode, on the finite-entropy domain certified below. -/
def thermalEntropyPower (X : B.FockOperator) : ℝ := Real.exp (entropyReal X)

/-- PDF p.18, (52): canonical attenuator, transmissivity exp(-t), vacuum environment.
This reuses the accepted full Fock thermal-channel dilation. -/
def attenuator (t : ℝ) (X : B.FockOperator) : B.FockOperator := C.thermal (Real.exp (-t)) 0 X

/-- PDF pp.23,32, (82): canonical amplifier with gain exp(t). -/
def amplifierFlow (t : ℝ) (X : B.FockOperator) : B.FockOperator :=
  B.operatorOfMatrix (fun m n => ∑' ell : ℕ,
    B.krausTerm (B.amplifierKraus (Real.exp (t / 2)) ell) X (B.fockKet n) m)

/-- Convergence and actual output of the accepted attenuator/thermal dilation. -/
def ThermalChannelRealized (eta n : ℝ) (X : B.FockOperator) : Prop :=
  (∀ m k, Summable (C.thermalTerm eta n X m k)) ∧
    B.HasFockMatrix (C.thermal eta n X) (C.thermalOutputMatrix eta n X) ∧
    B.IsDensity (C.thermal eta n X)

/-- Convergence and actual amplifier output; no unsupported sum/default value. -/
def AmplifierOutputRealized (t : ℝ) (X : B.FockOperator) : Prop :=
  B.AmplifierRealized (Real.exp (t / 2)) ∧
    (∀ m n, Summable (fun ell : ℕ =>
      B.krausTerm (B.amplifierKraus (Real.exp (t / 2)) ell) X (B.fockKet n) m)) ∧
    B.HasFockMatrix (amplifierFlow t X) (fun m n => ∑' ell : ℕ,
      B.krausTerm (B.amplifierKraus (Real.exp (t / 2)) ell) X (B.fockKet n) m) ∧
    B.IsDensity (amplifierFlow t X)

/-- PDF pp.9–10: single-mode phase-space displacement in the source's normalization. -/
def displaced (v : Fin 2 → ℝ) (X : B.FockOperator) : B.FockOperator :=
  let z : ℂ := -(Real.sqrt Real.pi : ℂ) * ((v 0 : ℂ) + Complex.I * (v 1 : ℂ))
  B.krausTerm (B.displacement z) X

/-- PDF p.10, (25): scalar coefficients of the one-mode Gaussian heat integral. -/
def heatIntegrand (t : ℝ) (X : B.FockOperator) (m n : ℕ) (v : Fin 2 → ℝ) : ℂ :=
  ((Real.exp (-(v 0 ^ 2 + v 1 ^ 2) / 2) / (2 * Real.pi) : ℝ) : ℂ) *
    displaced (Real.sqrt t • v) X (B.fockKet n) m

/-- PDF p.10, (25): single-mode canonical heat, with nonsingular zero time. -/
def heatOne (t : ℝ) (X : B.FockOperator) : B.FockOperator :=
  if t = 0 then X else B.operatorOfMatrix (fun m n => ∫ v, heatIntegrand t X m n v)

/-- Convergence and physical output for the single-mode heat integral. -/
def HeatOneRealized (t : ℝ) (X : B.FockOperator) : Prop :=
  (∀ m n, Integrable (heatIntegrand t X m n)) ∧
    B.HasFockMatrix (heatOne t X) (fun m n => ∫ v, heatIntegrand t X m n v) ∧
    B.IsDensity (heatOne t X)

/-- PDF p.9, (22): coordinate displacement-relative-entropy family. -/
def displacementD (X : B.FockOperator) (j : Fin 2) (s : ℝ) : ℝ≥0∞ :=
  quantumD X (displaced (Pi.single j s) X)

/-- Finite local C2 displacement family. This is a CONCLUSION only for thermal
states below, never an invented input regularity assumption for the all-state nodes. -/
def FiniteDisplacementC2 (X : B.FockOperator) : Prop :=
  ∀ j : Fin 2, (∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, |s| < r → displacementD X j s ≠ ⊤) ∧
    ContDiffAt ℝ 2 (fun s : ℝ => (displacementD X j s).toReal) 0

/-- PDF p.9, (22): trace of the actual displacement Hessian. The thermal theorem
concludes finite local C2 and the actual derivative value, preventing deriv defaults. -/
def fisher (X : B.FockOperator) : ℝ :=
  ∑ j : Fin 2, deriv (deriv (fun s : ℝ => (displacementD X j s).toReal)) 0

/-- PDF pp.4,23: zeta is the fixed generator parameter mu^2-lambda^2. -/
def ouDampingRate (mu lambda : ℝ) : ℝ := mu ^ 2 - lambda ^ 2

/-- PDF pp.4,23: constructed stationary mean occupation. -/
def stationaryMean (mu lambda : ℝ) : ℝ := lambda ^ 2 / ouDampingRate mu lambda

/-- PDF pp.4,23: actual qOU channel as an attenuator with the stationary thermal
environment. Its intensity transmissivity is exp(-(mu^2-lambda^2)t); differentiating
the dilation gives exactly mu^2 L_minus + lambda^2 L_plus, without negative-time maps. -/
def ou (mu lambda t : ℝ) (X : B.FockOperator) : B.FockOperator :=
  C.thermal (Real.exp (-ouDampingRate mu lambda * t)) (stationaryMean mu lambda) X

/-- PDF pp.4,23: fixed point computed from the generator parameters. -/
def stationaryState (mu lambda : ℝ) : B.FockOperator := C.photonMeanThermalState (stationaryMean mu lambda)

/-- PDF pp.4,23: stationarity for the whole semigroup, only at nonnegative times. -/
def Stationary (mu lambda : ℝ) (X : B.FockOperator) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ou mu lambda t X = X

/-- PDF p.31: covariance M=tr(rho {R_j,R_k}), for centered states and [Q,P]=i.
The accepted complex covariance uses C=(Var Q+Var P)/2, B=<a^2>-<a>^2. -/
def quadratureCovariance (X : B.FockOperator) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then
    if i = 0 then 2 * (C.covarianceC X + (C.covarianceB X).re)
    else 2 * (C.covarianceC X - (C.covarianceB X).re)
  else 2 * (C.covarianceB X).im

/-- PDF p.32: the standard one-mode symplectic form. -/
def oneModeSymplecticMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- PDF p.32: both orthogonal and symplectic, without deleting rotations. -/
def OrthogonalSymplectic (O : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  O.transpose * O = 1 ∧ O.transpose * oneModeSymplecticMatrix * O = oneModeSymplecticMatrix

/-- PDF p.32: the squeezing diagonal, z>=1 in the theorem. -/
def squeeze (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![z, z⁻¹]

example (X : B.FockOperator) : heatOne 0 X = X := by simp [heatOne]

example : C.g 0 = 0 := by simp [C.g]

example : squeeze 1 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [squeeze]

end QAlgorithms.Papers.Independent.Next46.P13


