-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22
-- name    : QAlgorithms_Papers_Independent_Advance50_P22
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:05:23.927905+00:00
-- url     : https://prove2.me/theorems/beb258f5-9968-41a1-abbe-50fbf08d2405
-- title:
--   Definitions for The multi-mode quantum Entropy Power Inequality
-- statement:
--   The objects the formalized statements of *The multi-mode quantum Entropy Power Inequality* (arXiv:1408.6410) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `InterleavedCoordinateVector`: PDF p.2, (5): real interleaved displacement coordinates.
--   - `JointIndex`: PDF p.2, (7): completed tensor-product number basis of K n-mode systems.
--   - `independentInput`: PDF p.2: independent subsystems, allowing all correlations within a subsystem.
--   - `subsystemWeylTrace`: PDF pp.2,4, (25): full joint characteristic trace, not just first moments.
--   - `Scattering`: PDF pp.2,4, (7),(8),(26): the exact noiseless Gaussian scattering channel. The CPTP map acts on the entire joint trace class, including correlated inputs. Its complete Weyl action, together with the CCR constraint, specifies the actual Gaussian channel equivalently to the scattering dilation, not merely its means. No energy preservation, gauge symmetry, or invertibility of individual blocks.
--   - `determinantWeight`: PDF p.3, (9): absolute determinant weight; singular blocks have weight zero.
--   - `inputNoise`: PDF p.3, (12): inverses are evaluated only for nonsingular blocks.
--   - `translateDensity`: PDF p.3, (13): D_x=exp(i x^T Delta^{-1} R), with physical mean shift +x. The coherent amplitude is (x_Q+i x_P)/sqrt(2).
--   - `anisotropicHeat`: PDF pp.3,5, (11)--(14): the additive-noise semigroup itself, as a convergent Gaussian average of displacement conjugations. Used only for positive-definite gamma or gamma=0, exactly the input/output noises occurring in this paper. At t=0 or gamma=0 it is the identity. The classical displacement covariance is t*gamma/2, hence the quantum full-anticommutator covariance increment is t*gamma.
--   - `displacementDivergence`: PDF p.4, (19): the displacement relative-entropy function, extended-valued.
--   - `MatrixFisherRegular`: PDF p.4, (19): finite neighborhood and genuine twice Frechet differentiability. No default derivative or conversion of infinite relative entropy is accepted.
--   - `matrixFisher`: PDF p.4, (19): the entire displacement Hessian on MatrixFisherRegular.
--   - `evolvedInputEntropyNats`: PDF p.3, (15): real finite-entropy input along its explicitly defined flow.
--   - `EntropyClocks`: PDF p.3, (15): the clock equations, including the right derivative at zero. Existence, time divergence, and lower bounds are conclusions, not fields here.
--   - `outputTime`: PDF p.4, (17): local output time, including the all-zero-weight case.
--   - `evolvedInputs`: PDF pp.3--4: actual independent evolved inputs at arbitrary local times.
--   - `scatteringEntropyPowerRatio`: PDF p.3, (10): finite-entropy rate evaluated on the physical output state.
--   - `generalizedHusimi`: PDF p.5, (30): overlap definition with denominator (2*pi)^n. The seed is the constructed centered Gaussian of physical covariance Gamma.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, https://arxiv.org/abs/1408.6410v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49

/-!
De Palma, Mari, Lloyd and Giovannetti, arXiv:1408.6410v2.
Full completed number-basis spaces; no photon cutoff. Covariances are full
anticommutators with [Q,P]=i, interleaved coordinates, vacuum covariance I.
Accepted paper imports are pinned library modules. All new definitions are local.

Reuse audit: the frozen same-short-name declarations are different interfaces.
Dependency50.P10.Phase is a grouped index, not real interleaved coordinates;
Support50.P29.jointCharacteristic is a reflected bipartite Weyl pairing;
Frontier18.P14.displace acts on two-mode vectors, not n-mode density kernels;
Gap20.P04.inputEntropy is conditional finite-register entropy in bits;
Next46.P27.entropyRate and Gap20.P07.QuantumSource.entropyRate are respectively
an infinitesimal entropy rate and a block-source entropy rate. Distinct local
names below retain this paper's actual formulas; none is an exact reuse.
Printed Eq.(6) omits i. Changed: use [Q,P]=i, as fixed by the physical
uncertainty condition Gamma >= ± i Delta on p.5 and by the Weyl formulas.
Independent moderation of this source correction is pending.
Eq.(20) is explicitly deferred. Source corrections and finite derivative domains
are recorded in the accompanying audit. Compilation is pending batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov PhysicalCovariance FiniteMeanEnergy
   productWeyl weylArgument multimodeWeylTrace)
open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm)
open QAlgorithms.Papers.Independent.Next46.P17
  (bosonicEntropyPower conjugateCoefficient firstMoments quadratureCovariance
   gaussianCoefficient gaussification)
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)

/-- PDF p.2, (5): real interleaved displacement coordinates. -/
abbrev InterleavedCoordinateVector (n : ℕ) := QuadratureIndex n → ℝ

/-- PDF p.2, (7): completed tensor-product number basis of K n-mode systems. -/
abbrev JointIndex (n K : ℕ) := Fin K → FockIndex n

/-- PDF p.2: independent subsystems, allowing all correlations within a subsystem. -/
def independentInput {n K : ℕ} (rho : Fin K → DensityKernel n) :
    Matrix (JointIndex n K) (JointIndex n K) ℂ :=
  fun i j => ∏ a, rho a (i a) (j a)

/-- PDF pp.2,4, (25): full joint characteristic trace, not just first moments. -/
def subsystemWeylTrace {n K : ℕ}
    (X : Matrix (JointIndex n K) (JointIndex n K) ℂ)
    (k : Fin K → InterleavedCoordinateVector n) : ℂ :=
  ∑' i, ∑' j, X i j * ∏ a, productWeyl (weylArgument (k a)) (j a) (i a)

/-- PDF pp.2,4, (7),(8),(26): the exact noiseless Gaussian scattering channel.
The CPTP map acts on the entire joint trace class, including correlated inputs.
Its complete Weyl action, together with the CCR constraint, specifies the actual
Gaussian channel equivalently to the scattering dilation, not merely its means.
No energy preservation, gauge symmetry, or invertibility of individual blocks.
-/
structure Scattering (n K : ℕ) where
  block : Fin K → Cov n
  ccr : (∑ a, block a * interleavedSymplecticForm n * (block a).transpose) =
    interleavedSymplecticForm n
  channel : Matrix (JointIndex n K) (JointIndex n K) ℂ → DensityKernel n
  cptp : IsTraceClassChannel channel
  weyl : ∀ (rho : State (JointIndex n K)) (q : InterleavedCoordinateVector n),
    multimodeWeylTrace (channel rho.coefficients) q =
      subsystemWeylTrace rho.coefficients (fun a => (block a).transpose.mulVec q)

/-- PDF p.3, (9): absolute determinant weight; singular blocks have weight zero. -/
def determinantWeight {n : ℕ} (M : Cov n) : ℝ := |M.det| ^ (1 / (n : ℝ))

/-- PDF p.3, (12): inverses are evaluated only for nonsingular blocks. -/
def inputNoise {n : ℕ} (M : Cov n) : Cov n :=
  if M.det = 0 then 0 else determinantWeight M • (M⁻¹ * (M⁻¹).transpose)

/-- PDF p.3, (13): D_x=exp(i x^T Delta^{-1} R), with physical mean shift +x.
The coherent amplitude is (x_Q+i x_P)/sqrt(2). -/
def translateDensity {n : ℕ} (x : InterleavedCoordinateVector n) (rho : DensityKernel n) : DensityKernel n :=
  conjugateCoefficient
    (productWeyl (fun j => ((x (j, 0) : ℂ) + Complex.I * (x (j, 1) : ℂ)) /
      (Real.sqrt 2 : ℂ))) rho

/-- PDF pp.3,5, (11)--(14): the additive-noise semigroup itself, as a convergent
Gaussian average of displacement conjugations. Used only for positive-definite
gamma or gamma=0, exactly the input/output noises occurring in this paper.
At t=0 or gamma=0 it is the identity. The classical displacement covariance is
t*gamma/2, hence the quantum full-anticommutator covariance increment is t*gamma.
-/
def anisotropicHeat {n : ℕ} (gamma : Cov n) (t : ℝ)
    (rho : DensityKernel n) : DensityKernel n :=
  if 0 < t ∧ gamma.PosDef then fun i j =>
    ∫ x : InterleavedCoordinateVector n,
      (((Real.pi * t) ^ n * Real.sqrt gamma.det)⁻¹ *
        Real.exp (-(∑ r, ∑ s, x r * gamma⁻¹ r s * x s) / t) : ℝ) •
          translateDensity x rho i j
  else rho

/-- PDF p.4, (19): the displacement relative-entropy function, extended-valued. -/
def displacementDivergence {n : ℕ} (rho : DensityKernel n) (x : InterleavedCoordinateVector n) : ℝ≥0∞ :=
  extendedRelativeEntropyNats rho (translateDensity x rho)

/-- PDF p.4, (19): finite neighborhood and genuine twice Frechet differentiability.
No default derivative or conversion of infinite relative entropy is accepted. -/
def MatrixFisherRegular {n : ℕ} (rho : DensityKernel n) : Prop :=
  (∀ᶠ x in 𝓝 (0 : InterleavedCoordinateVector n), displacementDivergence rho x ≠ ⊤) ∧
  (∀ᶠ x in 𝓝 (0 : InterleavedCoordinateVector n),
    DifferentiableAt ℝ (fun y => (displacementDivergence rho y).toReal) x) ∧
  DifferentiableAt ℝ
    (fderiv ℝ (fun y => (displacementDivergence rho y).toReal)) (0 : InterleavedCoordinateVector n)

/-- PDF p.4, (19): the entire displacement Hessian on MatrixFisherRegular. -/
def matrixFisher {n : ℕ} (rho : DensityKernel n) : Cov n :=
  fun i j => fderiv ℝ
    (fderiv ℝ (fun y => (displacementDivergence rho y).toReal)) (0 : InterleavedCoordinateVector n)
      (Pi.single i 1) (Pi.single j 1)

/-- PDF p.3, (15): real finite-entropy input along its explicitly defined flow. -/
def evolvedInputEntropyNats {n K : ℕ} (M : Fin K → Cov n)
    (rho : Fin K → DensityKernel n) (a : Fin K) (t : ℝ) : ℝ :=
  (extendedEntropyNats (anisotropicHeat (inputNoise (M a)) t (rho a))).toReal

/-- PDF p.3, (15): the clock equations, including the right derivative at zero.
Existence, time divergence, and lower bounds are conclusions, not fields here. -/
def EntropyClocks {n K : ℕ} (M : Fin K → Cov n)
    (rho : Fin K → DensityKernel n) (clock : Fin K → ℝ → ℝ) : Prop :=
  ∀ a, clock a 0 = 0 ∧ ∀ tau : ℝ, 0 ≤ tau →
    0 ≤ clock a tau ∧ HasDerivWithinAt (clock a)
      (Real.exp (evolvedInputEntropyNats M rho a (clock a tau) / (n : ℝ))) (Set.Ici 0) tau

/-- PDF p.4, (17): local output time, including the all-zero-weight case. -/
def outputTime {n K : ℕ} (M : Fin K → Cov n) (times : Fin K → ℝ) : ℝ :=
  ∑ a, determinantWeight (M a) * times a

/-- PDF pp.3--4: actual independent evolved inputs at arbitrary local times. -/
def evolvedInputs {n K : ℕ} (M : Fin K → Cov n)
    (rho : Fin K → DensityKernel n) (times : Fin K → ℝ) : Fin K → DensityKernel n :=
  fun a => anisotropicHeat (inputNoise (M a)) (times a) (rho a)

/-- PDF p.3, (10): finite-entropy rate evaluated on the physical output state. -/
def scatteringEntropyPowerRatio {n K : ℕ} (C : Scattering n K)
    (rho : Fin K → DensityKernel n) (times : Fin K → ℝ) : ℝ :=
  (∑ a, determinantWeight (C.block a) *
    Real.exp (evolvedInputEntropyNats C.block rho a (times a) / (n : ℝ))) /
  Real.exp ((extendedEntropyNats
    (C.channel (independentInput (evolvedInputs C.block rho times)))).toReal / (n : ℝ))

/-- PDF p.5, (30): overlap definition with denominator (2*pi)^n.
The seed is the constructed centered Gaussian of physical covariance Gamma. -/
def generalizedHusimi {n : ℕ} (Gamma : Cov n) (rho : DensityKernel n)
    (x : InterleavedCoordinateVector n) : ℝ :=
  ((2 * Real.pi) ^ n)⁻¹ *
    (∑' i, ∑' j, rho i j * translateDensity x (gaussianCoefficient Gamma 0) j i).re

example {n : ℕ} (rho : DensityKernel n) (i j : FockIndex n) :
    independentInput (fun _ : Fin 1 => rho) (fun _ => i) (fun _ => j) = rho i j := by
  simp [independentInput, Fin.prod_univ_succ]

example {n : ℕ} (rho : DensityKernel n) (h : MatrixFisherRegular rho) :
    ∀ᶠ x in 𝓝 (0 : InterleavedCoordinateVector n), displacementDivergence rho x ≠ ⊤ := h.1

example {n : ℕ} (Gamma : Cov n) (x : InterleavedCoordinateVector n) :
    generalizedHusimi Gamma (0 : DensityKernel n) x = 0 := by
  simp [generalizedHusimi]

example {n : ℕ} (M : Cov n) (h : M.det = 0) : inputNoise M = 0 := by
  simp [inputNoise, h]

example {n : ℕ} (rho : DensityKernel n) (gamma : Cov n) :
    anisotropicHeat gamma 0 rho = rho := by simp [anisotropicHeat]

example {n : ℕ} (rho : DensityKernel n) (gamma : Cov n) (t : ℝ)
    (h : ¬ gamma.PosDef) : anisotropicHeat gamma t rho = rho := by
  simp [anisotropicHeat, h]

example {n K : ℕ} (M : Fin K → Cov n) : outputTime M 0 = 0 := by
  simp [outputTime]

example : symplecticEntropy 1 = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P49.symplecticEntropy,
    QAlgorithms.Papers.Independent.Information100.P49.thermalEntropy]

end QAlgorithms.Papers.Independent.Advance50.P22


