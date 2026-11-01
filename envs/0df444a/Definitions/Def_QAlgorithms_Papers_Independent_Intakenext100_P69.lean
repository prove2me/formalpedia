-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P69
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P69
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:36:40.85088+00:00
-- url     : https://prove2.me/theorems/3585b1ef-282b-4e7e-9571-76c9db1edc33
-- title:
--   Definitions for Finite-resource teleportation stretching for continuous-variable systems
-- statement:
--   The objects the formalized statements of *Finite-resource teleportation stretching for continuous-variable systems* (arXiv:1706.06065) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CenteredGaussianAt`: PDF pp.2,8 [59]: centered normalized trace-class Gaussian density with physical covariance V, finite energy, convergent Weyl traces, and real symmetry. The accepted predicate uses doubled covariance (vacuum I), hence 2 times V.
--   - `centeredTwoModeGaussianKernel`: PDF pp.2,4: construct the unique centered Gaussian density from its full Weyl characteristic, using choice only when it exists. Vacuum is an explicit off-domain extension. The comparison theorem CONCLUDES validity at both constructed covariances, so the fallback cannot discharge a physical claim.
--   - `resourceDenominator`: PDF p.2, (10): D before the overall factor 2 in the denominator of b.
--   - `resourceNoise`: PDF p.2, (11), in physical vacuum variance 1/2 units.
--   - `resourceB`: PDF p.2, (10), restricted to D>0 in the theorem.
--   - `resourceA`: PDF p.2, (9), restricted to eta>0 in the theorem.
--   - `resourceC`: PDF p.2, (9): the positive square root of the intensity gain.
--   - `resourceCovariance`: PDF p.2, (8): (q_A,p_A,q_B,p_B), with off-diagonal c diag(1,-1).
--   - `comparisonC`: PDF p.4, (28): comparison correlation computed from this resource.
--   - `comparisonCovariance`: PDF p.4, (28): keep both diagonal blocks, replace only c by c_sep.
--   - `resourceKernel`: PDF p.2, (8)--(11): the actual centered resource density, not its CM.
--   - `comparisonKernel`: PDF p.4, (28): the actual centered comparison density, not a free candidate.
--   - `twoModeSplit`: PDF pp.2,4: relabel full two-mode Fock coordinates as Alice times Bob. Neither occupation number is truncated.
--   - `normalStateRelativeEntropyBits`: PDF p.3: Umegaki relative entropy in bits on actual normal densities. The accepted extended finite-compression definition retains support failures and divergence as infinity; no difference of infinite entropies is taken.
--   - `relativeEntropyEntanglementBits`: PDF pp.3--4, (23),(29): infimum over ALL normalized separable densities, using their full trace-norm closed convex-hull definition, not only Gaussians.
--   - `gaussianComparisonBound`: PDF p.4, (29): Psi is the divergence to the constructed Gaussian candidate.
--   - `additiveComparisonBound`: PDF pp.2,5, (11), eta=1: r=-ln(xi)/2. Used physically for 0<xi<=1.
--   - `additiveChainComparisonBound`: PDF p.6, (39): minimum of the constructed additive-noise comparison values on all N+1 links. The index type is nonempty even when N=0.
-- source:
--   Finite-resource teleportation stretching for continuous-variable systems, arXiv:1706.06065v3, https://arxiv.org/abs/1706.06065v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

/-!
Laurenza--Braunstein--Pirandola, arXiv:1706.06065v3, PDF pp.2--8.
The two statements below are the state comparison (28)--(29) and the algebraic
chain specialization on p.6. Operational capacity/stretching nodes are deferred
in HARD.md/GAPS.json: no finite-dimensional LOCC surrogate is used.
Covariance is in interleaved physical vacuum-I/2 units. Only the adapter to the
accepted characteristic doubles it. All densities have full oscillator support.
No defective Claimed50.P47.HasBipartiteMoments predicate is used.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P69

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance covarianceCharacteristicValue
   multimodeWeylTrace standardFormCovariance vacuumKernel)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsSeparable)
open QAlgorithms.Papers.Independent.Frontier18.P01 (generalizedRelativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,8 [59]: centered normalized trace-class Gaussian density with
physical covariance V, finite energy, convergent Weyl traces, and real symmetry.
The accepted predicate uses doubled covariance (vacuum I), hence 2 times V. -/
def CenteredGaussianAt (V : Cov 2) (rho : DensityKernel 2) : Prop :=
  V.transpose = V ∧ GaussianWithCovariance rho ((2 : ℝ) • V) ∧
    ∀ v, multimodeWeylTrace rho v =
      covarianceCharacteristicValue ((2 : ℝ) • V) 0 v

/-- PDF pp.2,4: construct the unique centered Gaussian density from its full
Weyl characteristic, using choice only when it exists. Vacuum is an explicit
off-domain extension. The comparison theorem CONCLUDES validity at both
constructed covariances, so the fallback cannot discharge a physical claim. -/
def centeredTwoModeGaussianKernel (V : Cov 2) : DensityKernel 2 :=
  if h : ∃ rho : DensityKernel 2, CenteredGaussianAt V rho then
    Classical.choose h
  else vacuumKernel 2

/-- PDF p.2, (10): D before the overall factor 2 in the denominator of b. -/
def resourceDenominator (eta r : ℝ) : ℝ :=
  eta + 1 - Real.exp (2 * r) * |eta - 1|

/-- PDF p.2, (11), in physical vacuum variance 1/2 units. -/
def resourceNoise (eta r : ℝ) : ℝ :=
  Real.exp (-2 * r) * (eta + 1) / 2

/-- PDF p.2, (10), restricted to D>0 in the theorem. -/
def resourceB (eta r : ℝ) : ℝ :=
  (-|eta - 1| + eta * Real.exp (2 * r) + Real.exp (-2 * r)) /
    (2 * resourceDenominator eta r)

/-- PDF p.2, (9), restricted to eta>0 in the theorem. -/
def resourceA (eta r : ℝ) : ℝ :=
  (2 * resourceB eta r + (eta - 1) * Real.exp (-2 * r)) / (2 * eta)

/-- PDF p.2, (9): the positive square root of the intensity gain. -/
def resourceC (eta r : ℝ) : ℝ :=
  (2 * resourceB eta r - Real.exp (-2 * r)) / (2 * Real.sqrt eta)

/-- PDF p.2, (8): (q_A,p_A,q_B,p_B), with off-diagonal c diag(1,-1). -/
def resourceCovariance (eta r : ℝ) : Cov 2 :=
  standardFormCovariance (resourceA eta r) (resourceB eta r)
    (resourceC eta r) (-resourceC eta r)

/-- PDF p.4, (28): comparison correlation computed from this resource. -/
def comparisonC (eta r : ℝ) : ℝ :=
  Real.sqrt ((resourceA eta r - 1 / 2) * (resourceB eta r - 1 / 2))

/-- PDF p.4, (28): keep both diagonal blocks, replace only c by c_sep. -/
def comparisonCovariance (eta r : ℝ) : Cov 2 :=
  standardFormCovariance (resourceA eta r) (resourceB eta r)
    (comparisonC eta r) (-comparisonC eta r)

/-- PDF p.2, (8)--(11): the actual centered resource density, not its CM. -/
def resourceKernel (eta r : ℝ) : DensityKernel 2 :=
  centeredTwoModeGaussianKernel (resourceCovariance eta r)

/-- PDF p.4, (28): the actual centered comparison density, not a free candidate. -/
def comparisonKernel (eta r : ℝ) : DensityKernel 2 :=
  centeredTwoModeGaussianKernel (comparisonCovariance eta r)

/-- PDF pp.2,4: relabel full two-mode Fock coordinates as Alice times Bob.
Neither occupation number is truncated. -/
def twoModeSplit (rho : DensityKernel 2) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun p q => rho (fun i => if i = 0 then p.1 else p.2)
    (fun i => if i = 0 then q.1 else q.2)

/-- PDF p.3: Umegaki relative entropy in bits on actual normal densities.
The accepted extended finite-compression definition retains support failures
and divergence as infinity; no difference of infinite entropies is taken. -/
def normalStateRelativeEntropyBits {I : Type} (rho sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  generalizedRelativeEntropy rho sigma / ENNReal.ofReal (Real.log 2)

/-- PDF pp.3--4, (23),(29): infimum over ALL normalized separable densities,
using their full trace-norm closed convex-hull definition, not only Gaussians. -/
def relativeEntropyEntanglementBits (rho : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) : ℝ≥0∞ :=
  ⨅ sigma : {sigma : State (ℕ × ℕ) // IsSeparable sigma.coefficients},
    normalStateRelativeEntropyBits rho sigma.val.coefficients

/-- PDF p.4, (29): Psi is the divergence to the constructed Gaussian candidate. -/
def gaussianComparisonBound (eta r : ℝ) : ℝ≥0∞ :=
  normalStateRelativeEntropyBits (twoModeSplit (resourceKernel eta r))
    (twoModeSplit (comparisonKernel eta r))

/-- PDF pp.2,5, (11), eta=1: r=-ln(xi)/2. Used physically for 0<xi<=1. -/
def additiveComparisonBound (xi : ℝ) : ℝ≥0∞ :=
  gaussianComparisonBound 1 (-Real.log xi / 2)

/-- PDF p.6, (39): minimum of the constructed additive-noise comparison values
on all N+1 links. The index type is nonempty even when N=0. -/
def additiveChainComparisonBound (N : ℕ) (noise : Fin (N + 1) → ℝ) : ℝ≥0∞ :=
  ⨅ i : Fin (N + 1), additiveComparisonBound (noise i)

/-- Sanity check for p.2, (8): q_A--q_B has sign +c. -/
example (eta r : ℝ) :
    resourceCovariance eta r (0, 0) (1, 0) = resourceC eta r := by
  simp [resourceCovariance, standardFormCovariance]

/-- Sanity check for p.2, (8): p_A--p_B has sign -c. -/
example (eta r : ℝ) :
    resourceCovariance eta r (0, 1) (1, 1) = -resourceC eta r := by
  simp [resourceCovariance, standardFormCovariance]

/-- Sanity check: the fallback is explicit and confined to absent Gaussians. -/
example (V : Cov 2) (h : ¬ ∃ rho, CenteredGaussianAt V rho) :
    centeredTwoModeGaussianKernel V = vacuumKernel 2 := by
  simp [centeredTwoModeGaussianKernel, h]

/-- Sanity check: at eta=1,r=0, the resource is prescribed the vacuum CM I/2. -/
example : resourceA 1 0 = 1 / 2 ∧ resourceB 1 0 = 1 / 2 ∧
    resourceC 1 0 = 0 := by
  norm_num [resourceA, resourceB, resourceC, resourceDenominator]

/-- Sanity check: at xi=1 the additive parametrization has r=0. -/
example : additiveComparisonBound 1 = gaussianComparisonBound 1 0 := by
  simp [additiveComparisonBound]

end QAlgorithms.Papers.Independent.Intakenext100.P69


