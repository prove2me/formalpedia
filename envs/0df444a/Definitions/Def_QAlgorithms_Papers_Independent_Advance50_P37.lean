-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P37
-- name    : QAlgorithms_Papers_Independent_Advance50_P37
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:37:58.761124+00:00
-- url     : https://prove2.me/theorems/fd5de510-6b93-4bea-9af8-6cd72bfabc6b
-- title:
--   Definitions for Long distance quantum key distribution with continuous variables
-- statement:
--   The objects the formalized statements of *Long distance quantum key distribution with continuous variables* (arXiv:1005.0328) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ModulationSpace`: PDF pp.4--5, Eq.(2): Euclidean R^8, with its l2 norm.
--   - `standardModulationGaussian`: PDF p.5, footnote 4: eight independent centered unit-variance normals.
--   - `sphericalModulation`: PDF pp.4--5: independent Hausdorff surface measure, normalized on S^7(2 alpha). Used as a probability only for alpha>0.
--   - `normalizeModulation`: PDF p.5, footnote 4: radial normalization; Gaussian-null zero input is sent to a specified point of the same sphere.
--   - `modulationAmplitudes`: PDF p.5, Eq.(2): successive real coordinates form complex amplitudes.
--   - `sphericalSchmidtCoefficient`: PDF p.6, Eq.(3): actual diagonal Schmidt coefficient, including the sector multiplicity (k+3 choose 3). No normalization premise is built in.
--   - `virtualCoefficient`: PDF p.6, Eq.(3): coefficients vanish unless Alice and Bob occupations agree.
--   - `entangledSector`: PDF p.6, Eq.(3): finite normalized k-photon sector. Each tuple of total k occurs once in the finite box; the final sum still ranges over every k.
--   - `virtualSummand`: PDF p.6, Eq.(3): weighted Hilbert-space summand.
--   - `virtualDensity`: PDF p.6: rank-one coefficients of the constructed resource; square summability and normalization are conclusions below.
--   - `sphericalBobMarginal`: PDF p.6: Bob's actual partial trace. Convergence is concluded below.
--   - `sphereCoherentDensity`: PDF pp.5--6: the four coherent states of Eq.(2), using accepted full-Fock coherent product coefficients.
--   - `SphericalSteeringPOVM`: PDF p.6: Borel-outcome POVM on Alice's completed four-mode space. Bounded effects are positive, normalized and weakly countably additive. No desired resource, steering or outcome-law property is assumed.
--   - `steeredBobKernel`: PDF p.6: unnormalized Bob density after Alice's effect. The entry E[d,b] follows Tr_A[(E tensor I)|Psi><Psi|].
--   - `steeringEventProbability`: PDF p.6: actual event probability by tracing the unnormalized kernel; diagonal summability is a conclusion, not a hidden assumption.
--   - `binaryDisplacementChannel`: PDF p.11: equally weighted real displacement conjugations +a and -a.
--   - `fairNoiseCoin`: PDF p.11: fixed independent fair noise coin in the explicit dilation.
--   - `controlledDisplacementKernel`: PDF p.11: actual controlled-displacement coefficients.
--   - `carrierWeylWithCoin`: PDF p.11, Eq.(5): input Weyl observable, with identity on the coin.
--   - `noisyCarrierWeyl`: PDF p.11, Eq.(5): Heisenberg output Weyl observable. Independent noise has B_Q equal to plus or minus sqrt(2)a, B_P=0 in accepted hbar=1 coordinates, equivalently source B_X equal to plus or minus 2a, B_P=0. This states more than a fitted covariance.
--   - `binaryNoiseCovariance`: PDF p.11: added full-anticommutator covariance, equal numerically to source shot-noise covariance: Var(B_X)=4a^2, Var(B_P)=0.
-- source:
--   Long distance quantum key distribution with continuous variables, arXiv:1005.0328v3, https://arxiv.org/abs/1005.0328v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

/-!
Leverrier--Grangier, arXiv:1005.0328v3, PDF pp.4--6,11.
Full oscillator spaces, no photon cutoff. Vacuum covariance is I. The accepted
hbar=1 full-anticommutator covariance equals the source's hbar=2 covariance;
physical means differ by sqrt(2). No use of the inconsistent printed Eq.(4)
or the defective Claimed50.P47.HasBipartiteMoments predicate is made.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P37

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Gap48.P26 (totalPhotons)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsBarycenter IsTraceClassChannel productCoeff)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov standardFormCovariance vacuumKernel productWeyl weylArgument)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation partialRight)
open QAlgorithms.Papers.Independent.Support50.P14 (CompleteMoments GaussianAt)
open QAlgorithms.Papers.Independent.Renew46.P39 (squeezedVacuum)
open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProductCoefficient NormalizedCoherent)

/-- PDF pp.4--5, Eq.(2): Euclidean R^8, with its l2 norm. -/
abbrev ModulationSpace := EuclideanSpace ℝ (Fin 8)

/-- PDF p.5, footnote 4: eight independent centered unit-variance normals. -/
def standardModulationGaussian : Measure ModulationSpace :=
  Measure.map (WithLp.equiv 2 (Fin 8 → ℝ)).symm
    (Measure.pi (fun _ : Fin 8 => ProbabilityTheory.gaussianReal 0 1))

/-- PDF pp.4--5: independent Hausdorff surface measure, normalized on
S^7(2 alpha). Used as a probability only for alpha>0. -/
def sphericalModulation (alpha : ℝ) : Measure ModulationSpace :=
  let surface : Measure ModulationSpace := Measure.hausdorffMeasure 7
  (surface (Metric.sphere 0 (2 * alpha)))⁻¹ •
    surface.restrict (Metric.sphere 0 (2 * alpha))

/-- PDF p.5, footnote 4: radial normalization; Gaussian-null zero input is
sent to a specified point of the same sphere. -/
def normalizeModulation (alpha : ℝ) (x : ModulationSpace) : ModulationSpace :=
  if x = 0 then EuclideanSpace.single 0 (2 * alpha)
  else (2 * alpha / ‖x‖) • x

/-- PDF p.5, Eq.(2): successive real coordinates form complex amplitudes. -/
def modulationAmplitudes (x : ModulationSpace) : Fin 4 → ℂ :=
  fun j => (x ⟨2 * j.val, by omega⟩ : ℂ) +
    Complex.I * (x ⟨2 * j.val + 1, by omega⟩ : ℂ)

/-- PDF p.6, Eq.(3): actual diagonal Schmidt coefficient, including the
sector multiplicity (k+3 choose 3). No normalization premise is built in. -/
def sphericalSchmidtCoefficient (alpha : ℝ) (n : FockIndex 4) : ℝ :=
  Real.exp (-2 * alpha ^ 2) * (2 * alpha) ^ totalPhotons n /
    (Real.sqrt (Nat.factorial (totalPhotons n) : ℝ) *
      Real.sqrt (Nat.choose (totalPhotons n + 3) 3 : ℝ))

/-- PDF p.6, Eq.(3): coefficients vanish unless Alice and Bob occupations agree. -/
def virtualCoefficient (alpha : ℝ) (n : (Fin 4 ⊕ Fin 4) → ℕ) : ℂ :=
  if n ∘ Sum.inl = n ∘ Sum.inr then
    (sphericalSchmidtCoefficient alpha (n ∘ Sum.inl) : ℂ) else 0

/-- PDF p.6, Eq.(3): finite normalized k-photon sector. Each tuple of total
k occurs once in the finite box; the final sum still ranges over every k. -/
def entangledSector (k : ℕ) : Hilbert ((Fin 4 ⊕ Fin 4) → ℕ) :=
  (Real.sqrt (Nat.choose (k + 3) 3 : ℝ) : ℂ)⁻¹ •
    ∑ n : Fin 4 → Fin (k + 1),
      if (∑ j, (n j).val) = k then
        lp.single 2 (Sum.elim (fun j => (n j).val) (fun j => (n j).val)) 1
      else 0

/-- PDF p.6, Eq.(3): weighted Hilbert-space summand. -/
def virtualSummand (alpha : ℝ) (k : ℕ) : Hilbert ((Fin 4 ⊕ Fin 4) → ℕ) :=
  (Real.exp (-2 * alpha ^ 2) * (2 * alpha) ^ k /
    Real.sqrt (Nat.factorial k : ℝ) : ℂ) • entangledSector k

/-- PDF p.6: rank-one coefficients of the constructed resource;
square summability and normalization are conclusions below. -/
def virtualDensity (alpha : ℝ) : Matrix ((Fin 4 ⊕ Fin 4) → ℕ) ((Fin 4 ⊕ Fin 4) → ℕ) ℂ :=
  fun i j => virtualCoefficient alpha i * star (virtualCoefficient alpha j)

/-- PDF p.6: Bob's actual partial trace. Convergence is concluded below. -/
def sphericalBobMarginal (alpha : ℝ) : DensityKernel 4 :=
  fun b d => ∑' a : FockIndex 4,
    virtualDensity alpha (Sum.elim a b) (Sum.elim a d)

/-- PDF pp.5--6: the four coherent states of Eq.(2), using accepted full-Fock
coherent product coefficients. -/
def sphereCoherentDensity (x : ModulationSpace) : DensityKernel 4 :=
  fun i j => coherentProductCoefficient (modulationAmplitudes x) i *
    star (coherentProductCoefficient (modulationAmplitudes x) j)

/-- PDF p.6: Borel-outcome POVM on Alice's completed four-mode space.
Bounded effects are positive, normalized and weakly countably additive.
No desired resource, steering or outcome-law property is assumed. -/
structure SphericalSteeringPOVM where
  effect : Set ModulationSpace →
    (Hilbert (FockIndex 4) →L[ℂ] Hilbert (FockIndex 4))
  empty : effect ∅ = 0
  total : effect Set.univ = 1
  positive : ∀ S, MeasurableSet S → ∀ v : Hilbert (FockIndex 4),
    (inner (𝕜 := ℂ) v (effect S v)).im = 0 ∧
    0 ≤ (inner (𝕜 := ℂ) v (effect S v)).re
  additive : ∀ S : ℕ → Set ModulationSpace,
    (∀ n, MeasurableSet (S n)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
    ∀ u v : Hilbert (FockIndex 4),
      HasSum (fun n => inner (𝕜 := ℂ) u (effect (S n) v))
        (inner (𝕜 := ℂ) u (effect (⋃ n, S n) v))

/-- PDF p.6: unnormalized Bob density after Alice's effect.
The entry E[d,b] follows Tr_A[(E tensor I)|Psi><Psi|]. -/
def steeredBobKernel (alpha : ℝ) (M : SphericalSteeringPOVM)
    (S : Set ModulationSpace) : DensityKernel 4 :=
  fun b d => (sphericalSchmidtCoefficient alpha b : ℂ) *
    star (sphericalSchmidtCoefficient alpha d : ℂ) *
    (M.effect S (lp.single 2 b 1)) d

/-- PDF p.6: actual event probability by tracing the unnormalized kernel;
diagonal summability is a conclusion, not a hidden assumption. -/
def steeringEventProbability (alpha : ℝ) (M : SphericalSteeringPOVM)
    (S : Set ModulationSpace) : ℝ :=
  ∑' b, (steeredBobKernel alpha M S b b).re

/-- PDF p.11: equally weighted real displacement conjugations +a and -a. -/
def binaryDisplacementChannel (a : ℝ) (rho : DensityKernel 1) : DensityKernel 1 :=
  (1 / 2 : ℂ) •
    (conjugateKernel (productWeyl (fun _ : Fin 1 => (a : ℂ))) rho +
      conjugateKernel (productWeyl (fun _ : Fin 1 => (-a : ℂ))) rho)

/-- PDF p.11: fixed independent fair noise coin in the explicit dilation. -/
def fairNoiseCoin : Matrix Bool Bool ℂ :=
  fun b c => if b = c then (1 / 2 : ℂ) else 0

/-- PDF p.11: actual controlled-displacement coefficients. -/
def controlledDisplacementKernel (a : ℝ) :
    Matrix (FockIndex 1 × Bool) (FockIndex 1 × Bool) ℂ :=
  fun i j => if i.2 = j.2 then
    productWeyl (fun _ : Fin 1 => ((if i.2 then a else -a : ℝ) : ℂ)) i.1 j.1 else 0

/-- PDF p.11, Eq.(5): input Weyl observable, with identity on the coin. -/
def carrierWeylWithCoin (v : (Fin 1 × Fin 2) → ℝ) :
    Matrix (FockIndex 1 × Bool) (FockIndex 1 × Bool) ℂ :=
  fun i j => if i.2 = j.2 then productWeyl (weylArgument v) i.1 j.1 else 0

/-- PDF p.11, Eq.(5): Heisenberg output Weyl observable. Independent noise
has B_Q equal to plus or minus sqrt(2)a, B_P=0 in accepted hbar=1 coordinates, equivalently
source B_X equal to plus or minus 2a, B_P=0. This states more than a fitted covariance. -/
def noisyCarrierWeyl (a : ℝ) (v : (Fin 1 × Fin 2) → ℝ) :
    Matrix (FockIndex 1 × Bool) (FockIndex 1 × Bool) ℂ :=
  fun i j => if i.2 = j.2 then
    Complex.exp (Complex.I *
      ((Real.sqrt 2 * (if i.2 then a else -a) * v (0, 0) : ℝ) : ℂ)) *
        productWeyl (weylArgument v) i.1 j.1 else 0

/-- PDF p.11: added full-anticommutator covariance, equal numerically to
source shot-noise covariance: Var(B_X)=4a^2, Var(B_P)=0. -/
def binaryNoiseCovariance (a : ℝ) : Cov 1 :=
  Matrix.diagonal (fun i => if i.2 = 0 then 4 * a ^ 2 else 0)

/-! Definition sanity checks, not proofs of the source results. -/

example (alpha : ℝ) : normalizeModulation alpha 0 =
    EuclideanSpace.single 0 (2 * alpha) := by simp [normalizeModulation]

example : modulationAmplitudes 0 = 0 := by
  funext j
  simp [modulationAmplitudes]

example (alpha : ℝ) : sphericalSchmidtCoefficient alpha (fun _ => 0) =
    Real.exp (-2 * alpha ^ 2) := by
  simp [sphericalSchmidtCoefficient, totalPhotons]

example (alpha : ℝ) : virtualCoefficient alpha (fun _ => 0) =
    (Real.exp (-2 * alpha ^ 2) : ℂ) := by
  simp [virtualCoefficient, Function.comp_def, sphericalSchmidtCoefficient, totalPhotons]

example (alpha : ℝ) (M : SphericalSteeringPOVM) :
    steeredBobKernel alpha M ∅ = 0 := by
  funext b d
  simp [steeredBobKernel, M.empty]

example : fairNoiseCoin true false = 0 := by simp [fairNoiseCoin]

example (a : ℝ) : binaryNoiseCovariance a (0, 0) (0, 0) = 4 * a ^ 2 := by
  simp [binaryNoiseCovariance]

example (a : ℝ) : binaryNoiseCovariance a (0, 1) (0, 1) = 0 := by
  norm_num [binaryNoiseCovariance]

end QAlgorithms.Papers.Independent.Advance50.P37


