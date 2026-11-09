-- Prove2me | Definitions.Def_HitRunGaps_Spectral_Samplers
-- name    : HitRunGaps_Spectral_Samplers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:13:43.934944+00:00
-- url     : https://prove2.me/theorems/300eb7c8-3bc9-49ad-9e3a-a8c69c5b4ee9
-- title:
--   Continuous chord Dirichlet forms and spectral gaps
-- statement:
--   Let $K\subset\mathbb R^n$ carry its normalized uniform law $\pi$. Use the published normalized sphere law $\sigma$ and uniform one-dimensional chord law $P_\theta(x,dy)$. For a fixed orthonormal basis $b=(b_i)$, the two Dirichlet forms are
--
--   $$\mathcal E_{HR}(f,f)=\frac12\int\!\int\!\int(f(x)-f(y))^2P_\theta(x,dy)\pi(dx)\sigma(d\theta),$$
--   $$\mathcal E_{CHAR}(f,f)=\frac1{2n}\sum_i\int\!\int(f(x)-f(y))^2P_{b_i}(x,dy)\pi(dx).$$
--
--   Each spectral gap is the Rayleigh infimum over every nonzero centered $L^2(\pi)$ class. The jump formula agrees with the source's $\langle f,(I-P)f\rangle_\pi$ by reversibility; neither chain has an added laziness factor. Extended nonnegative integration retains infinite energies instead of replacing nonintegrable functions by zero. The covariance norm uses the published centered covariance operator. These definitions attach the statements to the actual continuous samplers.
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, pp.2,4–7,13, algorithms and §1.2.1

import Definitions.Def_HitRunGaps_Spectral_Constants
import Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

/-- The continuous uniform target. PDF p.4. -/
def uniform {n : ℕ} (K : Set (Space n)) : Measure (Space n) :=
  (volume K)⁻¹ • volume.restrict K

/-- Nonnegative jump expression for the reversible chord Dirichlet form:
½∫∫(f(x)-f(y))² Pθ(x,dy)π(dx). PDF pp.5,7. -/
def chordForm {n : ℕ} (K : Set (Space n)) (θ : Space n) (f : Space n → ℝ) : ENNReal :=
  (2 : ENNReal)⁻¹ * ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2)
    ∂SmithHitAndRun.RandomDir.lineUniform K x θ ∂uniform K

def hitRunForm {n : ℕ} (K : Set (Space n)) (f : Space n → ℝ) : ENNReal :=
  ∫⁻ θ, chordForm K θ f ∂SmithHitAndRun.RandomDir.sphereUniform n

def coordinateForm {n : ℕ} (K : Set (Space n))
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (f : Space n → ℝ) : ENNReal :=
  (n : ENNReal)⁻¹ * ∑ i, chordForm K (b i) f

/-- Generic continuous reversible Rayleigh infimum; the two instantiated forms above are
computed from actual chords. Centering, L² and nonzeroness use π, not ambient volume. -/
def gap {n : ℕ} (K : Set (Space n)) (form : (Space n → ℝ) → ENNReal) : ENNReal :=
  ⨅ (f : Lp ℝ 2 (uniform K)) (_ : (∫ x, f x ∂uniform K) = 0) (_ : f ≠ 0),
    form f / ENNReal.ofReal (‖f‖ ^ 2)

def hitRunGap {n : ℕ} (K : Set (Space n)) : ENNReal := gap K (hitRunForm K)

def coordinateGap {n : ℕ} (K : Set (Space n))
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) : ENNReal := gap K (coordinateForm K b)

def covarianceNorm {n : ℕ} (K : Set (Space n)) : ENNReal :=
  ENNReal.ofReal ‖FunctionalInequalities.Covariance.operator (uniform K)‖

end HitRunGaps.Spectral


