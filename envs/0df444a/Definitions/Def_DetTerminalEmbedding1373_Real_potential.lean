-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_potential
-- name    : DetTerminalEmbedding1373_Real_potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:34.406208+00:00
-- url     : https://prove2.me/theorems/b6546f19-2a41-4e11-b879-a90bb4fba99d
-- title:
--   Gaussian quadratic potentials and unequal-tolerance test budget
-- statement:
--   For a sign matrix $\Sigma$, the projected linear map is $A=\Sigma/\sqrt m$. For a unit vector $v$, the quadratic form uses
--
--   $$B_v=m^{-1}I_m\otimes(vv^\top-\operatorname{diag}(v^2)),\qquad\lambda=\frac{m\delta}{2(1+\delta)}.$$
--
--   A partial sign pattern fixes coordinates to $\pm1$, and the remaining coordinates are independent standard Gaussians. Define
--
--   $$\Psi_v^\pm(\sigma)=\mathbb E\exp(-\lambda\delta\pm\lambda g(\sigma)^\top B_vg(\sigma)),\qquad\Phi=\sum_j(\Psi_j^++\Psi_j^-).$$
--
--   The common test budget is $\sum_j2e^{-m\delta_j^2/8}<1/2$. Expectations take values in the extended nonnegative reals, so divergence cannot produce a spurious zero. These are mathematical analysis objects; neither the machine nor the signing code can call a Gaussian integral evaluator.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 12–14, equations (10), (12)–(14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_geometry

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

noncomputable def signProjection {m d : ℕ} (σ : Fin m → Fin d → Bool) : E d →ₗ[ℝ] E m :=
  Matrix.toEuclideanLin (fun i j => (if σ i j then (1 : ℝ) else -1) / Real.sqrt (m : ℝ))

/-- The quadratic form of (1/m) I_m ⊗ (vvᵀ-diag(v²)), including the essential 1/m. -/
noncomputable def quadratic {m d : ℕ} (v : E d) (g : Fin m × Fin d → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m,
    ((∑ j : Fin d, v j * g (i,j)) ^ 2 - ∑ j : Fin d, (v j) ^ 2 * (g (i,j)) ^ 2)

def fillSigns {m d : ℕ} (σ : Fin m × Fin d → Option Bool)
    (g : Fin m × Fin d → ℝ) (i : Fin m × Fin d) : ℝ :=
  match σ i with | none => g i | some b => if b then 1 else -1

noncomputable def lambda (m : ℕ) (δ : ℝ) : ℝ := (m : ℝ) * δ / (2 * (1 + δ))

/-- Independent standard Gaussians, used in analysis only. -/
noncomputable def gaussianCoordinates (m d : ℕ) : Measure (Fin m × Fin d → ℝ) :=
  Measure.pi (fun _ : Fin m × Fin d => ProbabilityTheory.gaussianReal 0 1)

/-- Equation (14), as an extended nonnegative expectation. A divergent expectation
is infinity, not the Bochner integral's zero default. No integration instruction exists. -/
noncomputable def psi {m d : ℕ} (v : E d) (δ : ℝ)
    (σ : Fin m × Fin d → Option Bool) (positive : Bool) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (Real.exp (-lambda m δ * δ +
    (if positive then lambda m δ else -lambda m δ) * quadratic v (fillSigns σ g)))
    ∂gaussianCoordinates m d

noncomputable def totalPotential {L m d : ℕ} (v : Fin L → E d) (δ : Fin L → ℝ)
    (σ : Fin m × Fin d → Option Bool) : ℝ≥0∞ :=
  ∑ j, (psi (v j) (δ j) σ true + psi (v j) (δ j) σ false)

noncomputable def TestBudget {L : ℕ} (m : ℕ) (δ : Fin L → ℝ) : Prop :=
  (∑ j, 2 * Real.exp (-(m : ℝ) * (δ j) ^ 2 / 8)) < 1 / 2

end DetTerminalEmbedding1373.Real


