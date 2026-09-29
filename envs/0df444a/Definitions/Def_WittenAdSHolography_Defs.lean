-- Prove2me | Definitions.Def_WittenAdSHolography_Defs
-- name    : WittenAdSHolography_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T00:23:09.099747+00:00
-- url     : https://prove2.me/theorems/7a32bf36-b65c-4114-86bc-633e26ab871e
-- title:
--   Upper half-space model of Euclidean $\mathrm{AdS}_{d+1}$: hyperbolic Laplacian, massive solutions, kernel $K_\Delta$
-- statement:
--   Definitions for the upper half space model of Euclidean $\mathrm{AdS}_{d+1}$ used throughout Witten's Section 2.
--
--   1. $\mathrm{Bdry}\,d=\mathbb R^d$ (Euclidean space) is the boundary; a function on the bulk is written $u(x_0,x)$ with $x_0\in\mathbb R$, $x\in\mathbb R^d$.
--   2. $\partial_0u$ and $\partial_ju$ are the partial derivatives in $x_0$ and in the $j$-th boundary coordinate.
--   3. The **hyperbolic Laplacian** of the metric $x_0^{-2}(dx_0^2+\sum_i dx_i^2)$ (eq. (2.15)) is
--   $$\Delta_gu=x_0^2\Big(\partial_0^2u+\sum_{j=1}^d\partial_j^2u\Big)-(d-1)\,x_0\,\partial_0u .$$
--   4. $u$ is a **massive solution** with squared mass $m^2\in\mathbb R$ if $u$ is $C^2$ on $\{x_0>0\}$ and $\Delta_gu=m^2u$ there (eqs. (2.34), (2.37)).
--   5. The **conformal dimension** is $\Delta(d,m^2)=\tfrac12\big(d+\sqrt{d^2+4m^2}\big)$ (eq. (2.44)).
--   6. The **bulk-to-boundary kernel** is $K_\Delta(x_0,x)=x_0^{\Delta}/(x_0^2+|x|^2)^{\Delta}$ (eqs. (2.19), (2.38)).
--   7. The **Poisson-type integral** is $P_\Delta[\varphi_0](x_0,x)=\int_{\mathbb R^d}K_\Delta(x_0,x-x')\varphi_0(x')\,dx'$ (eqs. (2.20), (2.41)), without normalising constant.
--
--   These are the objects in terms of which the goal and all milestones of the mission are stated.
--
--   **Formalization Note** Partial derivatives are one-variable `deriv`s (which return $0$ at non-differentiable points), which is why the solution predicate also requires $C^2$ regularity. Powers are real powers (`Real.rpow`), and $\sqrt{\cdot}$ is `Real.sqrt`, which returns $0$ on negative inputs. The integral is the Bochner integral for Lebesgue measure and equals $0$ when the integrand is not integrable.
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, Section 2 (eqs. (2.15), (2.19)-(2.20), (2.34), (2.37)-(2.38), (2.41), (2.44))

import Mathlib

/-!
# Witten, *Anti de Sitter space and holography* (hep-th/9802150) — definitions

Upper half space model of Euclidean `AdS_{d+1}` (= hyperbolic space `H^{d+1}`):
points `(x₀, x)` with `x₀ > 0`, `x ∈ ℝ^d`, metric `ds² = x₀⁻² (dx₀² + Σ dxᵢ²)` (eq. (2.15)).
-/

namespace WittenAdSHolography

open MeasureTheory

/-- The boundary `ℝ^d` of the upper half space model, with its Euclidean norm. -/
abbrev Bdry (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Partial derivative `∂u/∂x₀` of a function `u(x₀, x)`. -/
noncomputable def d0 {d : ℕ} (u : ℝ → Bdry d → ℝ) (x₀ : ℝ) (x : Bdry d) : ℝ :=
  deriv (fun t => u t x) x₀

/-- Partial derivative `∂u/∂x_j` (`j`-th boundary coordinate) of a function `u(x₀, x)`. -/
noncomputable def dj {d : ℕ} (j : Fin d) (u : ℝ → Bdry d → ℝ) (x₀ : ℝ) (x : Bdry d) : ℝ :=
  deriv (fun s : ℝ => u x₀ (x + s • EuclideanSpace.single j (1 : ℝ))) 0

/-- Laplace–Beltrami operator of the hyperbolic metric `x₀⁻² (dx₀² + Σ dxᵢ²)` on the upper
half space, written out in coordinates:
`Δu = x₀^{d+1} ∂₀(x₀^{1-d} ∂₀u) + x₀² Σⱼ ∂ⱼ²u = x₀² (∂₀²u + Σⱼ ∂ⱼ²u) − (d−1) x₀ ∂₀u`. -/
noncomputable def hypLaplacian {d : ℕ} (u : ℝ → Bdry d → ℝ) (x₀ : ℝ) (x : Bdry d) : ℝ :=
  x₀ ^ 2 * (d0 (d0 u) x₀ x + ∑ j, dj j (dj j u) x₀ x) - ((d : ℝ) - 1) * x₀ * d0 u x₀ x

/-- `u` is a classical solution of the massive scalar wave equation `(−D_iD^i + m²)u = 0`
(eqs. (2.34), (2.37)) on the open upper half space `{x₀ > 0}`: `u` is `C²` there and
`Δu = m² u` pointwise. The squared mass `msq = m²` is an arbitrary real number. -/
def IsMassiveSolution (d : ℕ) (msq : ℝ) (u : ℝ → Bdry d → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun p : ℝ × Bdry d => u p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ∧
    ∀ x₀ : ℝ, 0 < x₀ → ∀ x : Bdry d, hypLaplacian u x₀ x = msq * u x₀ x

/-- The conformal dimension attached to a scalar of squared mass `m²` on `AdS_{d+1}`,
eq. (2.44): `Δ = (d + √(d² + 4m²)) / 2`. -/
noncomputable def confDim (d : ℕ) (msq : ℝ) : ℝ :=
  ((d : ℝ) + Real.sqrt ((d : ℝ) ^ 2 + 4 * msq)) / 2

/-- The bulk-to-boundary Green's function of eq. (2.38) (eq. (2.19) when `Δ = d`):
`K_Δ(x₀, x) = x₀^Δ / (x₀² + |x|²)^Δ` (real powers). -/
noncomputable def bulkKernel {d : ℕ} (Δ : ℝ) (x₀ : ℝ) (x : Bdry d) : ℝ :=
  x₀ ^ Δ / (x₀ ^ 2 + ‖x‖ ^ 2) ^ Δ

/-- The Poisson-type integral of eqs. (2.20), (2.41) (without the normalising constant):
`φ(x₀, x) = ∫_{ℝ^d} K_Δ(x₀, x − x') φ₀(x') dx'` (Lebesgue measure on `ℝ^d`). -/
noncomputable def poissonIntegral {d : ℕ} (Δ : ℝ) (φ₀ : Bdry d → ℝ) (x₀ : ℝ) (x : Bdry d) :
    ℝ :=
  ∫ x', bulkKernel Δ x₀ (x - x') * φ₀ x'

end WittenAdSHolography


