-- Prove2me | Definitions.Def_RBMSensitivity_Data_thetaDot
-- name    : RBMSensitivity_Data_thetaDot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:28.649023+00:00
-- url     : https://prove2.me/theorems/5f6c0a90-749c-432f-87ec-127c210ec008
-- title:
--   The averaged derivatives $\theta_t'$
-- statement:
--   For $x\in G$, $\xi=(x,0)$ and $t>0$,
--   $$\frac 1t\int_0^t\mathbb E\big[f'(Z^{\alpha,x}(s))\mathcal J^{\alpha,\xi}(s)\big]\,ds,\qquad\alpha\in U.$$
--   This is the expression for $\theta_t'(\alpha)$ in §9.
--
--   **Formalization Note** $f'(x)y$ is the derivative of $f$ within $G$ at $x$ applied to $y$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §9, p.36

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone_G
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The right side of the display for `θ'_t(α)`: arXiv:1907.00472v2, §9, p.36,
`(1/t) ∫_0^t E[f'(Z^{α,x}(s)) 𝒥^{α,ξ}(s)] ds` with `ξ = (x, 0)`.

**Formalization Note.** `f'(x)y` is `fderivWithin ℝ f G x y`, a real number. It is defined apart from
`deriv (theta …)`, because that these two agree is part of the milestone. -/
noncomputable def Data.thetaDot {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (D : Data J)
    (P : Measure Ω) (Z : ℝ → E J → ℝ≥0 → Ω → E J) (𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J)
    (f : E J → ℝ) (x : E J) (t α : ℝ) : ℝ :=
  (1 / t) * ∫ s in (0 : ℝ)..t,
    ∫ ω, fderivWithin ℝ f D.G (Z α x s.toNNReal ω) (𝒥 α (x, 0) s.toNNReal ω) ∂P

end RBMSensitivity


