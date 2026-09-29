-- Prove2me | Definitions.Def_DualSSD_MeanRisk_gini
-- name    : DualSSD_MeanRisk_gini
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:04:05.15999+00:00
-- url     : https://prove2.me/theorems/3615d6f5-5cbe-4f47-9e7d-96e4e3351b8f
-- title:
--   Mean $\mu_X$, vertical diameter $h_X(p)$ (3.6), Gini mean difference $\Gamma_X$ (3.8), tail Gini $G_X(p)$ (4.8)
-- statement:
--   Let $\mu_X=E X$ be the expected outcome. The **vertical diameter** of the dual dispersion space is
--
--   $$h_X(p)=\mu_Xp-F_X^{(-2)}(p),\qquad p\in[0,1].$$
--
--   The **Gini mean difference** is the doubled area of the dual dispersion space,
--
--   $$\Gamma_X=2\int_0^1\bigl(\mu_Xp-F_X^{(-2)}(p)\bigr)\,dp,$$
--
--   and for $p\in(0,1]$ the **tail Gini measure** is
--
--   $$G_X(p)=\frac{2}{p^2}\int_0^p\bigl(\mu_X\alpha-F_X^{(-2)}(\alpha)\bigr)\,d\alpha.$$
--
--   In particular $\Gamma_X=G_X(1)$, which the file records as a one-line lemma. These are the dual risk measures whose mean–risk models the mission studies.
--
--   **Formalization Note** $\Gamma_X$ is defined by the area formula (3.8), not by the double-integral formula for the Gini mean difference that the paper cites without proof. All integrals are Bochner integrals, used on integrable $X$.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 66 eq. (3.6), p. 67 eq. (3.8), p. 72 eq. (4.8), p. 73 (Γ_X = G_X(1))

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_secondQuantileR

namespace DualSSD.MeanRisk

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected outcome `μ_X = E X` (Ogryczak–Ruszczyński 2002, notation used throughout, e.g.
p. 62). A Bochner integral: every statement using it assumes `X` integrable. -/
noncomputable def mean (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂P

/-- The vertical diameter of the dual dispersion space (3.6) (Ogryczak–Ruszczyński 2002, §3,
p. 66): `h_X(p) = μ_X p − F_X^(−2)(p)`, for `p ∈ [0, 1]`. -/
noncomputable def hDiam (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  mean P X * p - secondQuantileR P X p

/-- The Gini mean difference, defined as the doubled area of the dual dispersion space (3.8)
(Ogryczak–Ruszczyński 2002, §3, p. 67): `Γ_X = 2 ∫_0^1 (μ_X p − F_X^(−2)(p)) dp`. -/
noncomputable def gini (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  2 * ∫ p in (0 : ℝ)..1, (mean P X * p - secondQuantileR P X p)

/-- The tail Gini measure (4.8) (Ogryczak–Ruszczyński 2002, §4, p. 72), for `p ∈ (0, 1]`:
`G_X(p) = (2/p²) ∫_0^p (μ_X α − F_X^(−2)(α)) dα`. -/
noncomputable def tailGini (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  2 / p ^ 2 * ∫ α in (0 : ℝ)..p, (mean P X * α - secondQuantileR P X α)

/-- `Γ_X = G_X(1)` (Ogryczak–Ruszczyński 2002, §5, p. 73), by unfolding (3.8) and (4.8). -/
theorem gini_eq_tailGini_one (P : Measure Ω) (X : Ω → ℝ) : gini P X = tailGini P X 1 := by
  simp [gini, tailGini]

end DualSSD.MeanRisk


