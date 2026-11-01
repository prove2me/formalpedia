-- Prove2me | Definitions.Def_SponsoredAssort_worstCaseRatio
-- name    : SponsoredAssort_worstCaseRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:53:46.362875+00:00
-- url     : https://prove2.me/theorems/0b57c645-8256-482e-978f-1a7833056217
-- title:
--   Worst-case ratio $\inf_F \mathbb E_F[R(m,v)]/\mathbb E_F[R(m^{FB},v)]$
-- statement:
--   The prior-independent performance of a mechanism $m$ is its worst ratio to first best over all priors,
--
--   $$
--   \inf_{F\in\mathcal P(\mathbb R^n_+)}\ \frac{\mathbb E_{v\sim F}[R(m,v)]}{\mathbb E_{v\sim F}[R(m^{FB},v)]}.
--   $$
--
--   This is the inner infimum of $\gamma^{PI}(r)$ in Definition 2.2 and the quantity bounded on p.28.
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$ over the probability measures $F$ with nonzero expected first-best welfare. With positive revenues this excludes exactly the point mass at $v=0$, where both expectations vanish and the ratio is $0/0$; without the exclusion the infimum would be $0$ for every mechanism.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12; display, p.28

import Mathlib
import Definitions.Def_SponsoredAssort_expWelfare
import Definitions.Def_SponsoredAssort_expFirstBest

open scoped NNReal ENNReal
open MeasureTheory

namespace SponsoredAssort

/-- The **prior-independent worst-case ratio** of a mechanism `m`,
`inf_{F ∈ P(ℝⁿ₊)} E_{v∼F}[R(m, v)] / E_{v∼F}[R(m^FB, v)]` (Balseiro, Désir, SSRN 3821382
(Feb. 21, 2022), Definition 2.2, p.12, the inner infimum of `γ^PI(r)`; also the display on p.28).

**Formalization Note.** The infimum ranges over all probability measures `F` on `ℝⁿ₊` (Borel
σ-algebra) whose expected first-best welfare is nonzero; the only excluded prior is the point mass
at `v = 0`, where the ratio is `0/0` (with positive revenues `R(m^FB, v) > 0` for every `v ≠ 0`).
Ratios live in `ℝ≥0∞`, so the infimum is well defined; the denominator is finite, because
welfare is bounded by `maxᵢ rᵢ`. -/
noncomputable def worstCaseRatio {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) : ℝ≥0∞ :=
  ⨅ (F : Measure (Attr n)) (_ : IsProbabilityMeasure F) (_ : expFirstBest r F ≠ 0),
    expWelfare r m F / expFirstBest r F

end SponsoredAssort


