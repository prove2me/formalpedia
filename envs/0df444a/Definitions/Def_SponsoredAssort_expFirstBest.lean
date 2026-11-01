-- Prove2me | Definitions.Def_SponsoredAssort_expFirstBest
-- name    : SponsoredAssort_expFirstBest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:52:40.357009+00:00
-- url     : https://prove2.me/theorems/d6b6c643-bb40-40c5-83b3-897a674a8269
-- title:
--   Expected first-best welfare $\mathbb E_{v\sim F}[R(m^{FB},v)]$
-- statement:
--   For a prior $F$ on $\mathbb R^n_+$, the expected first-best welfare is
--
--   $$
--   \mathbb E_{v\sim F}\big[R(m^{FB},v)\big]=\int \max_{S\subseteq[n]}R(S,v)\,dF(v).
--   $$
--
--   **Formalization Note** A lower Lebesgue integral valued in $[0,\infty]$, as for the expected welfare of a mechanism.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12

import Mathlib
import Definitions.Def_SponsoredAssort_firstBest

open scoped NNReal ENNReal
open MeasureTheory

namespace SponsoredAssort

/-- The **expected first-best welfare** `E_{v∼F}[R(m^FB, v)]` under a prior `F` on `ℝⁿ₊`
(Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12).

**Formalization Note.** A lower Lebesgue integral `∫⁻` of `ENNReal.ofReal R(m^FB, v)`, as for
`expWelfare`. -/
noncomputable def expFirstBest {n : ℕ} (r : Fin n → ℝ) (F : Measure (Attr n)) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (firstBest r v) ∂F

end SponsoredAssort


