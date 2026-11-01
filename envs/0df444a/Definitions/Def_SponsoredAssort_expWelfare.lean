-- Prove2me | Definitions.Def_SponsoredAssort_expWelfare
-- name    : SponsoredAssort_expWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:52:01.750307+00:00
-- url     : https://prove2.me/theorems/88f8c752-b2e2-4914-b9e1-e7b629b780ee
-- title:
--   Expected welfare $\mathbb E_{v\sim F}[R(m,v)]$
-- statement:
--   For a mechanism $m$ and a prior $F\in\mathcal P(\mathbb R^n_+)$, the expected welfare is
--
--   $$
--   \mathbb E_{v\sim F}\big[R(m,v)\big]=\int R\big(S(v),v\big)\,dF(v).
--   $$
--
--   **Formalization Note** The integral is the lower Lebesgue integral of the nonnegative welfare, valued in $[0,\infty]$. It is defined for every allocation rule and agrees with the expectation whenever $v\mapsto R(m,v)$ is measurable, so no measurability is required of mechanisms.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12

import Mathlib
import Definitions.Def_SponsoredAssort_welfare
import Definitions.Def_SponsoredAssort_Mechanism

open scoped NNReal ENNReal
open MeasureTheory

namespace SponsoredAssort

/-- The **expected welfare** `E_{v∼F}[R(m, v)]` of a mechanism `m` under a prior `F` on `ℝⁿ₊`
(Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12), where
`R(m, v) = R(S(v), v)`.

**Formalization Note.** Written as the lower Lebesgue integral `∫⁻` of `ENNReal.ofReal R(m, v)`
(welfare is nonnegative). It is defined for every allocation rule, measurable or not, and equals
the paper's expectation whenever `v ↦ R(m, v)` is measurable. -/
noncomputable def expWelfare {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (F : Measure (Attr n)) :
    ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (welfare r (m.alloc v) v) ∂F

end SponsoredAssort


