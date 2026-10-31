-- Prove2me | Definitions.Def_StaticProphetSec_expUtil
-- name    : StaticProphetSec_expUtil
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:09.177985+00:00
-- url     : https://prove2.me/theorems/03699e60-6721-4063-b55e-74e5fe24cee7
-- title:
--   Expected utilization $\mathbb E[\mathrm{UT}_k(D)]$ of the policy $(t,p)$
-- statement:
--   The **expected utilization** of the policy $(t,p)$ is
--
--   $$\mathbb E[\mathrm{UT}_k(D)],$$
--
--   where $D$ is the number of eligible applicants, and the expectation runs over the independent values and the tie-break coins. At $p=0$ this is $\mathbb E_{V\sim F}[\mathrm{UT}_k(D^t(V))]$ of Definition 1.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Definition 1, p.15; Remark 1, p.5

import Mathlib
import Definitions.Def_StaticProphetSec_UT
import Definitions.Def_StaticProphetSec_accepted
import Definitions.Def_StaticProphetSec_coinProb

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- The expected utilization `E[UT_k(D)]` of the policy `(t, p)` (Arnosti & Ma,
arXiv:2108.12893v2, Definition 1, p.15; Remark 1, p.5). `D` counts the eligible applicants, so
the expectation runs over the values and the tie-break coins.

**Formalization Note.** The integrand is bounded by `1`; the value lies in `ℝ≥0∞`. -/
noncomputable def expUtil {n : ℕ} (k : ℕ) (μ : Fin n → Measure ℝ) (t p : ℝ) : ℝ≥0∞ :=
  ∫⁻ V, ∑ B : Fin n → Bool, coinProb p B * ENNReal.ofReal (UT k (demand t V B)) ∂Measure.pi μ

end StaticProphetSec


