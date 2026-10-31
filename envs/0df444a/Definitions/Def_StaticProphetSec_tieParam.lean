-- Prove2me | Definitions.Def_StaticProphetSec_tieParam
-- name    : StaticProphetSec_tieParam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:15.941991+00:00
-- url     : https://prove2.me/theorems/4784cfc2-3baf-41cd-bac8-cdf06fb448d7
-- title:
--   Eligibility probabilities $q_i=\mathbb P(V_i>t)+p\,\mathbb P(V_i=t)$
-- statement:
--   Under the policy $(t,p)$, applicant $i$ is eligible with probability
--
--   $$q_i=\mathbb P(V_i>t)+p\,\mathbb P(V_i=t).$$
--
--   At $p=0$ this is the paper's $p_i=1-F_i(t)$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, p.17; Remark 1, p.5

import Mathlib

open MeasureTheory

namespace StaticProphetSec

/-- The eligibility probability of applicant `i` under the policy `(t, p)`:
`P(V_i > t) + p · P(V_i = t)`. At `p = 0` this is the paper's `p_i = 1 - F_i(t)` (Arnosti & Ma,
arXiv:2108.12893v2, p.17). -/
noncomputable def tieParam {n : ℕ} (μ : Fin n → Measure ℝ) (t p : ℝ) (i : Fin n) : ℝ :=
  (μ i).real (Set.Ioi t) + p * (μ i).real {t}

end StaticProphetSec


