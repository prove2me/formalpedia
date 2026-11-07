-- Prove2me | Definitions.Def_EffHorizonProphet_Rule
-- name    : EffHorizonProphet_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:45.024178+00:00
-- url     : https://prove2.me/theorems/0eda1ebe-761a-49f7-bb76-473af0bb7adb
-- title:
--   Single-quantile threshold rule $(\alpha,\theta)$
-- statement:
--   A **single-quantile threshold rule** is a pair $(\alpha,\theta)$, where $\alpha\in[0,\infty]$ is the base threshold (the paper's $\alpha_1$) and $\theta\in[0,1]$ is the tie-breaking probability.
--
--   Once the base threshold is fixed, the phase thresholds $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ are determined, so one scalar parameter (plus the tie-break) describes the policy.
--
--   **Formalization Note** $\alpha=\infty$ is the rule that never accepts, which is the paper's $p=0$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.4; Remark 5, p.9; Remark 16, p.31

import Mathlib

open scoped ENNReal

namespace EffHorizonProphet

/-- A **single-quantile threshold rule** in the base scale (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.4; Remark 5, p.9;
Remark 16, p.31): the base threshold `α` (the paper's `α₁`) and the tie-breaking probability `θ`.

**Formalization Note** `α = ⊤` is the rule that never accepts, the paper's `p = 0` (p.21: "If
`p_n = 0` …"): no finite threshold has acceptance probability `0` for an unbounded law. -/
structure Rule where
  /-- The base threshold; `⊤` never accepts. -/
  α : ℝ≥0∞
  /-- The tie-breaking probability. -/
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  θ_le_one : θ ≤ 1

end EffHorizonProphet


