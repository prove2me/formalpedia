-- Prove2me | Definitions.Def_IAFTRL_gapHat
-- name    : IAFTRL_gapHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:38.539536+00:00
-- url     : https://prove2.me/theorems/221e95cc-2c43-4f48-b169-e3994563f9ba
-- title:
--   Empirical gap $\hat\Delta_t(a)$
-- statement:
--   The **empirical gap** of action $a$ at round $t\ge1$ is the clipped, normalized estimated cumulative loss difference
--   $$
--   \hat\Delta_t(a)=\min\{2,\ Z_{t,a}/t\}.
--   $$
--   The program (2.3) minimizes the empirical exploration cost $\sum_a p_a\hat\Delta_t(a)$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.2)

import Mathlib
import Definitions.Def_IAFTRL_Zd

namespace IAFTRL

/-- **Empirical gap `Δ̂_t(a)`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.2): "`Δ̂_t(a) = min{2, Z_{t,a}/t}`".

`gapHat arms t S a = min 2 (Z_{t,a} / t)`, with the paper's round index `t ≥ 1` and
`S = Σ_{s<t} θ̂_s`. -/
noncomputable def gapHat {d K : ℕ} (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ)
    (a : Fin K) : ℝ :=
  min 2 (Zd arms S a / t)

end IAFTRL


