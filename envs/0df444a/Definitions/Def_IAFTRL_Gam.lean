-- Prove2me | Definitions.Def_IAFTRL_Gam
-- name    : IAFTRL_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:32.833461+00:00
-- url     : https://prove2.me/theorems/a377f5bf-4b9e-4af7-b554-36886b995c74
-- title:
--   Exploration cap $\Gamma_t$
-- statement:
--   The **exploration cap** at round $t\ge1$ is
--   $$
--   \Gamma_t=\frac{4d}{\beta_t}\ \Big(\le\tfrac14\Big).
--   $$
--   It bounds the total extra exploration mass $\gamma=\sum_b w_b$ in the program (2.3).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17

import Mathlib
import Definitions.Def_IAFTRL_beta

namespace IAFTRL

/-- **The exploration cap `Γ_t`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17: "In (2.3), we set `Γ_t = 4d/β_t ≤ 1/4`".

`Gam d K t = 4d / β_t`, with the paper's round index `t ≥ 1`. -/
noncomputable def Gam (d K t : ℕ) : ℝ :=
  4 * (d : ℝ) / beta d K t

end IAFTRL


