-- Prove2me | Definitions.Def_DRSub4633_t0
-- name    : DRSub4633_t0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:34.983209+00:00
-- url     : https://prove2.me/theorems/4eea0c64-9657-4744-9d28-70f19a070b14
-- title:
--   The time $t_0=1/4$
-- statement:
--   The time $t_0=1/4$: the averaging densities $w$ and $\varpi$ vanish before $t_0$, where only the small-block comparison is used.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (8), p.9

import Mathlib

namespace DRSub4633

/-- **The time `t₀ = 1/4`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (8), p.9: "`t₀ = 1/4`". -/
noncomputable def t0 : ℝ := 1 / 4

end DRSub4633


