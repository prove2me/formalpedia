-- Prove2me | Definitions.Def_MarkdownReadjust_proj
-- name    : MarkdownReadjust_proj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:51.471099+00:00
-- url     : https://prove2.me/theorems/76b39e5a-b0e8-4de3-85e6-959c33fbd525
-- title:
--   Projection $(\cdot)^+$ onto $[0,1]$
-- statement:
--   In the definition of the adjusted purchase rates, the operator $(\cdot)^+$ is the projection onto $[0,1]$,
--
--   $$
--   z^+=\max\{0,\min\{z,1\}\},
--   $$
--
--   because a feasible purchase rate cannot exceed $1$.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §5.1, pp.9–10

import Mathlib

namespace MarkdownReadjust

/-- The operator `(·)⁺` of the markdown readjustment policy: the projection onto `[0,1]`
(Chen–Jasin, SSRN 3740871, §5.1, pp.9–10: "the operator (·)+ in the definition of ρn is defined
as a projection onto [0,1] instead of the usual projection onto [0,∞)"). -/
def proj (z : ℝ) : ℝ := max 0 (min z 1)

end MarkdownReadjust


