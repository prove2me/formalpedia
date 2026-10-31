-- Prove2me | Definitions.Def_Underdogs_Condition6
-- name    : Underdogs_Condition6
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:58.510582+00:00
-- url     : https://prove2.me/theorems/fd53ab43-65ff-4018-b735-b766908ccf9e
-- title:
--   Condition (6): low quality gains proportionally more from resources
-- statement:
--   For a success function $g(q,r)$, quality levels $l$ (low) and $h$ (high), resources $r$ and an increment $\delta$, **condition (6)** says that the increase in resources from $r$ to $r+\delta$ raises the success probability of low-quality agents proportionally more than that of high-quality agents:
--   $$
--   \frac{g(l,r+\delta)-g(l,r)}{g(l,r)}>\frac{g(h,r+\delta)-g(h,r)}{g(h,r)}.
--   $$
--
--   It is the paper's characterization of when an increase in resources makes success less diagnostic of quality.
--
--   **Formalization Note** The condition is stated as printed, for given $r$ and $\delta$. In the paper's use (Appendix B) it is taken at $r=r_1$, $r+\delta=r_3$.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §5.1, eq. (6), p.11 (PDF p.12)

import Mathlib

namespace Underdogs

/-- Condition (6): an increase in resources from `r` to `r + δ` raises the success probability of
low-quality agents (quality `l`) proportionally more than that of high-quality agents (quality
`h`):
`(g(l, r + δ) − g(l, r)) / g(l, r) > (g(h, r + δ) − g(h, r)) / g(h, r)`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §5.1, eq. (6), p.11 (PDF p.12).

**Formalization Note** The condition is stated exactly as printed, for given `r` and `δ`. In the
paper's use (Appendix B, p.35) it is evaluated at `r = r1`, `r + δ = r3`, i.e. `δ = r3 − r1`. -/
def Condition6 (g : ℝ → ℝ → ℝ) (l h r δ : ℝ) : Prop :=
  (g l (r + δ) - g l r) / g l r > (g h (r + δ) - g h r) / g h r

end Underdogs


