-- Prove2me | Definitions.Def_Underdogs_ofResource
-- name    : Underdogs_ofResource
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:47.576971+00:00
-- url     : https://prove2.me/theorems/359d9000-9d85-4bc8-9012-c40ce8c3e08b
-- title:
--   Two-period model induced by a success function $g(q,r)$
-- statement:
--   Let $g(q,r)$ be the probability of success of an agent of quality $q$ with resources $r$, and let $l$ and $h$ be the low and high quality levels. Agents start with resources $r_2$; a first-period success raises them to $r_3$ and a failure lowers them to $r_1$. The induced two-period model has
--   $$
--   p_h=g(h,r_2),\quad p_l=g(l,r_2),\quad p_{h,S}=g(h,r_3),\quad p_{l,S}=g(l,r_3),\quad p_{h,F}=g(h,r_1),\quad p_{l,F}=g(l,r_1).
--   $$
--
--   This links the paper's general analysis of quality–resource interactions (§5.1, Appendix B) to the six-parameter model of §4.
--
--   **Formalization Note** The orderings $r_1<r_2<r_3$, $l<h$ and the monotonicity of $g$ are not built into the definition; the theorems state them where they are used.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §5.1, p.11 (PDF p.12); Appendix B, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params

namespace Underdogs

/-- The two-period model induced by a success-probability function `g(q, r)` of quality and
resources: agents of quality `l` (low) and `h` (high) start with resources `r2`; success
raises resources to `r3` and failure lowers them to `r1`. Hence
`p_h = g(h, r2)`, `p_l = g(l, r2)`, `p_{h,S} = g(h, r3)`, `p_{l,S} = g(l, r3)`,
`p_{h,F} = g(h, r1)`, `p_{l,F} = g(l, r1)`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §5.1, p.11 (PDF p.12), and Appendix B, p.35 (PDF p.36): "Suppose that failure decreases
resources from r2 to r1 < r2, while success increases resources to r3 > r2".

**Formalization Note** The first period is played at resources `r2`. The ordering
`r1 < r2 < r3`, `l < h` and the monotonicity of `g` are not part of this definition; theorems
state them where the paper uses them. -/
def ofResource (g : ℝ → ℝ → ℝ) (l h r1 r2 r3 : ℝ) : Params where
  ph := g h r2
  pl := g l r2
  phS := g h r3
  plS := g l r3
  phF := g h r1
  plF := g l r1

end Underdogs


