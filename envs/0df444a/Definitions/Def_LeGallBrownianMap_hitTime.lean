-- Prove2me | Definitions.Def_LeGallBrownianMap_hitTime
-- name    : LeGallBrownianMap_hitTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:08.785572+00:00
-- url     : https://prove2.me/theorems/53f5152e-46a8-4c27-9b68-4fd68cb4efd4
-- title:
--   Hitting times $S_r$ of the labels
-- statement:
--   For a label path $Z$ on $[0,1]$ and $r\ge0$,
--
--   $$
--   S_r=\inf\{s\in[0,1]: Z_s=-r\},\qquad \inf\varnothing=\infty .
--   $$
--
--   For continuous $Z$, $S_r<\infty$ iff $r\le\Delta$, and $\Gamma(r)=p(S_r)$ is the point at distance $r$ from $p(0)$ on the geodesic to $x_*$.
--
--   **Formalization Note** Valued in $\mathbb R\cup\{\infty\}$ (`WithTop ℝ`), keeping the convention $\inf\varnothing=\infty$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.14

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.14:
"We set for every r ≥ 0, S_r = inf{s ∈ [0, 1] : Z_s = −r} with the usual convention inf ∅ = ∞."

`hitTime Z r = S_r ∈ [0, 1] ∪ {∞}`.

**Formalization Note.** Valued in `WithTop ℝ`, with `⊤ = ∞` when `Z` never takes the value
`−r`, so the convention `inf ∅ = ∞` is kept (no junk `0`). -/
noncomputable def hitTime (Z : unitInterval → ℝ) (r : ℝ) : WithTop ℝ := by
  classical
  exact if ∃ s, Z s = -r then ((sInf {x : ℝ | ∃ s : unitInterval, (s : ℝ) = x ∧ Z s = -r} : ℝ) :
    WithTop ℝ) else ⊤

end LeGallBrownianMap


