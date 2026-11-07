-- Prove2me | Definitions.Def_StableVotingDistortion_leftRank
-- name    : StableVotingDistortion_leftRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:07.181835+00:00
-- url     : https://prove2.me/theorems/9654f30d-1dcf-4f8d-a184-e046337e1779
-- title:
--   The left-boundary rank $\mathrm{rank}_v(a;D)$
-- statement:
--   Given a voter $v$ and a lottery $D$, arrange an interval of width $D(a)$ for each candidate $a$ on $[0,1]$, in increasing order of $v$'s preference. The **rank** of $a$ is the left boundary of its interval:
--   $$\mathrm{rank}_v(a;D)=\Pr_{b\sim D}[a\succ_v b]=\sum_{b:\,a\succ_v b}D(b).$$
--
--   Higher rank is better: a favorite of mass $m$ has rank $1-m$. Candidate $a$ occupies $[\mathrm{rank}_v(a;D),\mathrm{rank}_v(a;D)+D(a))$.
--
--   **Formalization Note** The paper overloads $\mathrm{rank}_v$ on p.8. This definition is only the left boundary; the random-copy rank of an attacker is the separate definition `activation`.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

open Classical in
/-- The **left-boundary rank** of `a` on `v`'s rank line,
`rank_v(a; D) = Pr_{b ∼ D}[a ≻_v b] = ∑_{b : a ≻_v b} D(b)`. The rank line runs worst to best, so a
favorite has rank near `1`, and `a` occupies the interval `[rank_v(a; D), rank_v(a; D) + D(a))`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6: "We define the rank of a candidate a with respect to distribution D as:
rank_v(a; D) = Pr_{b∼D}[a ≻_v b]. For intuition, higher rank is better (more preferred). Visually, the
rank of a candidate is the coordinate of the left boundary of a's interval."

**Formalization Note.** The paper overloads `rank_v` (p.8). This declaration is only the left
boundary; the attacker's random-copy rank is `activation`. -/
noncomputable def leftRank {V C : Type} [Fintype C] (E : Election V C) (D : C → ℝ)
    (v : V) (a : C) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => E.prefers v a b), D b

end StableVotingDistortion


