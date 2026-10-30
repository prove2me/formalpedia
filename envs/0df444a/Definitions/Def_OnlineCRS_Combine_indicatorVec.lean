-- Prove2me | Definitions.Def_OnlineCRS_Combine_indicatorVec
-- name    : OnlineCRS_Combine_indicatorVec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:05.208898+00:00
-- url     : https://prove2.me/theorems/af831548-21fa-466c-9a9a-b3c292715db1
-- title:
--   Characteristic vector $\mathbf 1_I$
-- statement:
--   For a subset $I\subseteq N$, the **characteristic vector** $\mathbf 1_I\in\{0,1\}^N$ has coordinates
--   $$(\mathbf 1_I)_e=\begin{cases}1,& e\in I,\\ 0,& e\notin I.\end{cases}$$
--
--   Characteristic vectors of feasible sets span the polytope $P_{\mathcal F}$ and are the $\{0,1\}$-points that a relaxation must reproduce.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, §1.1, p. 2

import Mathlib

namespace OnlineCRS.Combine

/-- **Characteristic vector `1_I`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, §1.1, p. 2: "`P_F` is the convex hull of all characteristic vectors of feasible sets".

`indicatorVec I : N → ℝ` is the characteristic vector `1_I` of `I ⊆ N`: coordinate `1` on `I`
and `0` off `I`. -/
def indicatorVec {N : Type*} [DecidableEq N] (I : Finset N) : N → ℝ :=
  fun e => if e ∈ I then 1 else 0

end OnlineCRS.Combine


