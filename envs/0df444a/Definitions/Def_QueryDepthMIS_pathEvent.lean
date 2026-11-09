-- Prove2me | Definitions.Def_QueryDepthMIS_pathEvent
-- name    : QueryDepthMIS_pathEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:32.71434+00:00
-- url     : https://prove2.me/theorems/e6424999-5ca0-4c03-987f-712f6cdb4dd8
-- title:
--   The event $\mathcal E(P, Q)$: $P$ is a query path with shortcut set $Q$
-- statement:
--   For a fixed sequence of positions $P = (p_1, \dots, p_L)$ and a fixed set of positions $Q$,
--   $$
--   \mathcal E(P, Q) :\ P \text{ is a query path and } C(P) = Q,
--   $$
--   i.e. the vertices $(\pi(p_1), \dots, \pi(p_L))$ form a query path of $G$ and its set of shortcut positions is exactly $Q$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_IsQueryPath
import Definitions.Def_QueryDepthMIS_shortcutIdx
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- The event `E(P, Q)` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14): "Consider a fixed such position sequence P and a
fixed subset Q ⊆ {p₁, …, p_{L−2}} with |Q| ≤ h, define the event E(P, Q) : P is a query path and
C(P) = Q."

For a list of positions `P = [p₁, …, p_L]` and a set of positions `Q`: there is a list of vertices
`l` with ranks `P` (so `l = [π(p₁), …, π(p_L)]`) that is a query path of `G`, and the set of
shortcut positions `C(P) = {p_{i+1} : i ∈ shortcutIdx G l}` (0-based `i`) equals `Q`. -/
def pathEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List ℕ) (Q : Finset ℕ) (ω : Perm V) : Prop :=
  ∃ l : List V, l.map (rank ω) = P ∧ IsQueryPath G (rank ω) l ∧
    (shortcutIdx G l).image (fun i => P.getD i 0) = Q

end QueryDepthMIS


