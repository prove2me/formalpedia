-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_BoundedReach
-- name    : KSATSingleFlip_Connect_BoundedReach
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:24:22.673783+00:00
-- url     : https://prove2.me/theorems/9c778e4b-a7c8-4320-bd71-dad2947f6aa8
-- title:
--   Finite directed reachability balls
-- statement:
--   For a directed graph specified by finite outgoing-neighbor sets, $B_r(v)$ is the finite set of vertices reachable from $v$ in at most $r$ steps, including $v$. It is defined recursively by adjoining $v$ and all outgoing neighbors of the preceding ball.
-- source:
--   Auxiliary definition for the path-counting proof of Lemma 2.7 in Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13 (PDF pp. 14–15), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib

namespace KSATSingleFlip.Connect

/-- Vertices reachable in at most r directed steps from root, with finite
neighbor lists. The root is included even for r=0. -/
def boundedReachBall {V : Type} [DecidableEq V] (neighbors : V → Finset V) (root : V) : ℕ → Finset V
  | 0 => {root}
  | r+1 => {root} ∪ (boundedReachBall neighbors root r).biUnion neighbors

end KSATSingleFlip.Connect


