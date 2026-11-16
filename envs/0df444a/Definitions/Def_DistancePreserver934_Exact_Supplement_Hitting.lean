-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
-- name    : DistancePreserver934_Exact_Supplement_Hitting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:20:22.946597+00:00
-- url     : https://prove2.me/theorems/8da17787-011c-41b8-8861-472567debed9
-- title:
--   Definition 9 — demand hitting
-- statement:
--   A vertex $u$ hits a demand $q$ in $H$ if an edge $e\in E(H)$ is essential to $q$ and one of its endpoints $x\in e$ is adjacent to $u$ in $H$. A set $S$ hits $Q$ when
--
--   $$\forall q\in Q\;\exists u\in S\;\exists e\in E(H)\;\exists x\in e:\ ux\in E(H)\text{ and }e\text{ is essential to }q.$$
--
--   Essentiality is the published predicate quantifying over every shortest walk in the current graph. Hitting differs from covering by the extra adjacency; it includes no private-edge, density or length hypothesis.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Definition 9, printed p. 13 (PDF p. 14)

import Definitions.Def_DistancePreserver934_Exact_Essential

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

/-- Definition 9: one adjacency from a vertex to an endpoint of an essential edge. -/
def Hits {V : Type} (H : SimpleGraph V) (u : V) (q : Sym2 V) : Prop :=
  ∃ e ∈ H.edgeSet, ∃ x ∈ e, H.Adj u x ∧ IsEssential H q e

/-- Every demand has a hitting tuple whose first vertex lies in S. -/
def HitsAll {V : Type} (H : SimpleGraph V) (S : Finset V) (Q : Finset (Sym2 V)) : Prop :=
  ∀ q ∈ Q, ∃ u ∈ S, Hits H u q

end DistancePreserver934.Exact.Supplement


