-- Prove2me | Definitions.Def_BlockBochner_Supplement_IsForestEdges
-- name    : BlockBochner_Supplement_IsForestEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:32:15.913544+00:00
-- url     : https://prove2.me/theorems/9d881bb0-0dd9-4931-ae63-c87af9b0c278
-- title:
--   Forests: independent sets of the graphic matroid
-- statement:
--   In the graphic (cycle) matroid of a finite multigraph $G$ with edge set $E$, a subset $F\subseteq E$ is independent iff it is a forest, i.e. it contains no cycle. Equivalently, no edge $e\in F$ with endpoints $u,v$ has $u$ and $v$ connected in $(W,F\setminus\{e\})$.
--
--   A loop is a cycle and two parallel edges form a cycle, so neither occurs in a forest.
--
--   **Formalization Note** Stated by the equivalent edge-by-edge condition using `edgeConn`; the verification file checks a loop, a single edge, and two parallel edges.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 1.5, pp.7–8 (PDF pp.8–9); Sec. 5, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_edgeConn

namespace BlockBochner.Supplement

/-- **Forests (independent sets of the graphic matroid).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.5,
pp.7–8: in the graphic matroid of a graph, `E` is the set of edges and `I` is the set of acyclic
subsets of `E` (subforests). `IsForestEdges ends F` says the edge set `F` contains no cycle.

**Formalization Note** Multigraph reading (edges `α` with endpoint map `ends : α → Sym2 W`). `F` is
acyclic iff no edge `e ∈ F` lies on a cycle, i.e. iff for every `e ∈ F` with endpoints `{u, v}`, the
vertices `u` and `v` are not connected in `(W, F ∖ {e})`. A loop (`u = v`) is a cycle and two
parallel edges form a cycle, so neither lies in a forest. -/
def IsForestEdges {W α : Type*} [DecidableEq α] (ends : α → Sym2 W) (F : Finset α) : Prop :=
  ∀ e ∈ F, ∀ u v : W, ends e = s(u, v) → ¬ edgeConn ends (F.erase e) u v

end BlockBochner.Supplement


