-- Prove2me | Definitions.Def_PlantedSubgraphLD_ov
-- name    : PlantedSubgraphLD_ov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:47.164804+00:00
-- url     : https://prove2.me/theorems/dbf40971-973b-48eb-af11-24589f5a2086
-- title:
--   Ordered edge decompositions and the vertex-overlap count $\mathrm{ov}(F,\mathcal T(F))$
-- statement:
--   Let $F^\circ$ be a graph given by its edge set (with its incident vertices). An **ordered edge decomposition** of $F^\circ$ is an ordered tuple $\mathcal T(F^\circ)=(T^\circ_1,\dots,T^\circ_m)$ of nonempty subgraphs of $F^\circ$, each specified by its edge set together with its incident vertices, whose edge sets form an ordered partition
--
--   $$
--   E(F^\circ)=E(T^\circ_1)\sqcup E(T^\circ_2)\sqcup\cdots\sqcup E(T^\circ_m).
--   $$
--
--   Its **vertex-overlap count** is
--
--   $$
--   \mathrm{ov}(F,\mathcal T(F))=\sum_{i=1}^m v(T_i)-v(F),
--   $$
--
--   the number of extra vertex incidences created by cutting $F$ into the pieces. Small overlap is what lets the weight $n^{e(F)-v(F)}$ of a large subgraph be bounded by the product of the weights of its pieces.
--
--   **Formalization Note** Graphs are given by edge sets, pieces by a function `T : Fin m → Finset (Sym2 V)` (`IsOrderedEdgeDecomp`: nonempty, pairwise disjoint, union $E(F^\circ)$), and $v(\cdot)$ is the number of endpoints of the edges (`edgeSupp`). The overlap is an integer.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, (4.3), p.17 (PDF p.19); definition of ov, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_AbsGraph

namespace PlantedSubgraphLD

/-- `(T₁, …, T_m)` is an ordered edge decomposition of the edge set `S`: nonempty pieces whose edge
sets form an ordered partition `S = T₁ ⊔ ⋯ ⊔ T_m` (§4.1, p.17, (4.3)). -/
def IsOrderedEdgeDecomp {V : Type} [DecidableEq V] (S : Finset (Sym2 V)) {m : ℕ}
    (T : Fin m → Finset (Sym2 V)) : Prop :=
  (∀ i, (T i).Nonempty) ∧ (Pairwise fun i j => Disjoint (T i) (T j)) ∧
    Finset.univ.biUnion T = S

/-- The vertex-overlap count `ov(F, T(F)) = ∑ᵢ v(Tᵢ) − v(F)` of an ordered edge decomposition.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, p.19: "ov(F, T(F)) := ∑_{i=1}^m v(Ti) −
v(F) is the vertex-overlap count of the ordered edge decomposition T(F)." Ordered edge
decompositions, (4.3), p.17: "an ordered tuple T(F°) = (T°1, …, T°m) of nonempty subgraphs
T°i ⊂ F° whose edge sets form an ordered partition of E(F°) […] Each T°i is specified by its
edge set together with its incident vertices".

**Formalization Note** Graphs are given by their edge sets `S`, `Tᵢ`, and `v(·)` is the number of
incident vertices (`edgeSupp`), as in the paper (pieces and abstract graphs have no isolated
vertices). The count is an integer. -/
noncomputable def ov {V : Type} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) {m : ℕ}
    (T : Fin m → Finset (Sym2 V)) : ℤ :=
  (∑ i, ((edgeSupp (T i)).card : ℤ)) - (edgeSupp S).card

end PlantedSubgraphLD


