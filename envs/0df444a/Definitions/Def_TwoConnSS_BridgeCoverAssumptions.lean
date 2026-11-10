-- Prove2me | Definitions.Def_TwoConnSS_BridgeCoverAssumptions
-- name    : TwoConnSS_BridgeCoverAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:57.017197+00:00
-- url     : https://prove2.me/theorems/df030e05-f13d-46eb-b9ab-e5dfa1e8eee3
-- title:
--   The bridge-covering assumptions of §8.1.3
-- statement:
--   The bridge-covering theorem assumes of the graph $G$ that:
--
--   1. $G$ is simple and 2-vertex-connected, has no non-trivial 2-vertex cut, and has the 3-matching property;
--   2. $|V(G)| \ge 27$;
--   3. no 3-vertex cut has a side partition with both sides of size at least eight;
--   4. the 11/10-contractible subgraphs used in the final separator argument are excluded: every $11/10$-contractible subgraph has more than ten vertices.
--
--   Every $(\alpha, \eta)$-structured graph with $11/9 \le \alpha < 5/4$ and $\eta \le 1/100$ satisfies these assumptions.
--
--   **Formalization Note** The only 11/10-contractible subgraph the paper specifies is a ten-vertex subgraph (p.50), so the exclusion is stated for all such subgraphs on at most ten vertices.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.3, p.41; p.50

import Mathlib
import Definitions.Def_TwoConnSS_Structured

namespace TwoConnSS

variable {V : Type*} [Fintype V]

/-- **The bridge-covering assumptions of §8.1.3 on the graph.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1.3, p.41: "We use the following
preprocessing assumptions explicitly. The graph G is simple and 2-vertex-connected, has no
nontrivial 2-vertex cut, and satisfies the 3-matching property. … For the final separator argument,
|V(G)| ≥ 27, there is no large 3-vertex cut, and the 11/10-contractible subgraphs specified below
have been excluded."

`BridgeCoverAssumptions G` says: `G` is 2VC; no non-trivial 2-vertex cut; the 3-matching property;
`|V| ≥ 27`; no 3-vertex cut with a side partition whose sides both have at least eight vertices
(Definition 8.1); every 11/10-contractible subgraph has more than ten vertices.

**Formalization Note.** Simplicity is built into `SimpleGraph`. The only 11/10-contractible subgraph
"specified below" is the subgraph `J` of p.50, on ten vertices; the exclusion is stated for all
11/10-contractible subgraphs on at most ten vertices. A structured graph (`Structured α η`, with
`11/9 ≤ α < 5/4`, `η ≤ 1/100`) satisfies all of these. The conditions on the current cover
(canonicity, and for Algorithm B no 5-cycle component and one neighbour per 4-cycle component) are
separate hypotheses of Theorem 8.22. -/
def BridgeCoverAssumptions (G : SimpleGraph V) : Prop :=
  IsTwoVC G ∧ (∀ u v, ¬ IsNontrivialTwoCut G u v) ∧ HasThreeMatching G ∧
  27 ≤ Fintype.card V ∧ (∀ T, ¬ IsLargeCut G 3 8 T) ∧
  ∀ X EH, IsContractible G (11 / 10) X EH → 10 < X.card

end TwoConnSS


