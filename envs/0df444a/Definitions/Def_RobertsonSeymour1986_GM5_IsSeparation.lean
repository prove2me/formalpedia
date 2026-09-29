-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_IsSeparation
-- name    : RobertsonSeymour1986_GM5_IsSeparation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:54:23.633315+00:00
-- url     : https://prove2.me/theorems/02eab639-b25d-4789-8e70-4010d7ca3f43
-- title:
--   Separation of a graph
-- statement:
--   A **separation** of a graph $G$ is a pair $(V_1,V_2)$ of subsets of $V(G)$ with $V_1\cup V_2=V(G)$ such that no vertex of $V_1-V_2$ is adjacent to any vertex of $V_2-V_1$.
--
--   The **order** of the separation is $|V_1\cap V_2|$. Deleting $V_1\cap V_2$ disconnects $V_1-V_2$ from $V_2-V_1$.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, p. 94 (PDF p. 3), definition of separation; DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- `IsSeparation G V₁ V₂`: the pair `(V₁, V₂)` is a separation of `G`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 1, p. 94 (PDF p. 3), unnumbered: "A *separation* of a graph G is a pair (V₁, V₂), where
V₁, V₂ ⊆ V(G), V₁ ∪ V₂ = V(G), and no vertex of V₁ − V₂ is adjacent to any vertex of V₂ − V₁." -/
def IsSeparation {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V₁ V₂ : Finset V) :
    Prop :=
  V₁ ∪ V₂ = Finset.univ ∧ ∀ x ∈ V₁ \ V₂, ∀ y ∈ V₂ \ V₁, ¬ G.Adj x y

end RobertsonSeymour1986.GM5


