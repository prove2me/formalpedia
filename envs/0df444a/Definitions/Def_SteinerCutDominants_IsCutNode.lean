-- Prove2me | Definitions.Def_SteinerCutDominants_IsCutNode
-- name    : SteinerCutDominants_IsCutNode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:42.990129+00:00
-- url     : https://prove2.me/theorems/b90149aa-c911-4c7a-8f4b-856851fa3d75
-- title:
--   Cut node
-- statement:
--   A **cut node** of a connected graph $G$ is a node $w$ for which $G\setminus w$ is not connected.
--
--   **Formalization Note** $G\setminus w$ is the subgraph induced by $V(G)\setminus\{w\}$, and `Connected` includes nonemptiness; every Steiner graph has at least two nodes, so $G\setminus w$ is nonempty.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §5, p.10

import Mathlib

namespace SteinerCutDominants

/-- A cut node of a connected graph `G`: a node `w` for which `G \ w` is not connected (Conforti,
Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §5, p.10). -/
def IsCutNode {V : Type} (G : SimpleGraph V) (w : V) : Prop :=
  ¬ (G.induce ({w}ᶜ : Set V)).Connected

end SteinerCutDominants


