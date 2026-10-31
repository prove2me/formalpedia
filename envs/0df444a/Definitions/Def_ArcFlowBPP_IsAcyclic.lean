-- Prove2me | Definitions.Def_ArcFlowBPP_IsAcyclic
-- name    : ArcFlowBPP_IsAcyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:36.985103+00:00
-- url     : https://prove2.me/theorems/7556f2b7-3d0d-4046-a338-ca21a0ff3e47
-- title:
--   Acyclic labelled multigraph
-- statement:
--   The graph $G$ is **acyclic** if it has no closed directed walk of positive length: there is no nonempty walk from a vertex back to itself.
--
--   The paper requires the graph of the arc-flow model to be "a directed acyclic graph".
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, §3, p.7 ("we always need to ensure that it is a directed acyclic graph")

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_IsWalk

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, §3, p.7: "we always need to ensure that it is a directed acyclic graph".
The labelled graph `G` is acyclic: there is no closed directed walk of positive length. -/
def IsAcyclic {m : ℕ} {V A : Type*} (G : LabelledGraph m V A) : Prop :=
  ∀ (v : V) (π : List A), π ≠ [] → ¬ IsWalk G v π v

end ArcFlowBPP


