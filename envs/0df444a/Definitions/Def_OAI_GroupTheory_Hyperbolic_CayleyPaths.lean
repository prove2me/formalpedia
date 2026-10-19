-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyPaths
-- name    : OAI_GroupTheory_Hyperbolic_CayleyPaths
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:25:42.839067+00:00
-- url     : https://prove2.me/theorems/dcce2c48-81e7-4ace-b24d-bfb26270fd21
-- title:
--   Generator words based along the spanning tree
-- statement:
--   Each generator of a block presentation is written as a word of oriented edges based at the vertex $o$, using the two-edge spanning tree formed by the base $l$-edge $t_L$ and the base $r$-edge $t_R$.
--
--   1. **Generator words.** An $x$-edge $e$ becomes $t_L\,e\,\bar t_R$, an $l$-edge $e$ becomes $e\,\bar t_L$, and an $r$-edge $e$ becomes $e\,\bar t_R$.
--   2. **Values.** Since the tree edges are relators, the value of each generator word in the presented group is the generator itself:
--   $$
--   \mathrm{val}\bigl(\mathrm{word}(e)\bigr)=\gamma_e .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/CayleyPaths.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/CayleyPaths.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyMetric

namespace OAI

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The original edge is based using the fixed two-edge spanning tree. -/
def generatorWord : d.Edge → List d.OrientedEdge
  | .inl e => [(d.treeL,true),(.inl e,true),(d.treeR,false)]
  | .inr (.inl e) => [(.inr (.inl e),true),(d.treeL,false)]
  | .inr (.inr e) => [(.inr (.inr e),true),(d.treeR,false)]

@[simp] theorem generatorWord_value (e : d.Edge) : d.wordValue (d.generatorWord e) = d.edge e := by
  rcases e with e | e | e <;>
    simp [generatorWord,edgeValue,d.treeL_eq_one,d.treeR_eq_one]

end Release075.BlockPresentation

end OAI


