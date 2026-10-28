-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
-- name    : BS2_b3ba934b_Endpoint40RecordTree
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:33:25.866821+00:00
-- url     : https://prove2.me/theorems/c870bed6-cd39-4b1e-97cd-019ebef2cf4e
-- title:
--   Sensitivity separation: Endpoint40RecordTree (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordTree` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordTree.lean; original SHA-256 fa4fcab4b00f825e8bb2c5fd8c34b4bfd5473df208cd240ba8a394de9b6afd6c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The exact-row tree lists precisely the numerical certificate records. -/
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records

theorem tree_elements : tree.elements=ThreeBoundNumeric.Endpoint40.records := by rfl

end ThreeBoundEndpoint40Records
#print axioms ThreeBoundEndpoint40Records.tree_elements


