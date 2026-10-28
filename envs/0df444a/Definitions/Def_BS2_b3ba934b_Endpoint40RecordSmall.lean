-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
-- name    : BS2_b3ba934b_Endpoint40RecordSmall
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:59:43.930905+00:00
-- url     : https://prove2.me/theorems/3ddda3d1-14af-4a97-9cf7-35a344545884
-- title:
--   Sensitivity separation: Endpoint40RecordSmall (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordSmall` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordSmall.lean; original SHA-256 c4589bf645b1f6149bbd8d184c850b786d160bf0d2702c12acf66b82ca5c38cc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exhaustive kernel checks of the small typed-tournament lengths. -/
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_length0 : checkLength tree 0=true := by decide +kernel
theorem checked_length1 : checkLength tree 1=true := by decide +kernel
theorem checked_length2 : checkLength tree 2=true := by decide +kernel
theorem checked_length3 : checkLength tree 3=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_length3


