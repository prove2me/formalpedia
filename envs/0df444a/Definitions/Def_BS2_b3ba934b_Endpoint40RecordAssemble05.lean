-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble05
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble05
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:46:34.988606+00:00
-- url     : https://prove2.me/theorems/06906593-a435-4fff-9f5c-389b37a793d3
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble05 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble05` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble05.lean; original SHA-256 cdcd6c327a1b2e8ea5359f5dce70a2ed50cd12bfaa155b48b1ced080fc70fa18; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks034
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks035
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks036
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks037
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks038
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_141 : checkTypes tree [5,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,5,5,5,5] 704=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_141_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_141_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_141_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_141_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type5_141_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type5_141_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type5_141_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type5_141_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type5_141_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type5_141_chunk576 (checkCasesFrom_step tree _ 640 64 checked_type5_141_chunk640 (hend)))))))))))

theorem checked_type5_142 : checkTypes tree [5,5,5,5,6]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,5,5,5,6] 192=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_142_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_142_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_142_chunk128 (hend)))

theorem checked_type5_143 : checkTypes tree [5,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,5,5,5,7] 480=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_143_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_143_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_143_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_143_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type5_143_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type5_143_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type5_143_chunk384 (checkCasesFrom_step tree _ 448 32 checked_type5_143_chunk448 (hend))))))))

theorem checked_type5_145 : checkTypes tree [5,5,5,6,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,5,5,6,7] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_145_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_145_chunk64 (hend))

theorem checked_type5_146 : checkTypes tree [5,5,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,5,5,7,7] 304=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_146_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_146_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_146_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_146_chunk192 (checkCasesFrom_step tree _ 256 48 checked_type5_146_chunk256 (hend)))))

theorem checked_type5_149 : checkTypes tree [5,5,7,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,5,7,7,7] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_149_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_149_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_149_chunk128 (hend)))

theorem checked_type5_151 : checkTypes tree [5,7,7,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [5,7,7,7,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_151_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_151_chunk64 (hend))

theorem checked_type6_1 : checkTypes tree [1,2,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,2,5,5,5,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_1_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_1_chunk64 (hend))

end ThreeBoundEndpoint40Records


