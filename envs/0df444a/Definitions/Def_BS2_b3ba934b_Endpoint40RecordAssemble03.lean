-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble03
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:44:43.866235+00:00
-- url     : https://prove2.me/theorems/ce6cd527-9813-4063-b983-166834841da7
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble03.lean; original SHA-256 e648acb18b5ef5f0b45d2c61d5f4b056fb0e824af70f1f2e5a6505c3dab2064f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks028
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks029
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks030
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks031
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_99 : checkTypes tree [2,5,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,7,7] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_99_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_99_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_99_chunk128 (hend)))

theorem checked_type5_101 : checkTypes tree [2,5,7,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,7,7,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_101_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_101_chunk64 (hend))

theorem checked_type5_109 : checkTypes tree [3,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [3,4,5,5,5] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_109_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_109_chunk64 (hend))

theorem checked_type5_113 : checkTypes tree [3,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [3,5,5,5,5] 192=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_113_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_113_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_113_chunk128 (hend)))

theorem checked_type5_115 : checkTypes tree [3,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [3,5,5,5,7] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_115_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_115_chunk64 (hend))

theorem checked_type5_120 : checkTypes tree [4,4,4,4,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,4,4,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_120_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_120_chunk64 (hend))

theorem checked_type5_122 : checkTypes tree [4,4,4,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,4,5,5] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_122_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_122_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_122_chunk128 (hend)))

theorem checked_type5_124 : checkTypes tree [4,4,4,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,4,5,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_124_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_124_chunk64 (hend))

end ThreeBoundEndpoint40Records


