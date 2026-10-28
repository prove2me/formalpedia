-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble08
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble08
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:50:39.37347+00:00
-- url     : https://prove2.me/theorems/9f5a2e02-de7b-47c4-bc96-105102c026e5
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble08 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble08` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble08.lean; original SHA-256 7b427f2f1ab4226192df11dcba7a013ba7724c8dfd09259eb5a4c74e1280d8b6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks046
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks047
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks048
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks049
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks050
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks051
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks052
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_18 : checkTypes tree [3,5,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [3,5,5,5,5,5] 424=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_18_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_18_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_18_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_18_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_18_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_18_chunk320 (checkCasesFrom_step tree _ 384 40 checked_type6_18_chunk384 (hend)))))))

theorem checked_type6_19 : checkTypes tree [3,5,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [3,5,5,5,5,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_19_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_19_chunk64 (hend))

theorem checked_type6_20 : checkTypes tree [4,4,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,4,5,5,5] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_20_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_20_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_20_chunk128 (hend)))

theorem checked_type6_21 : checkTypes tree [4,4,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,5,5,5,5] 688=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_21_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_21_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_21_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_21_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_21_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_21_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_21_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_21_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_21_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_21_chunk576 (checkCasesFrom_step tree _ 640 48 checked_type6_21_chunk640 (hend)))))))))))

theorem checked_type6_22 : checkTypes tree [4,4,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,5,5,5,7] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_22_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_22_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_22_chunk128 (hend)))

theorem checked_type6_23 : checkTypes tree [4,5,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,5,5,5] 2144=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_23_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_23_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_23_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_23_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_23_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_23_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_23_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_23_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_23_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_23_chunk576 (checkCasesFrom_step tree _ 640 64 checked_type6_23_chunk640 (checkCasesFrom_step tree _ 704 64 checked_type6_23_chunk704 (checkCasesFrom_step tree _ 768 64 checked_type6_23_chunk768 (checkCasesFrom_step tree _ 832 64 checked_type6_23_chunk832 (checkCasesFrom_step tree _ 896 64 checked_type6_23_chunk896 (checkCasesFrom_step tree _ 960 64 checked_type6_23_chunk960 (checkCasesFrom_step tree _ 1024 64 checked_type6_23_chunk1024 (checkCasesFrom_step tree _ 1088 64 checked_type6_23_chunk1088 (checkCasesFrom_step tree _ 1152 64 checked_type6_23_chunk1152 (checkCasesFrom_step tree _ 1216 64 checked_type6_23_chunk1216 (checkCasesFrom_step tree _ 1280 64 checked_type6_23_chunk1280 (checkCasesFrom_step tree _ 1344 64 checked_type6_23_chunk1344 (checkCasesFrom_step tree _ 1408 64 checked_type6_23_chunk1408 (checkCasesFrom_step tree _ 1472 64 checked_type6_23_chunk1472 (checkCasesFrom_step tree _ 1536 64 checked_type6_23_chunk1536 (checkCasesFrom_step tree _ 1600 64 checked_type6_23_chunk1600 (checkCasesFrom_step tree _ 1664 64 checked_type6_23_chunk1664 (checkCasesFrom_step tree _ 1728 64 checked_type6_23_chunk1728 (checkCasesFrom_step tree _ 1792 64 checked_type6_23_chunk1792 (checkCasesFrom_step tree _ 1856 64 checked_type6_23_chunk1856 (checkCasesFrom_step tree _ 1920 64 checked_type6_23_chunk1920 (checkCasesFrom_step tree _ 1984 64 checked_type6_23_chunk1984 (checkCasesFrom_step tree _ 2048 64 checked_type6_23_chunk2048 (checkCasesFrom_step tree _ 2112 32 checked_type6_23_chunk2112 (hend))))))))))))))))))))))))))))))))))

theorem checked_type6_24 : checkTypes tree [4,5,5,5,5,6]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,5,5,6] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_24_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_24_chunk64 (hend))

theorem checked_type6_25 : checkTypes tree [4,5,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,5,5,7] 688=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_25_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_25_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_25_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_25_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_25_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_25_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_25_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_25_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_25_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_25_chunk576 (checkCasesFrom_step tree _ 640 48 checked_type6_25_chunk640 (hend)))))))))))

end ThreeBoundEndpoint40Records


