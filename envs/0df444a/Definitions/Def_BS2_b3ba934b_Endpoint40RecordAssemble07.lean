-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble07
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:54:53.530023+00:00
-- url     : https://prove2.me/theorems/6a123583-f683-4ce1-9c82-6ca75a6d4225
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble07 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble07` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble07.lean; original SHA-256 56a7e8d2ecc356dc463e91065c393df4856408ba3e64f4f651679cf659f63803; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks040
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks041
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks042
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks043
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks044
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks045
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks046
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_10 : checkTypes tree [2,4,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,4,5,5,5] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_10_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_10_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_10_chunk128 (hend)))

theorem checked_type6_11 : checkTypes tree [2,4,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,5,5,5,5] 688=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_11_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_11_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_11_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_11_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_11_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_11_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_11_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_11_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_11_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_11_chunk576 (checkCasesFrom_step tree _ 640 48 checked_type6_11_chunk640 (hend)))))))))))

theorem checked_type6_12 : checkTypes tree [2,4,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,5,5,5,7] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_12_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_12_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_12_chunk128 (hend)))

theorem checked_type6_13 : checkTypes tree [2,5,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,5,5] 2144=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_13_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_13_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_13_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_13_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_13_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_13_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_13_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_13_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_13_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_13_chunk576 (checkCasesFrom_step tree _ 640 64 checked_type6_13_chunk640 (checkCasesFrom_step tree _ 704 64 checked_type6_13_chunk704 (checkCasesFrom_step tree _ 768 64 checked_type6_13_chunk768 (checkCasesFrom_step tree _ 832 64 checked_type6_13_chunk832 (checkCasesFrom_step tree _ 896 64 checked_type6_13_chunk896 (checkCasesFrom_step tree _ 960 64 checked_type6_13_chunk960 (checkCasesFrom_step tree _ 1024 64 checked_type6_13_chunk1024 (checkCasesFrom_step tree _ 1088 64 checked_type6_13_chunk1088 (checkCasesFrom_step tree _ 1152 64 checked_type6_13_chunk1152 (checkCasesFrom_step tree _ 1216 64 checked_type6_13_chunk1216 (checkCasesFrom_step tree _ 1280 64 checked_type6_13_chunk1280 (checkCasesFrom_step tree _ 1344 64 checked_type6_13_chunk1344 (checkCasesFrom_step tree _ 1408 64 checked_type6_13_chunk1408 (checkCasesFrom_step tree _ 1472 64 checked_type6_13_chunk1472 (checkCasesFrom_step tree _ 1536 64 checked_type6_13_chunk1536 (checkCasesFrom_step tree _ 1600 64 checked_type6_13_chunk1600 (checkCasesFrom_step tree _ 1664 64 checked_type6_13_chunk1664 (checkCasesFrom_step tree _ 1728 64 checked_type6_13_chunk1728 (checkCasesFrom_step tree _ 1792 64 checked_type6_13_chunk1792 (checkCasesFrom_step tree _ 1856 64 checked_type6_13_chunk1856 (checkCasesFrom_step tree _ 1920 64 checked_type6_13_chunk1920 (checkCasesFrom_step tree _ 1984 64 checked_type6_13_chunk1984 (checkCasesFrom_step tree _ 2048 64 checked_type6_13_chunk2048 (checkCasesFrom_step tree _ 2112 32 checked_type6_13_chunk2112 (hend))))))))))))))))))))))))))))))))))

theorem checked_type6_14 : checkTypes tree [2,5,5,5,5,6]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,5,6] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_14_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_14_chunk64 (hend))

theorem checked_type6_15 : checkTypes tree [2,5,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,5,7] 688=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_15_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_15_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_15_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_15_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_15_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_15_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_15_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_15_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_15_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_15_chunk576 (checkCasesFrom_step tree _ 640 48 checked_type6_15_chunk640 (hend)))))))))))

theorem checked_type6_16 : checkTypes tree [2,5,5,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,7,7] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_16_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_16_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_16_chunk128 (hend)))

theorem checked_type6_17 : checkTypes tree [3,4,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [3,4,5,5,5,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_17_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_17_chunk64 (hend))

end ThreeBoundEndpoint40Records


