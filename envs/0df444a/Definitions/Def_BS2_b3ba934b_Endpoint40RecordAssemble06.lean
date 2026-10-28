-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble06
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:47:47.008148+00:00
-- url     : https://prove2.me/theorems/77a2ab2e-0162-4737-bb71-2c95da55b644
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble06 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble06` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble06.lean; original SHA-256 ca1f18636ba26d42cc66edc211b64878a82c0529e572e21c939bdaa76660fc2e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks038
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks039
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks040
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_2 : checkTypes tree [1,4,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,4,5,5,5,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_2_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_2_chunk64 (hend))

theorem checked_type6_3 : checkTypes tree [1,5,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,5,5,5,5,5] 424=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_3_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_3_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_3_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_3_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_3_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_3_chunk320 (checkCasesFrom_step tree _ 384 40 checked_type6_3_chunk384 (hend)))))))

theorem checked_type6_4 : checkTypes tree [1,5,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,5,5,5,5,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_4_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_4_chunk64 (hend))

theorem checked_type6_5 : checkTypes tree [2,2,2,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,2,5,5,5] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_5_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_5_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_5_chunk128 (hend)))

theorem checked_type6_6 : checkTypes tree [2,2,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,4,5,5,5] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_6_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_6_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_6_chunk128 (hend)))

theorem checked_type6_7 : checkTypes tree [2,2,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,5,5,5,5] 688=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_7_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_7_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type6_7_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type6_7_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type6_7_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type6_7_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type6_7_chunk384 (checkCasesFrom_step tree _ 448 64 checked_type6_7_chunk448 (checkCasesFrom_step tree _ 512 64 checked_type6_7_chunk512 (checkCasesFrom_step tree _ 576 64 checked_type6_7_chunk576 (checkCasesFrom_step tree _ 640 48 checked_type6_7_chunk640 (hend)))))))))))

theorem checked_type6_8 : checkTypes tree [2,2,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,5,5,5,7] 132=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_8_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type6_8_chunk64 (checkCasesFrom_step tree _ 128 4 checked_type6_8_chunk128 (hend)))

theorem checked_type6_9 : checkTypes tree [2,3,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,3,5,5,5,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type6_9_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type6_9_chunk64 (hend))

end ThreeBoundEndpoint40Records


