-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble00
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:43:25.218033+00:00
-- url     : https://prove2.me/theorems/cd7bb3c4-d8c2-4493-a13d-a9e58c77dfb4
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble00.lean; original SHA-256 8ad8b7774194d31c0d8254ab3b0eccaac588a4b9c4d316499dba757b31d730fa; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks018
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks019
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks020
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks021
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_25 : checkTypes tree [1,2,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,2,5,5,5] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_25_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_25_chunk64 (hend))

theorem checked_type5_35 : checkTypes tree [1,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,4,5,5,5] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_35_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_35_chunk64 (hend))

theorem checked_type5_39 : checkTypes tree [1,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,5,5,5,5] 192=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_39_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_39_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_39_chunk128 (hend)))

theorem checked_type5_41 : checkTypes tree [1,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [1,5,5,5,7] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_41_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_41_chunk64 (hend))

theorem checked_type5_47 : checkTypes tree [2,2,2,2,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,2,2,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_47_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_47_chunk64 (hend))

theorem checked_type5_51 : checkTypes tree [2,2,2,4,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,2,4,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_51_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_51_chunk64 (hend))

theorem checked_type5_53 : checkTypes tree [2,2,2,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,2,5,5] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_53_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_53_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_53_chunk128 (hend)))

theorem checked_type5_55 : checkTypes tree [2,2,2,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,2,5,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_55_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_55_chunk64 (hend))

end ThreeBoundEndpoint40Records


