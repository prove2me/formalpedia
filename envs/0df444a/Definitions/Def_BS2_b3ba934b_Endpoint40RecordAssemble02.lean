-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble02
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:44:00.437366+00:00
-- url     : https://prove2.me/theorems/e7ce13b8-8fdd-473c-82c4-19018b88a0e6
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble02.lean; original SHA-256 375e36acb8fab523b056aaba5e9305c5fc1e9741fde09fe81403cf733694286c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks025
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks026
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks027
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks028
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_84 : checkTypes tree [2,4,4,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,4,5,5] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_84_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_84_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_84_chunk128 (hend)))

theorem checked_type5_86 : checkTypes tree [2,4,4,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,4,5,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_86_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_86_chunk64 (hend))

theorem checked_type5_88 : checkTypes tree [2,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,5,5,5] 304=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_88_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_88_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_88_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_88_chunk192 (checkCasesFrom_step tree _ 256 48 checked_type5_88_chunk256 (hend)))))

theorem checked_type5_90 : checkTypes tree [2,4,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,5,5,7] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_90_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_90_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_90_chunk128 (hend)))

theorem checked_type5_92 : checkTypes tree [2,4,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,5,7,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_92_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_92_chunk64 (hend))

theorem checked_type5_94 : checkTypes tree [2,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,5] 480=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_94_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_94_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_94_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_94_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type5_94_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type5_94_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type5_94_chunk384 (checkCasesFrom_step tree _ 448 32 checked_type5_94_chunk448 (hend))))))))

theorem checked_type5_95 : checkTypes tree [2,5,5,5,6]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,6] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_95_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_95_chunk64 (hend))

theorem checked_type5_96 : checkTypes tree [2,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,5,5,5,7] 304=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_96_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_96_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_96_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_96_chunk192 (checkCasesFrom_step tree _ 256 48 checked_type5_96_chunk256 (hend)))))

end ThreeBoundEndpoint40Records


