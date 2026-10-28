-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble01
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:41:44.888669+00:00
-- url     : https://prove2.me/theorems/6a6d965b-2c3a-4cdc-8d4b-c7cbe3aec0df
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble01.lean; original SHA-256 ed04fcee2d50e10d097119e93ebed3efb892b3154207f43cac8e0def4ed341cf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks022
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks023
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks024
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks025
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_61 : checkTypes tree [2,2,4,4,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,4,4,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_61_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_61_chunk64 (hend))

theorem checked_type5_63 : checkTypes tree [2,2,4,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,4,5,5] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_63_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_63_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_63_chunk128 (hend)))

theorem checked_type5_65 : checkTypes tree [2,2,4,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,4,5,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_65_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_65_chunk64 (hend))

theorem checked_type5_67 : checkTypes tree [2,2,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,5,5,5] 304=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_67_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_67_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_67_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_67_chunk192 (checkCasesFrom_step tree _ 256 48 checked_type5_67_chunk256 (hend)))))

theorem checked_type5_69 : checkTypes tree [2,2,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,5,5,7] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_69_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_69_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_69_chunk128 (hend)))

theorem checked_type5_71 : checkTypes tree [2,2,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,2,5,7,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_71_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_71_chunk64 (hend))

theorem checked_type5_77 : checkTypes tree [2,3,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,3,5,5,5] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_77_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_77_chunk64 (hend))

theorem checked_type5_82 : checkTypes tree [2,4,4,4,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [2,4,4,4,5] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_82_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_82_chunk64 (hend))

end ThreeBoundEndpoint40Records


