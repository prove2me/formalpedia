-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble04
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:44:54.093636+00:00
-- url     : https://prove2.me/theorems/31ce9b73-de8e-4a6e-bb99-cf1e978d020a
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble04 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordAssemble04` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble04.lean; original SHA-256 c1d124b2e5c1f9a0cde9acf371a9afd66dec57261d17e698b5e8b734b44b76a6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks031
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks032
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks033
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks034
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_126 : checkTypes tree [4,4,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,5,5,5] 304=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_126_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_126_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_126_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_126_chunk192 (checkCasesFrom_step tree _ 256 48 checked_type5_126_chunk256 (hend)))))

theorem checked_type5_128 : checkTypes tree [4,4,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,5,5,7] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_128_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_128_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_128_chunk128 (hend)))

theorem checked_type5_130 : checkTypes tree [4,4,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,4,5,7,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_130_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_130_chunk64 (hend))

theorem checked_type5_132 : checkTypes tree [4,5,5,5,5]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,5,5] 480=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_132_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_132_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_132_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_132_chunk192 (checkCasesFrom_step tree _ 256 64 checked_type5_132_chunk256 (checkCasesFrom_step tree _ 320 64 checked_type5_132_chunk320 (checkCasesFrom_step tree _ 384 64 checked_type5_132_chunk384 (checkCasesFrom_step tree _ 448 32 checked_type5_132_chunk448 (hend))))))))

theorem checked_type5_133 : checkTypes tree [4,5,5,5,6]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,5,6] 106=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_133_chunk0 (checkCasesFrom_step tree _ 64 42 checked_type5_133_chunk64 (hend))

theorem checked_type5_134 : checkTypes tree [4,5,5,5,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,5,7] 304=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_134_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_134_chunk64 (checkCasesFrom_step tree _ 128 64 checked_type5_134_chunk128 (checkCasesFrom_step tree _ 192 64 checked_type5_134_chunk192 (checkCasesFrom_step tree _ 256 48 checked_type5_134_chunk256 (hend)))))

theorem checked_type5_137 : checkTypes tree [4,5,5,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,5,7,7] 172=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_137_chunk0 (checkCasesFrom_step tree _ 64 64 checked_type5_137_chunk64 (checkCasesFrom_step tree _ 128 44 checked_type5_137_chunk128 (hend)))

theorem checked_type5_139 : checkTypes tree [4,5,7,7,7]=true := by
  apply checkTypes_of_from
  have hend : checkCasesFrom tree [4,5,7,7,7] 80=true :=
    checkCasesFrom_end tree _ _ (by decide +kernel)
  exact checkCasesFrom_step tree _ 0 64 checked_type5_139_chunk0 (checkCasesFrom_step tree _ 64 16 checked_type5_139_chunk64 (hend))

end ThreeBoundEndpoint40Records


