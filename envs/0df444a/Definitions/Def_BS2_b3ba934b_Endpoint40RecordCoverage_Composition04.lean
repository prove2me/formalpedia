-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordCoverage_Composition04
-- name    : BS2_b3ba934b_Endpoint40RecordCoverage_Composition04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:42:20.149566+00:00
-- url     : https://prove2.me/theorems/4fa6ec96-094b-4202-8094-86b4c232c826
-- title:
--   Sensitivity separation: Endpoint40RecordCoverage proof composition 5
-- statement:
--   Proves the unchanged original statement ThreeBoundEndpoint40Records.activeTypes6_eq using the original accepted certificate checks, original kernel decisions, and small opaque structural lemmas.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordCoverage.lean; original SHA-256 c0cbb975d0b32d8bfeba818e4c16919ab962fa66af5f94a14b4cb925832b8510; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem activeTypes6_eq : activeTypes 6 = [
[0,5,5,5,5,5],
[1,2,5,5,5,5],
[1,4,5,5,5,5],
[1,5,5,5,5,5],
[1,5,5,5,5,7],
[2,2,2,5,5,5],
[2,2,4,5,5,5],
[2,2,5,5,5,5],
[2,2,5,5,5,7],
[2,3,5,5,5,5],
[2,4,4,5,5,5],
[2,4,5,5,5,5],
[2,4,5,5,5,7],
[2,5,5,5,5,5],
[2,5,5,5,5,6],
[2,5,5,5,5,7],
[2,5,5,5,7,7],
[3,4,5,5,5,5],
[3,5,5,5,5,5],
[3,5,5,5,5,7],
[4,4,4,5,5,5],
[4,4,5,5,5,5],
[4,4,5,5,5,7],
[4,5,5,5,5,5],
[4,5,5,5,5,6],
[4,5,5,5,5,7],
[4,5,5,5,7,7],
[5,5,5,5,5,5],
[5,5,5,5,5,6],
[5,5,5,5,5,7],
[5,5,5,5,6,7],
[5,5,5,5,7,7],
[5,5,5,7,7,7]] := by decide +kernel

end ThreeBoundEndpoint40Records


