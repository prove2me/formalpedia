-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl003
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl003
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:33:45.358004+00:00
-- url     : https://prove2.me/theorems/92d60521-5c56-4754-aac1-577bcddfa02c
-- title:
--   Sensitivity record composition: checked_type6_28
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_28, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl002
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_28 : checkTypes tree [5,5,5,5,5,6]=true :=
  checkTypes_of_from tree [5,5,5,5,5,6] checked_type6_28_assembly_from0

end ThreeBoundEndpoint40Records


