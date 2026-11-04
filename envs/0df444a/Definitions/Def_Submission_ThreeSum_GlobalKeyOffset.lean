-- Prove2me | Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
-- name    : Submission_ThreeSum_GlobalKeyOffset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:44:41.721947+00:00
-- url     : https://prove2.me/theorems/ba79431c-ad3a-4733-aa8b-b117e15efcdb
-- title:
--   Global Key Offset
-- statement:
--   Definitions and structural lemmas for Global Key Offset, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalRecords_nodup
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_mem_globalRecords

set_option autoImplicit false
namespace ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000
noncomputable def recordEquiv (h J : ℕ) : Fin (globalRecords h J).length ≃ GlobalOutput h J :=
  Equiv.ofBijective (globalRecords h J).get
    ⟨(globalRecords_nodup h J).injective_get,fun q => List.mem_iff_get.mp (mem_globalRecords h J q)⟩
def wantedCount (p : ℕ) (left : List ℤ) (h J : ℕ) (d : ℤ) : ℕ :=
  ∑ i : Fin left.length, ∑ q : GlobalOutput h J,
    if (globalKey q : ZMod p)-(left.getD i.val 0 : ZMod p)=(d : ZMod p) then 1 else 0
def selected (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) : ℕ :=
  LightOriginalOffset.selected p (fun i => left.getD i 0)
    (fun i => (globalKeys h J).getD i 0) left.length (globalKeys h J).length
end ThreeSum.GlobalKeyOffset


