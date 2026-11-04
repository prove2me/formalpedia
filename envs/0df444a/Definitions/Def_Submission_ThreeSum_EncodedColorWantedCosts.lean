-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
-- name    : Submission_ThreeSum_EncodedColorWantedCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:31:43.837195+00:00
-- url     : https://prove2.me/theorems/310dd45b-87a0-47d8-a32e-de04f4f9bc3e
-- title:
--   Encoded Color Wanted Costs
-- statement:
--   Definitions and structural lemmas for Encoded Color Wanted Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
set_option autoImplicit false
namespace ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
def time (P M h J U len : ℕ) : ℕ :=
  LightCoverKeys.time h J+LightRawAKeys.time len U+
    LightOriginalOffset.time M (3*len) (LightGuardedWanted.totalKeys h J)
      (LightGuardedWanted.keyBound P h J)+
    2000*(3*len+LightGuardedWanted.totalKeys h J+M+
      3*len*LightGuardedWanted.totalKeys h J/M+1)*
      (Nat.log 2 (LightGuardedWanted.keyBound P h J+1)+Nat.log 2 (M+M+1)+1)+400
def sourceBase (free M h J len : ℕ) : ℕ :=
  LightWantedSetup.pairBase (LightGuardedWanted.wantedFree free h J len)
    (3*len) (LightGuardedWanted.totalKeys h J) M+
    2*(3*len*LightGuardedWanted.totalKeys h J/M)
def space (free P M h J U len : ℕ) : ℕ :=
  max (LightCoverKeys.space free h J)
    (max (LightRawAKeys.space (LightCoverKeyData.keyEnd free h J) len U)
      (max (LightOriginalOffset.space (LightGuardedWanted.wantedFree free h J len)
        M (3*len+LightGuardedWanted.totalKeys h J) (LightGuardedWanted.keyBound P h J))
        (max (LightSourceResidues.space
          (LightWantedSetup.pairBase (LightGuardedWanted.wantedFree free h J len)
            (3*len) (LightGuardedWanted.totalKeys h J) M)
          M (LightGuardedWanted.keyBound P h J) M)
          (sourceBase free M h J len))))
end ThreeSum.EncodedColorWantedCosts


