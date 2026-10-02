-- Prove2me | Definitions.Def_Yukon_3aac3fd32187b2b2508b1f4e
-- name    : Yukon_3aac3fd32187b2b2508b1f4e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:45:37.431395+00:00
-- url     : https://prove2.me/theorems/87eac712-f179-4424-9306-31524e6261b8
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberTenPhase6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberTenPhase6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberTenPhase6814.lean
--
--   yukon-proof-operation:foundation-direct-cbbafbbf8a542e8f5bdbd6380265d2560c84cf35323ddf8436caf1c2c6b326d5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzE3OWZmOGQ3NjdjYmVjMjRjZDUxYTVlMTliMWQ3YzkxYWRmYjIwYTM4NzNlYmEyNTg5OGU3Mjg2N2JkOWVhYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWNiYmFmYmJmOGE1NDJlOGY1YmRiZDYzODAyNjVkMjU2MGM4NGNmMzUzMjNkZGY4NDM2Y2FmMWMyYzZiMzI2ZDUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zYWFjM2ZkMzIxODdiMmIyNTA4YjFmNGUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_dfd305be17d46cecd47c7820









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.Lower80889.TenPhase
open ProximityPrize.Benchmark RCN095 RCN140 RCN156 RCN234 RCN238 RCN266 RCN319
open Lower80889.Oracle Lower80889.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.TenPhase.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.TenPhase.instDecidableEqI : DecidableEq I := Classical.decEq _

/-- The exact compact10 ordering: seven distinct sources, then repeat 3,4,5. -/
def sound : ℕ → PhaseSourceSound
  | 0 => SourceSound.Phase00.sound
  | 1 => SourceSound.Phase01.sound
  | 2 => SourceSound.Phase02.sound
  | 3 => SourceSound.Phase03.sound
  | 4 => SourceSound.Phase04.sound
  | 5 => SourceSound.Phase05.sound
  | 6 => SourceSound.Phase06.sound
  | 7 => SourceSound.Phase03.sound
  | 8 => SourceSound.Phase04.sound
  | _+9 => SourceSound.Phase05.sound

def kernel (u0 u1 : I → K) (j : ℕ) : PhaseKernelRealization (sound j) u0 u1 :=
  match j with
  | 0 => SourceSound.Phase00.kernel u0 u1
  | 1 => SourceSound.Phase01.kernel u0 u1
  | 2 => SourceSound.Phase02.kernel u0 u1
  | 3 => SourceSound.Phase03.kernel u0 u1
  | 4 => SourceSound.Phase04.kernel u0 u1
  | 5 => SourceSound.Phase05.kernel u0 u1
  | 6 => SourceSound.Phase06.kernel u0 u1
  | 7 => SourceSound.Phase03.kernel u0 u1
  | 8 => SourceSound.Phase04.kernel u0 u1
  | _+9 => SourceSound.Phase05.kernel u0 u1

end
end ProximityPrize.SubmissionLower.Lower80889.TenPhase


