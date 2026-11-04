-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBalancedWanted
-- name    : Submission_ThreeSum_LightBalancedWanted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:08:12.869894+00:00
-- url     : https://prove2.me/theorems/f4a00130-980a-4161-a946-11a49e8daffe
-- title:
--   Light Balanced Wanted
-- statement:
--   Definitions and structural lemmas for Light Balanced Wanted, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pOffset pWanted : ℕ) : Stmt :=
  .set 6 (v 2 +' v 3) ;;
  .call pOffset [v 0,v 1,v 2,v 3,v 4,v 6,v 5] 7 ;;
  .call pWanted [v 0,v 1,v 2,v 3,v 4,v 7,v 5] 0
def program : Program := ReportingHostRelocation.program
  LightOriginalOffset.program LightWantedSetup.program ++ [body 0 24]
def time (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) : ℕ :=
  LightOriginalOffset.time M NL NR U+
    LightWantedSetup.time M left right NL NR U M
      (LightOriginalOffset.selected M left right NL NR)+100
def space (free M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) : ℕ :=
  max (LightOriginalOffset.space free M (NL+NR) U)
    (LightWantedSetup.space free M left right NL NR U M
      (LightOriginalOffset.selected M left right NL NR))
def word (M NL NR U : ℕ) : ℕ :=
  max (LightOriginalOffset.word M (NL+NR) U) (LightSourceResidues.word M M U M)
variable {lim : Limits}
end ThreeSum.LightBalancedWanted


