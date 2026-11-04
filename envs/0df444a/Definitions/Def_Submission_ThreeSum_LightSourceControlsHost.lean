-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceControlsHost
-- name    : Submission_ThreeSum_LightSourceControlsHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:39:25.451189+00:00
-- url     : https://prove2.me/theorems/9f6434bd-036c-4313-8b27-eab187757a41
-- title:
--   Light Source Controls Host
-- statement:
--   Definitions and structural lemmas for Light Source Controls Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsHost.lean

import Definitions.Def_Submission_ThreeSum_LightSourceControlsProgram
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceControlsHost
open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def sourceBase (base : ℕ) : ℕ := base+3
def finish (base NL NR g h J cut : ℕ) : ℕ :=
  LightSourceBandHost.finish (sourceBase base) NL NR g h J cut
def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceControls.space (sourceBase base) h J)
    (LightSourceBandHost.space (sourceBase base) NL NR g p h J cut U D)
def word (NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceControls.word h J cut) (LightSourceBandHost.word NL NR g p h J U D)
def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  LightSourceControls.time h J+LightSourceBandHost.time NL NR g p h J cut U D+500
def body (pControls pSource : ℕ) : Stmt :=
  .set 20 (v 18 +' k 3) ;;
  .call pControls [v 0,v 1,v 3,v 5,v 19,v 6,v 18,v 20] 21 ;;
  .set 22 (M (v 18)) ;;
  .set 23 (M (v 18 +' k 1)) ;;
  .call pSource [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,
    v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 20,v 22,v 23,v 19,v 21] 24 ;;
  .set 0 (v 24)
structure Procs (P : Program) (pMain : ℕ) where
  pControls : ℕ
  pSource : ℕ
  controls : LightSourceControls.Procs P pControls
  source : LightSourceBandHost.Procs P pSource
  main : P[pMain]?=some (body pControls pSource)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceControlsHost


