-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandHost
-- name    : Submission_ThreeSum_LightSourceBandHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:18:57.850996+00:00
-- url     : https://prove2.me/theorems/0f48e775-df26-4c5b-9648-e82e761212bd
-- title:
--   Light Source Band Host
-- statement:
--   Definitions and structural lemmas for Light Source Band Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHost.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceBandHost
open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def occurrenceBase (base NL NR g h J : ℕ) : ℕ :=
  SourceBandPairData.next base NL NR g (modulus h J)
def bankHeader (base NL NR g h J : ℕ) : ℕ :=
  occurrenceBase base NL NR g h J+LightBlockSourceCatalog.count h J*J
def finish (base NL NR g h J cut : ℕ) : ℕ :=
  SourceBandBankData.finish (bankHeader base NL NR g h J) NL NR g h J cut
def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceBandPair.space base NL NR g p (modulus h J) U D)
    (LightSourceBandBanks.space (bankHeader base NL NR g h J) NL NR g h J cut)
def word (NL NR g p h J U D : ℕ) : ℕ :=
  max (LightSourceBandPair.word NL NR g p (modulus h J) U D)
    (LightSourceBandBanks.word NL NR h J)
def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  LightSourceBandPair.time NL NR g p (modulus h J) U D+
    LightSourceBandBanks.time NL NR g h J cut+500
def body (pPair pBanks : ℕ) : Stmt :=
  .call pPair [v 11,v 12,v 13,v 14,v 15,v 16,v 6,v 17,v 18] 23 ;;
  .set 24 (v 23 +' v 20 *' v 0) ;;
  .call pBanks [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 23,v 7,v 8,v 9,v 10,v 18,v 24,
    v 19,v 20,v 21,v 22] 25 ;;
  .set 0 (v 25)
structure Procs (P : Program) (pMain : ℕ) where
  pPair : ℕ
  pBanks : ℕ
  pair : LightSourceBandPair.Procs P pPair
  banks : LightSourceBandBanks.Procs P pBanks
  main : P[pMain]?=some (body pPair pBanks)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandHost


