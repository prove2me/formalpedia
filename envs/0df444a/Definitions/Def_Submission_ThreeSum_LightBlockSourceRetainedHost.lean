-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
-- name    : Submission_ThreeSum_LightBlockSourceRetainedHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:02:59.658239+00:00
-- url     : https://prove2.me/theorems/d4ecce64-5b47-459b-bdc9-3919cbe3635b
-- title:
--   Light Block Source Retained Host
-- statement:
--   Definitions and structural lemmas for Light Block Source Retained Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedHost.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourcePreparation
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCoverInput
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBlockSourceRetainedHost
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LightSubsetAddress LightPascal LocalCoverBounds BlockSourceFlags
open BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 4000000
set_option maxRecDepth 14000
def body (pEnum pPrepare pStages : ℕ) : Stmt :=
  .call pEnum [v 0 *' v 1,v 5,v 14,v 25] 26 ;;
  .call pPrepare [v 0,v 1,v 2,v 3,v 4,v 7,v 8,v 9,v 10,v 11,v 14,v 26,
    v 15,v 16,v 17,v 18,v 19,v 23,v 24,v 25] 27 ;;
  .call pStages [v 17,v 19,v 12,v 20,v 6,v 25,v 0 *' v 1,v 5,v 22,v 26] 27 ;;
  .call pStages [v 18,v 19 +' v 26,v 13,v 21,v 6,v 25,v 0 *' v 1,v 5,v 22,v 26] 27
def time (h J cut : ℕ) : ℕ :=
  LightDownsetEnumerationSetup.time (J*(512*h)) cut+
  LightSourcePreparation.time (downsetCap (J*(512*h)) cut) J (512*h) (localPrime h)+
  LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J)+
  LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J)+500
def space (work h J : ℕ) : ℕ :=
  max (work+(J*(512*h)+1))
    (max (LightSourcePreparation.space work J (512*h) (localPrime h))
      (LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J)))
def word (NL NR h J : ℕ) : ℕ :=
  2^(J*(512*h)+1)+
  LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
    ((512*h).choose h) (localBucketCap h)+
  LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL+
  LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR
structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pDownset : ℕ
  pLayer : ℕ
  pPrepare : ℕ
  pStages : ℕ
  enumMain : P[pEnum]? = some (LightDownsetEnumerationSetup.body pPowers pDownset)
  powers : P[pPowers]? = some powTableBody
  downset : P[pDownset]? = some (LightDownsetEnumeration.body pLayer)
  layer : P[pLayer]? = some (LightSubsetEnumeration.body pLayer)
  prepare : LightSourcePreparation.Procs P pPrepare
  stages : LightSourceRetainedStages.Procs P pStages
  main : P[pMain]? = some (body pEnum pPrepare pStages)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceRetainedHost


