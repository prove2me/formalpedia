-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
-- name    : Submission_ThreeSum_LightEncodedColorPrime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:00:23.462528+00:00
-- url     : https://prove2.me/theorems/4c69142e-4e48-478b-b812-d5a99b6ad33f
-- title:
--   Light Encoded Color Prime
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Prime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrime.lean

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorPrime
open Light BandPartition BandCandidateRows BandRawA SourceFiniteInputs
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
def count (nA nB nC g : ℕ) : ℕ :=
  size nB g*size nC g+size nA g*size nB g+size nA g*size nC g
def moduli (A B C : List ℤ) (g : ℕ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) (y : ℕ) : ℕ → ℕ :=
  LightBandPrimeConstruction.modulus y A.length B.length C.length g
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (sortedRecords A B C g hg hsA hsB hsC)
def body (pCore : ℕ) : Stmt :=
  .set 11 (M (v 1)) ;;
  .set 12 (M (v 3)) ;;
  .set 13 (M (v 5)) ;;
  .set 14 (M (v 1 +' k 1)) ;;
  .set 15 (M (v 3 +' k 1)) ;;
  .set 16 (M (v 5 +' k 1)) ;;
  .set 17 (v 15 *' v 16 +' v 14 *' v 15 +' v 14 *' v 16) ;;
  .call pCore [v 0,v 2,v 4,v 11,v 12,v 13,v 6,v 7,v 17,v 8,v 9,v 10] 0
def program : Program := LightEncodedColorPrimeCore.program ++ [body 23]
def time (maxMod nA nB nC g M y U : ℕ) : ℕ :=
  LightEncodedColorPrimeCore.time maxMod g (count nA nB nC g) M y U+400
def word (maxMod nA nB nC g M y U : ℕ) : ℕ :=
  LightEncodedColorPrimeCore.word maxMod nA nB nC g (count nA nB nC g) M y U+
    nA+nB+nC+count nA nB nC g+100
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
end ThreeSum.LightEncodedColorPrime


