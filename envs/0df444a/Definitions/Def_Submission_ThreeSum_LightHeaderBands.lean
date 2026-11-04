-- Prove2me | Definitions.Def_Submission_ThreeSum_LightHeaderBands
-- name    : Submission_ThreeSum_LightHeaderBands
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:39:11.83894+00:00
-- url     : https://prove2.me/theorems/c118cf92-7d01-49c6-af1e-8c8cf4515e5e
-- title:
--   Light Header Bands
-- statement:
--   Definitions and structural lemmas for Light Header Bands, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHeaderBands.lean

import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightHeaderBands
open Light ThreeSum.BandEnumeration
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
def At (μ : ℕ → ℤ) (header n : ℕ) (A : Family) : Prop :=
  μ header = (n : ℤ) ∧ μ (header+1) = (A.size : ℤ) ∧
    LightBandEnumeration.At μ (header+2) (header+2+n) A
def body (pEnumerate : ℕ) : Stmt :=
  .call pEnumerate
    [v 0 +' k 2,v 0 +' k 2 +' M (v 0),
      v 1 +' k 2,v 1 +' k 2 +' M (v 1),
      v 2 +' k 2,v 2 +' k 2 +' M (v 2),
      M (v 0 +' k 1),M (v 1 +' k 1),M (v 2 +' k 1),v 3] 0
def time (a b c : ℕ) : ℕ := LightBandEnumeration.time a b c+100
structure Procs (P : Program) (pMain : ℕ) where
  pEnumerate : ℕ
  enumerate : LightBandEnumeration.Procs P pEnumerate
  main : P[pMain]? = some (body pEnumerate)
def program : Program :=
  [body 1,LightBandEnumeration.body 2 3 4,clog2Body,powTableBody,
    LightBandTable.body 5,LightBandTable.rowBody 6,LightBandLookup.body 7,LightBandLookup.searchBody 7]
def program_procs : Procs program 0 :=
  ⟨1,⟨2,3,4,5,6,7,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightHeaderBands


