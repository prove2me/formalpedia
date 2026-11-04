-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
-- name    : Submission_ThreeSum_LightTernaryWantedBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:04:46.519525+00:00
-- url     : https://prove2.me/theorems/b559e66e-c7b6-4c5f-a8d3-f67abc9157c5
-- title:
--   Light Ternary Wanted Batch
-- statement:
--   Definitions and structural lemmas for Light Ternary Wanted Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBatch.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryWantedBatch
open Light LightTernaryWantedCanonical
open TernaryWantedLittleEndian (wantedCodes)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
def body : Stmt :=
  .set 7 (v 4) ;;
  .for 6 (v 3) (
    .call 0 [v 0,M (v 1 +' v 6),k 0,k 1,k 0,k 1,M (v 2 +' v 6),v 7,v 5] 7) ;;
  .set 0 (v 7)
def program (P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  LightTernaryWantedCanonical.program P R S raws words maps++[body]
def rows (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) : ℕ → List ℤ
  | 0 => []
  | n+1 => rows P R S J raws words maps targets positions n++
      rowCells (positions n) (wantedCodes (P : ℤ) raws words maps J (targets n) R S 0 1 0 1)
def time (P C V J n : ℕ) : ℕ :=
  n*((overhead P V+stepCost V+40)*(J+1)*C^J+100)+50
def Inv (μ : ℕ → ℤ) (P R S J targetBase positionBase n dst work : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ,
    σ=⟨frame [J,targetBase,positionBase,n,dst,work,i,
      dst+(rows P R S J raws words maps targets positions i).length],ν⟩ ∧
    Seg ν dst (rows P R S J raws words maps targets positions i) ∧ Kept μ ν dst
variable {lim : Limits}
end ThreeSum.LightTernaryWantedBatch


