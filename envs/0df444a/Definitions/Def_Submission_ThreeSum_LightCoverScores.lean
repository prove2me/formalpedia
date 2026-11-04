-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCoverScores
-- name    : Submission_ThreeSum_LightCoverScores
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:29.16845+00:00
-- url     : https://prove2.me/theorems/9bf70b85-19cd-4f85-beba-0a6f011b9440
-- title:
--   Light Cover Scores
-- statement:
--   Definitions and structural lemmas for Light Cover Scores, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverScores.lean

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightCoverScores
open Light
def score (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ) (cols row : ℕ) : ℕ :=
  LightBooleanDot.dot (matrix row) active cols
def body (pDot : ℕ) : Stmt :=
  .for 5 (v 4) (
    .call pDot [v 0 +' v 5 *' v 3,v 1,v 3] 6 ;;
    .store (v 2 +' v 5) (k 0 -' v 6))
def time (rows cols : ℕ) : ℕ := rows*(LightBooleanDot.time cols+70)+6
def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (src activePtr dst rows cols i : ℕ) (σ : State) : Prop :=
  ∃ (v : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src,activePtr,dst,cols,rows,i,v],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = -(score matrix active cols j : ℤ)) ∧
    SameOutside μ μ' dst rows
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightBooleanDot.body]
end ThreeSum.LightCoverScores


