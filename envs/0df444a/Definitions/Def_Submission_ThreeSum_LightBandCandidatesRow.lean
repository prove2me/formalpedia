-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandCandidatesRow
-- name    : Submission_ThreeSum_LightBandCandidatesRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:35.842866+00:00
-- url     : https://prove2.me/theorems/a81a26d7-f91a-4e48-8fbc-18264f01341c
-- title:
--   Light Band Candidates Row
-- statement:
--   Definitions and structural lemmas for Light Band Candidates Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesRow.lean

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesCell
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandCandidatesRow
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
def body (pCell : ℕ) : Stmt :=
  .for 4 (v 2) (
    .set 5 (M (v 0 +' v 4)) ;;
    .call pCell [v 5,v 3,v 4,v 1 +' k 4 *' v 4] 6)
def time (n : ℕ) : ℕ := n*(LightBandCandidatesCell.time+100)+6
def Inv (μ : ℕ → ℤ) (mode : Mode) (f : ℕ → ℕ)
    (src dst n outer j : ℕ) (σ : State) : Prop :=
  ∃ (x r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [src,dst,n,outer,j,x,r],ν⟩ ∧
    (∀ k < j, Seg ν (dst+4*k) (make mode outer k (f k)).cells) ∧
    SameOutside μ ν dst (4*n)
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst n outer U : ℕ} {f : ℕ → ℕ}
end ThreeSum.LightBandCandidatesRow


