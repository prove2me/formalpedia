-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
-- name    : Submission_ThreeSum_LightBandCandidatesTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:23:02.33819+00:00
-- url     : https://prove2.me/theorems/94034c94-0ab4-48ea-9401-747a9dc663c9
-- title:
--   Light Band Candidates Table
-- statement:
--   Definitions and structural lemmas for Light Band Candidates Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesTable.lean

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesRow
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBandCandidatesTable
open Light BandCandidateRows
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
def body (pRow : ℕ) : Stmt :=
  .for 4 (v 2) (
    .call pRow [v 0 +' v 4 *' v 3,v 1 +' k 4 *' (v 4 *' v 3),v 3,v 4] 5)
def time (m n : ℕ) : ℕ := m*(LightBandCandidatesRow.time n+100)+6
def Inv (μ : ℕ → ℤ) (mode : Mode) (f : ℕ → ℕ → ℕ)
    (src dst m n i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [src,dst,m,n,i,r],ν⟩ ∧
    (∀ x < i, ∀ y < n, Seg ν (dst+4*(x*n+y)) (make mode x y (f x y)).cells) ∧
    SameOutside μ ν dst (4*(m*n))
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}
def program (mode : Mode) : Program :=
  [body 1,LightBandCandidatesRow.body 2,LightBandCandidatesCell.body mode]
end ThreeSum.LightBandCandidatesTable


