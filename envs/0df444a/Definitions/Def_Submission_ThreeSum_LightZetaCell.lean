-- Prove2me | Definitions.Def_Submission_ThreeSum_LightZetaCell
-- name    : Submission_ThreeSum_LightZetaCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:45.803603+00:00
-- url     : https://prove2.me/theorems/0da40f22-ff6d-4d98-b786-3160904f1cbc
-- title:
--   Light Zeta Cell
-- statement:
--   Definitions and structural lemmas for Light Zeta Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaCell.lean

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_Subset
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def TableAt {L : ℕ} (μ : ℕ → ℤ) (src cut : ℕ) (f : Finset (Fin L) → ℤ) : Prop :=
  ∀ S, S.card ≤ cut → μ (src+subsetRank S) = f S
def KeptExcept (μ μ' : ℕ → ℤ) (work changed : ℕ) : Prop :=
  ∀ i < work, i ≠ changed → μ' i = μ i
def body (pSetup pOffset pErase pRank : ℕ) : Stmt :=
  .set 10 (v 6 +' (v 0 +' k 1) *' (v 0 +' k 1)) ;;
  .call pSetup [v 0,v 1,v 2,v 6] 7 ;;
  .call pOffset [v 6,v 0,v 1,v 0] 8 ;;
  .set 9 (v 7 +' v 8) ;;
  .call pErase [v 0,v 3,v 2,v 0,v 10] 11 ;;
  .ite (v 11 <' v 2)
    (.call pRank [v 0,v 1 -' k 1,v 11,v 0,v 6,v 10] 12 ;;
      .call pOffset [v 6,v 0,v 1 -' k 1,v 0] 13 ;;
      .set 14 (v 12 +' v 13) ;;
      .store (v 5 +' v 9) (M (v 4 +' v 9) +' M (v 4 +' v 14)))
    (.store (v 5 +' v 9) (M (v 4 +' v 9)))
def time (L : ℕ) : ℕ := LightSubsetSetup.time L +
  LightMaskErase.time L + rankTime L + 2*LightSubsetOffset.time L + 200
def program : Program :=
  [body 1 8 9 7, LightSubsetSetup.body 2 6 7, buildBody 3 4, fillBody, rowBody 5,
    LightArray.linearBody, powTableBody, rankBody 7, LightSubsetOffset.body, LightMaskErase.body 9]
end ThreeSum.LightZetaCell


