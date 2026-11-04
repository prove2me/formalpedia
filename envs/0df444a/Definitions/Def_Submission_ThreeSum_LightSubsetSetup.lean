-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSubsetSetup
-- name    : Submission_ThreeSum_LightSubsetSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:28.393247+00:00
-- url     : https://prove2.me/theorems/4f48b20e-ab06-4cbd-adff-ddfb750327a8
-- title:
--   Light Subset Setup
-- statement:
--   Definitions and structural lemmas for Light Subset Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pBuild pPowers pRank : ℕ) : Stmt :=
  .set 4 (v 3 +' (v 0 +' k 1) *' (v 0 +' k 1)) ;;
  .call pBuild [v 3,v 0] 5 ;;
  .call pPowers [v 4,v 0 +' k 1,k 2] 5 ;;
  .call pRank [v 0,v 1,v 2,v 0,v 3,v 4] 0
def time (L : ℕ) : ℕ := buildTime L + powTableTime (L+1) + rankTime L + 60
structure Procs (P : Program) (pMain pBuild pFill pRow pLinear pPowers pRank : ℕ) : Prop where
  main : P[pMain]? = some (body pBuild pPowers pRank)
  build : P[pBuild]? = some (buildBody pFill pRow)
  fill : P[pFill]? = some fillBody
  row : P[pRow]? = some (rowBody pLinear)
  linear : P[pLinear]? = some LightArray.linearBody
  powers : P[pPowers]? = some powTableBody
  rank : P[pRank]? = some (rankBody pRank)
def program : Program :=
  [body 1 5 6, buildBody 2 3, fillBody, rowBody 4,
    LightArray.linearBody, powTableBody, rankBody 6]
end ThreeSum.LightSubsetSetup


