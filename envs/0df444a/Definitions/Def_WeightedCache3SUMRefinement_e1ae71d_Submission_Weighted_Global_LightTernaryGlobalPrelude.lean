-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPrelude
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPrelude
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:28:19.973262+00:00
-- url     : https://prove2.me/theorems/d25db347-44e3-47e7-9746-06edfd2c5179
-- title:
--   LightTernaryGlobalPrelude
-- statement:
--   Definitions and structural lemmas for LightTernaryGlobalPrelude, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryGlobalPrelude.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalGlobalPrelude
open Light
def dimensionsLibrary (M b p K : ℕ) : Program :=
  ReportingHostRelocation.program LightScales.program (LightWeightedGlobalDimensions.program M b p K)
def backendLibrary (M b p K : ℕ) : Program :=
  ReportingHostRelocation.program (dimensionsLibrary M b p K) LightWeightedGlobalExtensionBackendSetup.program
def libraries (M b p K : ℕ) : Program :=
  ReportingHostRelocation.program (backendLibrary M b p K) LightNatPower.program
def body (baseM b p K κ : ℕ) : Stmt :=
  .call 48 [v 0,k κ] 2 ;;
  .set 3 (v 1 +' k 10) ;;
  .set 4 (v 3 +' k 19) ;;
  .set 9 (v 4 +' k 4) ;;
  .call 0 [v 0,v 3] 18 ;;
  .call 5 [v 0,v 2,v 4] 18 ;;
  .set 5 (M (v 4)) ;;
  .set 6 (M (v 4 +' k 1)) ;;
  .set 7 (M (v 4 +' k 2)) ;;
  .set 8 (M (v 4 +' k 3)) ;;
  .call 47 [k p,v 7,v 8,v 6,v 9] 10 ;;
  .set 11 (v 8 *' v 8) ;;
  .set 12 (v 6 +' k 2) ;;
  .set 13 (v 9 +' k 4 *' v 7 +' k 11 +' v 11 +' v 11 *' v 12) ;;
  .set 14 (v 7 +' k p +' v 8 +' v 6 +' k 2) ;;
  .call 48 [v 14,k 6] 15 ;;
  .set 16 (v 9 +' k 100000000 *' v 15) ;;
  .store (v 1) (v 0) ;;
  .store (v 1 +' k 1) (v 2) ;;
  .store (v 1 +' k 2) (v 5) ;;
  .store (v 1 +' k 3) (v 6) ;;
  .store (v 1 +' k 4) (v 7) ;;
  .store (v 1 +' k 5) (v 8) ;;
  .store (v 1 +' k 6) (v 3) ;;
  .store (v 1 +' k 7) (v 13) ;;
  .store (v 1 +' k 8) (v 16) ;;
  .store (v 1 +' k 9) (v 10) ;;
  .set 0 (v 1)
def program (M b p K κ : ℕ) : Program := libraries M b p K++[body M b p K κ]
def params (free : ℕ) :=free+10
def dimensions (free : ℕ) :=free+29
def backend (free : ℕ) :=free+33
def finish (free d p q J : ℕ) :=backend free+LightExtensionBackendLayout.reserve d p q J
def header (n U r J d p q free c : ℕ) : List ℤ :=
  [n,U,r,J,d,q,params free,LightExtensionBackendLayout.physical (backend free) d q J,
    finish free d p q J,c+1]
end ThreeSum.LightWeightedGlobalGlobalPrelude
end
end WeightedCache3SUMRefinement_e1ae71d


