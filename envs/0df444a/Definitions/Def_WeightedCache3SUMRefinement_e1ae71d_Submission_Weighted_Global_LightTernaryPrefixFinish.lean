-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixFinish
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixFinish
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:51:56.748144+00:00
-- url     : https://prove2.me/theorems/162e5e51-4bbf-44f3-a435-30ac8599c48d
-- title:
--   LightTernaryPrefixFinish
-- statement:
--   Definitions and structural lemmas for LightTernaryPrefixFinish, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixFinish.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixProgramLibrary
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixFinish
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def body : Stmt :=
  .call 178 seedArgs 26 ;;
  .call 188 [M (v 3 +' k 9),M (v 3 +' k 8),M (v 3 +' k 10),
    M (v 3 +' k 13),M (v 3 +' k 12),M (v 3 +' k 14),
    M (v 3 +' k 17),M (v 3 +' k 16),M (v 3 +' k 18)] 26 ;;
  .call 189 [M (v 3 +' k 47),M (v 3 +' k 3),v 19 *' v 11] 26 ;;
  .set 0 (v 19)
def header (C : Config) (n dB dC dP tB tC tP newSpan : ℕ) : List ℤ :=
  LightWeightedGlobalSeedController.args (withSeed C 0).argv n dB dC dP tB tC tP newSpan
structure Layout (C : Config) (lim : Limits) (seed rows newSpan : ℕ) : Prop where
  seedEnd : seed+48≤C.Bold
  BC : C.Bold+C.nB≤C.Cold
  CO : C.Cold+C.nC≤C.Oold
  OB : C.Oold+C.nO≤C.Bnew
  OC : C.Oold+C.nO≤C.Cnew
  OO : C.Oold+C.nO≤C.Onew
  Bspace : C.Bnew+C.nB≤lim.space
  Cspace : C.Cnew+C.nC≤lim.space
  Ospace : C.Onew+C.nO≤lim.space
  keysSpan : C.Oold+C.nO≤C.catalog
  spanApart : C.catalog+rows*C.J≤newSpan
  spanSpace : newSpan+rows*C.J≤lim.space
def Committed (C : Config) (rows newSpan : ℕ) (ξ ν : ℕ→ℤ) : Prop :=
  Kept ξ ν C.Bold ∧
  (∀i<C.nB, ν (C.Bold+i)=ξ (C.Bnew+i)) ∧
  (∀i<C.nC, ν (C.Cold+i)=ξ (C.Cnew+i)) ∧
  (∀i<C.nO, ν (C.Oold+i)=ξ (C.Onew+i)) ∧
  (∀k<rows, ∀i<C.J, ν (C.catalog+C.J*k+i)=ξ (newSpan+C.J*k+i)) ∧
  (∀x, (x<C.Bold ∨ C.Oold+C.nO≤x)→(x<C.catalog ∨ C.catalog+rows*C.J≤x)→ν x=ξ x)
def time (C : Config) (n seedTime rows : ℕ) : ℕ :=
  LightWeightedGlobalSeedController.time n seedTime (LightSpanCatalogStep.time C.J C.p C.catalogRows)+
    LightTernaryCommitKeys.time C.nB C.nC C.nO+copyTime (rows*C.J)+5000
end ThreeSum.LightWeightedGlobalPrefixFinish
end
end WeightedCache3SUMRefinement_e1ae71d


