-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
-- name    : Submission_Weighted_Global_LightTernaryPrefixInit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:00:42.923361+00:00
-- url     : https://prove2.me/theorems/6f78185b-007d-4ee3-b177-32fc282f5a21
-- title:
--   Light Ternary Prefix Init
-- statement:
--   Definitions and structural lemmas for Light Ternary Prefix Init, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixInit.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPhases
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixInit
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixPhases
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def Initialized (C : Config) (seed : ℕ) (values : List ℤ) (μ ν : ℕ→ℤ) : Prop :=
  Seg ν seed values ∧ (∀i<C.nB,ν (C.Bold+i)=0) ∧ (∀i<C.nC,ν (C.Cold+i)=0) ∧
    (∀i<C.nO,ν (C.Oold+i)=0) ∧ (∀i<C.J,ν (C.catalog+i)=0) ∧
    (∀x,(x<seed ∨ seed+48≤x)→(x<C.Bold ∨ C.Oold+C.nO≤x)→
      (x<C.catalog ∨ C.catalog+C.J≤x)→ν x=μ x)
def time (C : Config) (rounds T : ℕ) : ℕ :=
  copyTime 48+LightTernaryInitialKeys.time C.nB C.nC C.nO+fillTime C.J+LightWeightedGlobalPrefixLoop.time rounds T+1000
end ThreeSum.LightWeightedGlobalPrefixInit


