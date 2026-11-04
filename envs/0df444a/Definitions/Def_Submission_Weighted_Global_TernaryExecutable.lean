-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryExecutable
-- name    : Submission_Weighted_Global_TernaryExecutable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:49:49.679239+00:00
-- url     : https://prove2.me/theorems/a89c8c6c-4ec0-4f46-be00-23fa4b6f6562
-- title:
--   Ternary Executable
-- statement:
--   Definitions and structural lemmas for Ternary Executable, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutable.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalExecutable
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCanonicalDictionaries
variable {p m F : ℕ} [Fact p.Prime]
def leftRecords (maps : Fin F→Weight m p) (cap : ℕ) :=records (α := fixedAlpha m) false maps cap
def rightRecords (maps : Fin F→Weight m p) (cap : ℕ) :=records (α := fixedAlpha m) true maps cap
def reporting (maps : Fin F→Weight m p) (cap K : ℕ) : Program :=
  LightWeightedGlobalPreparedPostSelection.closedProgram
    ((leftRecords maps cap).map (native false maps)) ((leftRecords maps cap).map wordCode)
    ((leftRecords maps cap).map mapCode) ((rightRecords maps cap).map (native true maps))
    ((rightRecords maps cap).map wordCode) ((rightRecords maps cap).map mapCode) (2*p^K)
def reportingMain (K : ℕ) :=139*(TernaryMomentSchedule.channels (2*(2*p^K)+1)).length+24
def color (maps : Fin F→Weight m p) (τ cap M radix K D E : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) : Program :=
  LightWeightedGlobalColoredSolver.program radix D E K radix
    (p^(2*K)) (9*F*M*(WeightedGlobalGoodOutputCatalog.Rbar m)^K)
    (2^((fixedPi m 2)*K)) p (4^(fixedLength m)) F m (fixedAlpha m 2)
    (WeightedGlobalArenaSourceSetup.alphaRank m) (TernaryCodeSemantics.address Q.val) (fixedLength m)
    (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
    (WeightedGlobalGoodOutputCatalog.mapCodes maps τ)
    ((leftRecords maps cap).map (native false maps)) ((leftRecords maps cap).map wordCode)
    ((leftRecords maps cap).map mapCode) ((rightRecords maps cap).map (native true maps))
    ((rightRecords maps cap).map wordCode) ((rightRecords maps cap).map mapCode)
    (reporting maps cap K) (reportingMain (p := p) K)
def colorMain (K : ℕ) :=252+(reportingMain (p := p) K+1)
def program (maps : Fin F→Weight m p) (τ cap M radix K D E κ : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) : Program :=
  LightWeightedGlobalFastProgram.program M radix p K κ (color maps τ cap M radix K D E Q)
    (colorMain (p := p) K)
def main (K : ℕ) :=54+(colorMain (p := p) K+1)
end ThreeSum.WeightedGlobalExecutable


