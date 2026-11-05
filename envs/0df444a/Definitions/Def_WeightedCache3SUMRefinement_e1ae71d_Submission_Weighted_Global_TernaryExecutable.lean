-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutable
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:47:21.102739+00:00
-- url     : https://prove2.me/theorems/f6689802-269f-4736-843c-70f388c2f4b7
-- title:
--   TernaryExecutable
-- statement:
--   Definitions and structural lemmas for TernaryExecutable, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryExecutable.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_main
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


