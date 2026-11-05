-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:53:40.291142+00:00
-- url     : https://prove2.me/theorems/ef07fd87-72d7-421a-94b1-d67a1ade82af
-- title:
--   TernaryArenaPairMass
-- statement:
--   Definitions and structural lemmas for TernaryArenaPairMass, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPairMass.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPairMass
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeMomentBounds
open WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
def tableWidth (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  max (localRecords maps cap false).length (localRecords maps cap true).length
def base (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  (tableWidth maps cap+1)^2*2^(fixedLength m)
def envelope (maps : Fin F→Weight m p) (cap M n : ℕ) : ℕ :=
  M^(base maps cap)*(n+1)^(2*base maps cap+2)
end ThreeSum.WeightedGlobalArenaPairMass
end
end WeightedCache3SUMRefinement_e1ae71d


