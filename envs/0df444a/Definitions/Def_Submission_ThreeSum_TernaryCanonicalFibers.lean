-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
-- name    : Submission_ThreeSum_TernaryCanonicalFibers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:33.700181+00:00
-- url     : https://prove2.me/theorems/1b4d6023-8dde-4464-90cf-631003bc86b4
-- title:
--   Ternary Canonical Fibers
-- statement:
--   Definitions and structural lemmas for Ternary Canonical Fibers, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
def rightNativeFiber (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (a : ZMod p) : Finset (SourceRecord L α I) := by
  classical
  exact univ.filter fun r => acceptedRight maps B r ∧ rightNative maps r = a
end ThreeSum.TernaryCanonicalFibers


