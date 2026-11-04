-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
-- name    : Submission_ThreeSum_TernaryCanonicalDictionaries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:12.155489+00:00
-- url     : https://prove2.me/theorems/276f43db-158c-4996-916c-93b684a9f90c
-- title:
--   Ternary Canonical Dictionaries
-- statement:
--   Definitions and structural lemmas for Ternary Canonical Dictionaries, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean

import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
def records (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) : List (SourceRecord L α I) :=
  if right then trimmedRightRecords maps B else trimmedLeftRecords maps B
def native (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ℤ :=
  ((if right then rightNative maps r else leftNative maps r).val : ℕ)
def wordCode (r : SourceRecord L α I) : ℤ :=
  (TernaryAddresses.code (TernaryBankEnumeration.wordList r.2.val) : ℕ)
def mapCode (r : SourceRecord L α I) : ℤ := ((Fintype.equivFin I r.1).val : ℕ)
variable {lim : Limits}
end ThreeSum.TernaryCanonicalDictionaries


