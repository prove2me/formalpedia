-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
-- name    : Submission_ThreeSum_TernaryFixedDictionaries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:55.803843+00:00
-- url     : https://prove2.me/theorems/5d59672f-54cf-48fc-8c1c-efcd33e3ca31
-- title:
--   Ternary Fixed Dictionaries
-- statement:
--   Definitions and structural lemmas for Ternary Fixed Dictionaries, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev SourceRecord (L : ℕ) (α : DigitType) (I : Type*) := I × {a // a ∈ vertices L α}
def leftKey (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ℤ := -rawSource (maps r.1) false r.2.val
def rightKey (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ℤ := rawSource (maps r.1) true r.2.val
def sourceRecords (L : ℕ) (α : DigitType) (I : Type*) [Fintype I] : List (SourceRecord L α I) := by
  classical
  exact (univ : Finset (SourceRecord L α I)).toList
def outputRecords (L : ℕ) (π : DigitType) (I : Type*) [Fintype I] : List (OutputBlock L π I) := by
  classical
  exact (univ : Finset (OutputBlock L π I)).toList
def leftNative (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ZMod p :=
  TernaryCoverHashes.linearHash (TernaryCoverHashes.leftVector (fieldWord p r.2.val)) (maps r.1)
def rightNative (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ZMod p :=
  TernaryCoverHashes.linearHash (TernaryCoverHashes.rightVector (fieldWord p r.2.val)) (maps r.1)
def acceptedLeft (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (r : SourceRecord L α I) : Prop :=
  TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.leftVector
    (maps r.1) (leftNative maps r) ≤ B
def acceptedRight (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (r : SourceRecord L α I) : Prop :=
  TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.rightVector
    (maps r.1) (rightNative maps r) ≤ B
def trimmedLeftRecords (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) : List (SourceRecord L α I) := by
  classical
  exact ((univ : Finset (SourceRecord L α I)).filter (acceptedLeft maps B)).toList
def trimmedRightRecords (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) : List (SourceRecord L α I) := by
  classical
  exact ((univ : Finset (SourceRecord L α I)).filter (acceptedRight maps B)).toList
def leftNativeFiber (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (a : ZMod p) : Finset (SourceRecord L α I) := by
  classical
  exact univ.filter fun r => acceptedLeft maps B r ∧ leftNative maps r = a
variable {lim : Limits}
end ThreeSum.TernaryFixedDictionaries


