-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
-- name    : Submission_ThreeSum_TernaryCoverLocal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:46:10.492335+00:00
-- url     : https://prove2.me/theorems/8352296a-828b-485f-a9b5-cc360825f52c
-- title:
--   Ternary Cover Local
-- statement:
--   Definitions and structural lemmas for Ternary Cover Local, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
def edgeSet (L : ℕ) (α π : DigitType) : Finset (TritWord L × TritWord L × TritWord L) := by
  classical
  exact univ.filter fun e => Edge α π e.1 e.2.1 e.2.2
abbrev LocalEdge (L : ℕ) (α π : DigitType) := {e // e ∈ edgeSet L α π}
def left {α π : DigitType} (e : LocalEdge L α π) : TritWord L := e.val.1
def right {α π : DigitType} (e : LocalEdge L α π) : TritWord L := e.val.2.1
def output {α π : DigitType} (e : LocalEdge L α π) : TritWord L := e.val.2.2
def vertices (L : ℕ) (α : DigitType) : Finset (TritWord L) := by
  classical
  exact univ.filter fun w => HasType w α
def fieldVertices (L p : ℕ) (α : DigitType) : Finset (Fin L → ZMod p) := by
  classical
  exact (vertices L α).image (fieldWord p)
def fieldLeft {α π : DigitType} (e : LocalEdge L α π) : Fin L → ZMod p :=
  fieldWord p (left e)
def fieldRight {α π : DigitType} (e : LocalEdge L α π) : Fin L → ZMod p :=
  fieldWord p (right e)
variable [Fact (Nat.Prime p)]
def leftHash {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : ZMod p :=
  linearHash (leftVector (fieldLeft e)) w
def rightHash {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : ZMod p :=
  linearHash (rightVector (fieldRight e)) w
def outputHash (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) : ZMod p :=
  linearHash (outputVector (fieldWord p q)) w
def trimmedEvents (α π : DigitType) (B : ℕ) (a b : ZMod p)
    (e : LocalEdge L α π) : Finset (Coordinate (Fin L) → ZMod p) :=
  TernaryCoverTrimming.trimmedPairEvent (fieldLeft e) (fieldRight e) a b
    (fieldVertices L p α) (fieldVertices L p α) B
def hitCount (α π : DigitType) (B : ℕ) (w : Coordinate (Fin L) → ZMod p)
    (a b : ZMod p) : ℕ :=
  HashFamily.incidenceCount (trimmedEvents α π B a b) w
def rawCap (α π : DigitType) (w : Coordinate (Fin L) → ZMod p) : ℕ := by
  classical
  exact (univ : Finset (ZMod p × ZMod p)).sup fun t =>
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) t.1 t.2
end ThreeSum.TernaryCoverLocal


