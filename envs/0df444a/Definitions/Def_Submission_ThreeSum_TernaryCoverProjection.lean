-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
-- name    : Submission_ThreeSum_TernaryCoverProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:53.937427+00:00
-- url     : https://prove2.me/theorems/93e9587d-3b9d-4649-aab9-c02a410054ef
-- title:
--   Ternary Cover Projection
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
def differenceCode (a b : Fin 3) : ℕ := a.val + (2 - b.val)
def marked {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Finset (Fin L) :=
  univ.filter fun i => left e i = 1 ∧ right e i = 1
def differenceFiber {L p : ℕ} (α π : DigitType) (q : Fin L → ZMod p) :
    Finset (LocalEdge L α π) :=
  univ.filter fun e => ∀ i, fieldLeft (p := p) e i - fieldRight e i = q i
def doubledCode (swap : Bool) (a b : Fin 3) : ℕ :=
  if swap then a.val + 2 * b.val else 2 * a.val + b.val
def doubledMark (swap : Bool) (a b : Fin 3) : Prop :=
  if swap then a = 2 ∧ b = 0 else a = 0 ∧ b = 2
def doubledMarked {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π) : Finset (Fin L) := by
  classical
  exact univ.filter fun i => doubledMark swap (left e i) (right e i)
def doubledAmbiguous {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π) : Finset (Fin L) :=
  univ.filter fun i => doubledCode swap (left e i) (right e i) = 2
def doubledFiber {L p : ℕ} (swap : Bool) (α π : DigitType) (q : Fin L → ZMod p) :
    Finset (LocalEdge L α π) :=
  univ.filter fun e => ∀ i, (doubledCode swap (left e i) (right e i) : ZMod p) = q i
end ThreeSum.TernaryCoverProjection


