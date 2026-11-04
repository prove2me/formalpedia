-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryJointType
-- name    : Submission_ThreeSum_TernaryJointType
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:52.985198+00:00
-- url     : https://prove2.me/theorems/2836adde-e31d-4451-af15-341c9d8ea6b3
-- title:
--   Ternary Joint Type
-- statement:
--   Definitions and structural lemmas for Ternary Joint Type, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.TernaryJointType
open Finset
abbrev TritWord (L : ℕ) := Fin L → Fin 3
abbrev DigitType := Fin 3 → ℕ
def digitCount {L : ℕ} (w : TritWord L) (d : Fin 3) : ℕ :=
  ∑ i : Fin L, if w i = d then 1 else 0
def HasType {L : ℕ} (w : TritWord L) (t : DigitType) : Prop :=
  ∀ d, digitCount w d = t d
def PointwiseSum {L : ℕ} (a b q : TritWord L) : Prop :=
  ∀ i, (a i).val + (b i).val = (q i).val
def Edge {L : ℕ} (α π : DigitType) (a b q : TritWord L) : Prop :=
  HasType a α ∧ HasType b α ∧ HasType q π ∧ PointwiseSum a b q
def jointCount {L : ℕ} (a b : TritWord L) (u v : Fin 3) : ℕ :=
  ∑ i : Fin L, if a i = u ∧ b i = v then 1 else 0
def fieldWord {L : ℕ} (p : ℕ) (w : TritWord L) : Fin L → ZMod p :=
  fun i => ((w i).val : ZMod p)
namespace CertifiedParameters
def pi0 : ℚ := 81204746 / 100000000
def pi1 : ℚ := 15860450 / 100000000
def pi2 : ℚ := 2934804 / 100000000
def alpha0 : ℚ := 90113239 / 100000000
def alpha1 : ℚ := 8908493 / 100000000
def alpha2 : ℚ := 978268 / 100000000
def deficit : ℚ := 1344861 / 100000000
def bankY : ℚ := 1816256201 / 10000000000
def queryZ : ℚ := 752397677 / 10000000000
def target192028 : ℚ := 48007 / 25000
def target1921 : ℚ := 19203 / 10000
end CertifiedParameters
end ThreeSum.TernaryJointType


