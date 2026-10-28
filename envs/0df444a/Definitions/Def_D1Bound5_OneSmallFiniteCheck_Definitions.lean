-- Prove2me | Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
-- name    : D1Bound5_OneSmallFiniteCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:30.89999+00:00
-- url     : https://prove2.me/theorems/49023879-0993-426d-9e13-ca9bc0c1be9c
-- title:
--   One Small Finite Check
-- statement:
--   Ordered coordinates retain which anchor is small. The named objects in this bundle include `firstPairCoordinates`, `FirstPairNorms`, `instDecidableFirstPairNorms`, `firstPairClassifiedBool`, `oneSmallThirdCoveredBool`, `oneSmallFourthGrowthBool`.
-- source:
--   D1Bound5/OneSmallFiniteCheck.lean, lines 50-52, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55; D1Bound5/OneSmallFiniteCheck.lean, lines 54-57, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55; D1Bound5/OneSmallFiniteCheck.lean, lines 59-61, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55; D1Bound5/OneSmallFiniteCheck.lean, lines 63-74, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55; D1Bound5/OneSmallFiniteCheck.lean, lines 107-115, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55; D1Bound5/OneSmallFiniteCheck.lean, lines 130-139, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt





/-- Ordered coordinates retain which anchor is small. -/
def firstPairCoordinates {tau nu : ℤ} (a b : QuadInt tau nu) :
    (ℤ × ℤ) × (ℤ × ℤ) := ((a.re,a.im),(b.re,b.im))

/-- Exact first-pair size restrictions after the analytic region reduction. -/
def FirstPairNorms {tau nu : ℤ} (a b : QuadInt tau nu) : Prop :=
  (a.norm = 1 ∧ 9 ≤ b.norm ∧ b.norm ≤ 63) ∨
  (a.norm = 2 ∧ 9 ≤ b.norm ∧ b.norm ≤ 15)

instance {tau nu : ℤ} (a b : QuadInt tau nu) : Decidable (FirstPairNorms a b) := by
  unfold FirstPairNorms
  infer_instance

def firstPairClassifiedBool {tau nu : ℤ}
    (small roots : List (QuadInt tau nu))
    (rows : List ((ℤ × ℤ) × (ℤ × ℤ))) : Bool :=
  small.all fun a =>
    if decide (a ≠ 0) then
      roots.all fun q =>
        let b := pairSeedCandidate a q
        if decide (q*q = a*b+1 ∧ FirstPairNorms a b) then
          decide ((a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨
            firstPairCoordinates a b ∈ rows)
        else true
    else true



/-- The full third-entry disk is small enough to check directly. -/
def oneSmallThirdCoveredBool {tau nu : ℤ} (a b : QuadInt tau nu)
    (diskEntries allowed : List (QuadInt tau nu)) : Bool :=
  diskEntries.all fun s =>
    if decide (b.norm ≤ s.norm ∧ s ≠ a ∧ s ≠ b) then
      if hasSquareRoot (a*s+1) && hasSquareRoot (b*s+1) then
        decide (s ∈ allowed)
      else true
    else true



/-- No intermediate or final nonzero/distinctness condition is needed here. -/
def oneSmallFourthGrowthBool {tau nu : ℤ} (a b s : QuadInt tau nu)
    (cutoff : ℤ) (roots : List (QuadInt tau nu)) : Bool :=
  roots.all fun q =>
    let z := pairSeedCandidate a q
    if decide (q*q = a*z+1 ∧ z.norm < cutoff) then
      if hasSquareRoot (b*z+1) && hasSquareRoot (s*z+1) then
        decide (z.norm ≤ 4*b.norm*s.norm)
      else true
    else true



end D1Bound5
end


