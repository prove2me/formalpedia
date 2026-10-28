-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
-- name    : D1Bound5_SmallPairGraphCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:28:06.274165+00:00
-- url     : https://prove2.me/theorems/310e2382-53d8-4da6-a69f-7080d300a89c
-- title:
--   Small Pair Graph Check
-- statement:
--   Filtering is performed only after the full reversible closure has been certified. Zero, anchors and small entries are retained in that closure. The named objects in this bundle include `largePairVertices`, `pairGraphTriangleFreeBool`.
-- source:
--   D1Bound5/SmallPairGraphCheck.lean, lines 10-14, SHA-256 a1fd39ac1e63a1a407d5fbedb3ad3d7599b1489a8857fc7d2c2d3c2c9b4396e6; D1Bound5/SmallPairGraphCheck.lean, lines 16-31, SHA-256 a1fd39ac1e63a1a407d5fbedb3ad3d7599b1489a8857fc7d2c2d3c2c9b4396e6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Filtering is performed only after the full reversible closure has been
certified. Zero, anchors and small entries are retained in that closure. -/
def largePairVertices {tau nu : ℤ} (a b : QuadInt tau nu)
    (vertices : List (QuadInt tau nu)) : List (QuadInt tau nu) :=
  vertices.filter fun z => decide (9 ≤ z.norm ∧ z ≠ 0 ∧ z ≠ a ∧ z ≠ b)

/-- A lazy triangle checker. The outer square edge gates the third-vertex
scan, and the proved modular prefilter rejects most huge nonsquares. -/
def pairGraphTriangleFreeBool {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) : Bool :=
  vertices.all fun a =>
    if decide (a ≠ 0) then
      vertices.all fun b =>
        if decide (b ≠ 0 ∧ a ≠ b) then
          if hasSquareRootFast sieve (a*b+1) then
            vertices.all fun c =>
              if decide (c ≠ 0 ∧ a ≠ c ∧ b ≠ c) then
                !(hasSquareRootFast sieve (a*c+1) && hasSquareRootFast sieve (b*c+1))
              else true
          else true
        else true
    else true





end D1Bound5
end


