-- Prove2me | Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
-- name    : D1Bound5_PairSelectedFloorWitnesses_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:39:17.512402+00:00
-- url     : https://prove2.me/theorems/dbfbfcef-4264-4cfc-b164-545a96b3542b
-- title:
--   Pair Selected Floor Witnesses
-- statement:
--   A base-32 word supplies one tag for every actual tail vertex. Tags 0--24 select one rejecting cached mask, tag 30 checks a repeated vertex, and tag 31 checks the existing integer obstruction or consumes one exact floor witness. All other tags reject. The full tail drives recursion even when the packed word is zero, so leading zero tags never omit pairs. At the end both the remaining word and the floor list must be empty. The named objects in this bundle include `pairSelectedFloorRowBool`, `pairSelectedFloorIndependentBool`, `pairSelectedFloorIndependentCertificateBool`.
-- source:
--   D1Bound5/PairSelectedFloorWitnesses.lean, lines 7-31, SHA-256 5627d261d76c8200c3ce7a8601856a8cef8aa9e7be044b0ebf81c7f060ce8b74; D1Bound5/PairSelectedFloorWitnesses.lean, lines 90-98, SHA-256 5627d261d76c8200c3ce7a8601856a8cef8aa9e7be044b0ebf81c7f060ce8b74; D1Bound5/PairSelectedFloorWitnesses.lean, lines 117-124, SHA-256 5627d261d76c8200c3ce7a8601856a8cef8aa9e7be044b0ebf81c7f060ce8b74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions
import Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions

section
namespace D1Bound5
open QuadInt

/-- A base-32 word supplies one tag for every actual tail vertex. Tags 0--24
select one rejecting cached mask, tag 30 checks a repeated vertex, and tag 31
checks the existing integer obstruction or consumes one exact floor witness.
All other tags reject. The full tail drives recursion even when the packed
word is zero, so leading zero tags never omit pairs. At the end both the
remaining word and the floor list must be empty. -/
def pairSelectedFloorRowBool {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (x : PairResidueVertex tau nu) :
    List (PairResidueVertex tau nu) → ℕ → List ℕ → Bool
  | [], code, ks => decide (code = 0 ∧ ks = [])
  | y :: ys, code, ks =>
      if code % 32 < 25 then
        pairSelectedCachedMaskRejectBool tau nu sieve x.signature y.signature (code % 32) &&
          pairSelectedFloorRowBool sieve x ys (code / 32) ks
      else if code % 32 = 30 then
        decide (x.vertex = y.vertex) && pairSelectedFloorRowBool sieve x ys (code / 32) ks
      else if code % 32 = 31 then
        if pairNegativeIntegerObstructionBool (x.vertex * y.vertex + 1) = true then
          pairSelectedFloorRowBool sieve x ys (code / 32) ks
        else match ks with
          | [] => false
          | k :: rest =>
              QuadInt.floorObstructionBool (x.vertex * y.vertex + 1) k &&
                pairSelectedFloorRowBool sieve x ys (code / 32) rest
      else false



/-- Exactly one packed word and floor list is required for each actual head.
Unmatched vertex or witness tails reject the certificate. -/
def pairSelectedFloorIndependentBool {tau nu : ℤ} (sieve : List (ℕ × ℕ)) :
    List (PairResidueVertex tau nu) → List (ℕ × List ℕ) → Bool
  | [], [] => true
  | x :: xs, (code, ks) :: rows =>
      pairSelectedFloorRowBool sieve x xs code ks &&
        pairSelectedFloorIndependentBool sieve xs rows
  | _, _ => false



/-- The accepted complete color-list coverage and signature validation are
retained exactly, followed by the selected-mask and sparse-floor check. -/
def pairSelectedFloorIndependentCertificateBool {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ)) : Bool :=
  decide (cached.map PairResidueVertex.vertex = vertices) &&
    ((cached.all fun x => decide (x.signature = pairCoordinateSignature sieve x.vertex)) &&
      pairSelectedFloorIndependentBool sieve cached rows)





end D1Bound5
end


