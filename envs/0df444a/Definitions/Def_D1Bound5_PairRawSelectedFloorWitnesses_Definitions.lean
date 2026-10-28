-- Prove2me | Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
-- name    : D1Bound5_PairRawSelectedFloorWitnesses_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:39:09.536533+00:00
-- url     : https://prove2.me/theorems/71af1fc9-9a4c-405b-907c-accdd13aee10
-- title:
--   Pair Raw Selected Floor Witnesses
-- statement:
--   The same aligned selected-mask lookup, evaluated by the exactly equal natural-arithmetic mask predicate. Missing entries still reject. The named objects in this bundle include `pairSelectedCachedMaskNatRejectBool`, `pairRawSelectedFloorRowBool`, `pairRawSelectedFloorIndependentBool`, `pairRawSelectedFloorIndependentCertificateBool`.
-- source:
--   D1Bound5/PairRawSelectedFloorWitnesses.lean, lines 6-12, SHA-256 16663ee7ed18799dce07207a0b374d05787f04c1c37fca43ad73b4907ad0a013; D1Bound5/PairRawSelectedFloorWitnesses.lean, lines 27-48, SHA-256 16663ee7ed18799dce07207a0b374d05787f04c1c37fca43ad73b4907ad0a013; D1Bound5/PairRawSelectedFloorWitnesses.lean, lines 64-71, SHA-256 16663ee7ed18799dce07207a0b374d05787f04c1c37fca43ad73b4907ad0a013; D1Bound5/PairRawSelectedFloorWitnesses.lean, lines 88-95, SHA-256 16663ee7ed18799dce07207a0b374d05787f04c1c37fca43ad73b4907ad0a013. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairResidueMaskNat_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions

section
namespace D1Bound5

/-- The same aligned selected-mask lookup, evaluated by the exactly equal
natural-arithmetic mask predicate. Missing entries still reject. -/
def pairSelectedCachedMaskNatRejectBool (tau nu : ℤ) (sieve : List (ℕ × ℕ))
    (xs ys : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  match sieve[i]?, xs[i]?, ys[i]? with
  | some (k, mask), some u, some v => !pairResidueMaskNatBool tau nu k mask u v
  | _, _, _ => false



/-- A copy of the accepted packed row whose only change is the selected
mask evaluation. Tail traversal, tag decoding, duplicate checks, integer
guards, floor values, and all exhaustion conditions are identical. -/
def pairRawSelectedFloorRowBool {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (x : PairResidueVertex tau nu) :
    List (PairResidueVertex tau nu) → ℕ → List ℕ → Bool
  | [], code, ks => decide (code = 0 ∧ ks = [])
  | y :: ys, code, ks =>
      if code % 32 < 25 then
        pairSelectedCachedMaskNatRejectBool tau nu sieve x.signature y.signature (code % 32) &&
          pairRawSelectedFloorRowBool sieve x ys (code / 32) ks
      else if code % 32 = 30 then
        decide (x.vertex = y.vertex) && pairRawSelectedFloorRowBool sieve x ys (code / 32) ks
      else if code % 32 = 31 then
        if pairNegativeIntegerObstructionBool (x.vertex * y.vertex + 1) = true then
          pairRawSelectedFloorRowBool sieve x ys (code / 32) ks
        else match ks with
          | [] => false
          | k :: rest =>
              QuadInt.floorObstructionBool (x.vertex * y.vertex + 1) k &&
                pairRawSelectedFloorRowBool sieve x ys (code / 32) rest
      else false



/-- Exact copy of the accepted outer lockstep traversal. -/
def pairRawSelectedFloorIndependentBool {tau nu : ℤ} (sieve : List (ℕ × ℕ)) :
    List (PairResidueVertex tau nu) → List (ℕ × List ℕ) → Bool
  | [], [] => true
  | x :: xs, (code, ks) :: rows =>
      pairRawSelectedFloorRowBool sieve x xs code ks &&
        pairRawSelectedFloorIndependentBool sieve xs rows
  | _, _ => false



/-- Full original coverage and signature validation, with raw arithmetic
used only in the exactly equal selected-mask evaluation. -/
def pairRawSelectedFloorIndependentCertificateBool {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ)) : Bool :=
  decide (cached.map PairResidueVertex.vertex = vertices) &&
    ((cached.all fun x => decide (x.signature = pairCoordinateSignature sieve x.vertex)) &&
      pairRawSelectedFloorIndependentBool sieve cached rows)





end D1Bound5
end


