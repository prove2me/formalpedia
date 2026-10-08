-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinus_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinus_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:01:16.629139+00:00
-- url     : https://prove2.me/theorems/b96a63a5-9d3b-4d19-b477-66db5f391e2d
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityMinus source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityMinus

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityMinus
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Infinity_p0

set_option autoImplicit false




/-!
# The negative infinity of the N13 genus-two curve

The second branch at infinity is obtained by sending `Y` to the negative of
the positive Laurent expansion.  It gives the opposite orientation datum for
the two-infinity sextic model.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def ySeriesMinus : LaurentSeries K := -(N13Infinity.ySeries K)

@[simp] theorem ySeriesMinus_eq_neg :
    ySeriesMinus K = -(N13Infinity.ySeries K) := rfl

theorem ySeriesMinus_sq :
    ySeriesMinus K ^ 2 =
      (N13Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := by
  rw [ySeriesMinus, neg_sq, N13Infinity.ySeries_sq]

theorem curvePolyRat_eval_ySeriesMinus :
    (N13Infinity.curvePolyRat K).eval₂ (N13Infinity.ratToLaurent K)
      (ySeriesMinus K) = 0 := by
  rw [N13Infinity.curvePolyRat, Polynomial.eval₂_map,
    N13Infinity.ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹)) (ySeriesMinus K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeriesMinus_sq]
  exact sub_self _

def algebraicToLaurentMinus :
    N13Infinity.AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (N13Infinity.ratToLaurent K) (ySeriesMinus K)
    (curvePolyRat_eval_ySeriesMinus K)

@[simp] theorem algebraicToLaurentMinus_root :
    algebraicToLaurentMinus K
      (AdjoinRoot.root (N13Infinity.curvePolyRat K)) = ySeriesMinus K := by
  exact AdjoinRoot.lift_root (curvePolyRat_eval_ySeriesMinus K)

theorem algebraicToLaurentMinus_injective :
    Function.Injective (algebraicToLaurentMinus K) :=
  (algebraicToLaurentMinus K).injective

def coordinateToLaurentMinus :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurentMinus K).comp (N13Infinity.coordinateToAlgebraic K)

theorem coordinateToLaurentMinus_injective :
    Function.Injective (coordinateToLaurentMinus K) :=
  (algebraicToLaurentMinus_injective K).comp
    (N13Infinity.coordinateToAlgebraic_injective K)

@[simp] theorem coordinateToLaurentMinus_yClass :
    coordinateToLaurentMinus K
      (SexticMumford.yClass (N13Mumford.model K)) = ySeriesMinus K := by
  change algebraicToLaurentMinus K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact algebraicToLaurentMinus_root K

def functionFieldToLaurentMinus :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurentMinus_injective K)

theorem functionFieldToLaurentMinus_injective :
    Function.Injective (functionFieldToLaurentMinus K) :=
  (functionFieldToLaurentMinus K).injective

def infinityOrderHomMinus :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (N13Infinity.laurentOrder K).comp
    (Units.map (functionFieldToLaurentMinus K))

def negativeInfinityOrder :
    SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHomMinus K

end

end MazurProof.N13InfinityMinus


