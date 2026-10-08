-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinusAPI_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinusAPI_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:04:58.285707+00:00
-- url     : https://prove2.me/theorems/c6bea81c-dd53-40d5-a104-237f247c4c0b
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityMinusAPI source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityMinusAPI

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityMinusAPI
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityAPI_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinus_p0

set_option autoImplicit false




/-!
# Evaluation API for the negative infinity embedding of the N13 sextic
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

@[simp] theorem functionFieldToLaurentMinus_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurentMinus K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurentMinus_injective K) z

@[simp] theorem coordinateToLaurentMinus_xClass (p : K[X]) :
    coordinateToLaurentMinus K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((N13Infinity.parameter K)⁻¹) := by
  change algebraicToLaurentMinus K
      (N13Infinity.coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [N13Infinity.coordinateToAlgebraic_xClass]
  unfold algebraicToLaurentMinus
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeriesMinus K)]
  exact DFunLike.congr_fun (N13Infinity.ratToLaurent_comp_algebraMap K) p

@[simp] theorem coordinateToLaurentMinus_scalar (c : K) :
    coordinateToLaurentMinus K
      (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurentMinus K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurentMinus_xClass]
  simp

def coordinateConstUnitMinus (c : Kˣ) : (N13Mumford.CoordinateRing K)ˣ :=
  Units.map (algebraMap K (N13Mumford.CoordinateRing K)) c

def functionConstUnitMinus (c : Kˣ) : (N13Mumford.FunctionField K)ˣ :=
  Units.map
    (algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K))
    (coordinateConstUnitMinus K c)

@[simp] theorem functionFieldToLaurentMinus_functionConstUnit (c : Kˣ) :
    functionFieldToLaurentMinus K (functionConstUnitMinus K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurentMinus K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurentMinus_algebraMap, coordinateToLaurentMinus_scalar]

@[simp] theorem ordPlus_functionConstUnitMinus (c : Kˣ) :
    (negativeInfinityOrder K).ordPlus (functionConstUnitMinus K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurentMinus K
        (functionConstUnitMinus K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurentMinus_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]

@[simp] theorem principalIdeal_functionConstUnitMinus (c : Kˣ) :
    toPrincipalIdeal (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K) (functionConstUnitMinus K c) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton
      (N13Mumford.CoordinateRing K)⁰
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (coordinateConstUnitMinus K c : N13Mumford.CoordinateRing K)) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨(coordinateConstUnitMinus K c)⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul]
  change algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K)
      (((coordinateConstUnitMinus K c)⁻¹ :
          (N13Mumford.CoordinateRing K)ˣ) * coordinateConstUnitMinus K c :
        (N13Mumford.CoordinateRing K)ˣ) = 1
  simp

theorem ySeriesMinus_order :
    (ySeriesMinus K).order = (N13Infinity.ySeries K).order := by
  rw [ySeriesMinus_eq_neg, HahnSeries.order_neg]

end

end MazurProof.N13InfinityMinus

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

private theorem wSeries_coeff_zero :
    (wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, sqrtReverseF_constantCoeff]

private theorem wSeries_ne_zero : wSeries K ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun z : LaurentSeries K => z.coeff (0 : ℤ)) h
  simp [wSeries_coeff_zero] at hcoeff

/-- The square-root factor in the Laurent expansion is a unit at infinity. -/
theorem wSeries_order : (wSeries K).order = 0 := by
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by simp [wSeries_coeff_zero])
  · rw [HahnSeries.le_order_iff_forall (wSeries_ne_zero K)]
    intro j hj
    change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff j = 0
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image]
    rintro n ⟨_, hn⟩
    have hnon : (0 : ℤ) ≤ (Nat.castOrderEmbedding n : ℤ) := by
      change (0 : ℤ) ≤ (n : ℤ)
      omega
    rw [hn] at hnon
    omega

/-- Both branches have a pole of order three at their respective infinities. -/
theorem ySeries_order : (ySeries K).order = -3 := by
  rw [ySeries]
  have hp : (parameter K)⁻¹ ^ 3 = HahnSeries.single (-3 : ℤ) 1 := by
    simp [parameter, HahnSeries.inv_single, HahnSeries.single_pow]
  rw [hp, HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero)
    (wSeries_ne_zero K), HahnSeries.order_single one_ne_zero, wSeries_order]
  norm_num

end

end MazurProof.N13Infinity

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem ySeriesMinus_order_eq_neg_three : (ySeriesMinus K).order = -3 := by
  rw [ySeriesMinus_order, N13Infinity.ySeries_order]

end

end MazurProof.N13InfinityMinus


