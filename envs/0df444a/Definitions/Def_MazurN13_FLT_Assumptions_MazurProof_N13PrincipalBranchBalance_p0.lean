-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrincipalBranchBalance_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13PrincipalBranchBalance_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:37:40.619462+00:00
-- url     : https://prove2.me/theorems/1e4a0004-10c9-4213-94e7-eec1e2013744
-- title:
--   FLT.Assumptions.MazurProof.N13PrincipalBranchBalance source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13PrincipalBranchBalance

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13PrincipalBranchBalance
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordInfinityBalance_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FunctionConjugation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordFixedUnit_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdealConjugation_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The affine principal relation between TWO products of Mumford graph ideals
forces the missing sum of the positive and negative infinity orders. The
proof multiplies by the hyperelliptic conjugate, extracts an affine unit,
and proves that the conjugation-fixed unit is a scalar. It uses no global
specialization compatibility or desired additive code equation.
-/

namespace MazurProof.N13PrincipalBranchBalance

noncomputable section
open Polynomial SexticMumford
open scoped nonZeroDivisors

universe u
variable {K : Type u} [Field K] [CharZero K]
abbrev M := N13Mumford.model K
abbrev R := N13Mumford.CoordinateRing K
abbrev F := N13Mumford.FunctionField K

theorem exists_scalar_norm_ratio
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ *
        toPrincipalIdeal R F α = mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃) :
    ∃ q : Kˣ,
      N13Infinity.functionConstUnit K q *
          (α * conjugateFunctionUnit M α) *
          xClassFunctionUnit M (D₀.u * D₁.u)
            (mul_ne_zero D₀.u_monic.ne_zero D₁.u_monic.ne_zero) =
        xClassFunctionUnit M (D₂.u * D₃.u)
          (mul_ne_zero D₂.u_monic.ne_zero D₃.u_monic.ne_zero) := by
  let αbar : Fˣ := conjugateFunctionUnit M α
  have hbar := congrArg (conjugateInvFrac M) h
  simp only [map_mul, conjugateInvFrac_mumfordIdealUnit, conjugateInvFrac_principal] at hbar
  have hnorm :
      (mumfordIdealUnit M D₀ * mumfordIdealUnit M (conjugateSemiMumford M D₀)) *
        (mumfordIdealUnit M D₁ * mumfordIdealUnit M (conjugateSemiMumford M D₁)) *
        toPrincipalIdeal R F (α * αbar) =
      (mumfordIdealUnit M D₂ * mumfordIdealUnit M (conjugateSemiMumford M D₂)) *
        (mumfordIdealUnit M D₃ * mumfordIdealUnit M (conjugateSemiMumford M D₃)) := by
    calc
      _ = (mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ * toPrincipalIdeal R F α) *
          (mumfordIdealUnit M (conjugateSemiMumford M D₀) *
            mumfordIdealUnit M (conjugateSemiMumford M D₁) * toPrincipalIdeal R F αbar) := by
        rw [map_mul]
        ac_rfl
      _ = _ := by
        rw [h]
        dsimp only [αbar]
        rw [hbar]
        ac_rfl
  have hfrac := congrArg (fun U : InvFrac M => U.val) hnorm
  simp only [Units.val_mul, coe_toPrincipalIdeal, coe_mumfordIdealUnit,
    conjugateSemiMumford_u, conjugateSemiMumford_v] at hfrac
  rw [mumfordIdeal_mul_conj_fractional M D₀,
    mumfordIdeal_mul_conj_fractional M D₁,
    mumfordIdeal_mul_conj_fractional M D₂,
    mumfordIdeal_mul_conj_fractional M D₃] at hfrac
  simp only [FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at hfrac
  change FractionalIdeal.spanSingleton R⁰
      (algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₀.u) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₁.u) *
        ((α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K))) =
    FractionalIdeal.spanSingleton R⁰
      (algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₂.u) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M D₃.u)) at hfrac
  obtain ⟨ε, he⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
  rw [Units.smul_def, Algebra.smul_def] at he
  have heq : algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (ε : N13Mumford.CoordinateRing K) *
      ((α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u))) =
      algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₂.u * D₃.u)) := by
    simp only [xClass_mul, map_mul]
    rw [← he]
    ring
  have hfixed : functionConjugateEquiv M
      ((α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u))) =
      (α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) * algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u)) := by
    simp only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, αbar, conjugateFunctionUnit_val]
    rw [functionConjugate_involutive]
    ring
  have hconj := congrArg (functionConjugateEquiv M) heq
  simp only [map_mul, functionConjugateEquiv_algebraMap, conjugate_xClass, hfixed] at hconj
  have hne : (α : N13Mumford.FunctionField K) * (αbar : N13Mumford.FunctionField K) *
      algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u)) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero α.ne_zero αbar.ne_zero)
    simpa only [map_zero] using (IsFractionRing.injective (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K)).ne
      (xClass_ne_zero M (mul_ne_zero D₀.u_monic.ne_zero D₁.u_monic.ne_zero))
  have hε : conjugate M (ε : N13Mumford.CoordinateRing K) = ε := by
    apply IsFractionRing.injective (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K)
    apply mul_right_cancel₀ hne
    exact hconj.trans heq.symm
  obtain ⟨q, hq⟩ := fixed_coordinate_unit_is_scalar M ε hε
  refine ⟨q, ?_⟩
  apply Units.ext
  change algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K)
      (Units.map (algebraMap K (N13Mumford.CoordinateRing K)).toMonoidHom q : N13Mumford.CoordinateRing K) *
        ((α : N13Mumford.FunctionField K) * (conjugateFunctionUnit M α : N13Mumford.FunctionField K)) *
        algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₀.u * D₁.u)) =
      algebraMap (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) (xClass M (D₂.u * D₃.u))
  rw [← hq]
  simpa only [mul_assoc, αbar] using heq

/-- Exact degree balance for the two infinity orders of the actual common
principal multiplier between two tensor products of graph ideals. -/
theorem principal_branch_orders_sum
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ *
        toPrincipalIdeal R F α = mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃) :
    Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) +
        Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) =
      (D₀.u.natDegree : ℤ) + D₁.u.natDegree - D₂.u.natDegree - D₃.u.natDegree := by
  obtain ⟨q, hq⟩ := exists_scalar_norm_ratio D₀ D₁ D₂ D₃ α h
  have ho := congrArg
    (fun z : Fˣ => Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus z)) hq
  simp only [map_mul, toAdd_mul, N13Infinity.ordPlus_functionConstUnit,
    toAdd_one, zero_add,
    N13FunctionConjugation.positive_order_conjugate_eq_negative,
    N13MumfordInfinityBalance.ordPlus_xClassFunctionUnit] at ho
  rw [Polynomial.natDegree_mul D₀.u_monic.ne_zero D₁.u_monic.ne_zero,
    Polynomial.natDegree_mul D₂.u_monic.ne_zero D₃.u_monic.ne_zero,
    Nat.cast_add, Nat.cast_add] at ho
  omega

end
end MazurProof.N13PrincipalBranchBalance


