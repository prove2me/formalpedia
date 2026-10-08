-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerRelation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerRelation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:13:57.885623+00:00
-- url     : https://prove2.me/theorems/4bd3213f-2ba6-4be5-bca7-a2477e0091a5
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordKummerRelation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordKummerRelation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordKummerRelation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerValue_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordFixedUnit_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrincipalNumerator_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticOrientedPic_p0

set_option autoImplicit false




/-!
# Principal relations and the N13 Mumford fake-Kummer value

The value `u(θ)` must not depend on a balanced Mumford representative.  The
reason is ideal-theoretic, not a case split on the degree of `u`.

If

`I₁ (α) = I₂`,

then multiplying this relation by its hyperelliptic conjugate gives

`(u₁) (α * ᾱ) = (u₂)`.

The ratio of the two generators is therefore a unit of the affine coordinate
ring.  It is fixed by hyperelliptic conjugation, hence is a nonzero rational
scalar.  Integral numerator and conumerator witnesses then give

`u₁(θ) u₂(θ) = q z(θ)^2`.

Thus the two values have the same class modulo squares and rational scalars.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13MumfordKummerRelation

noncomputable section

open SexticMumford

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev R : Type :=
  N13Mumford.CoordinateRing ℚ

abbrev F : Type :=
  N13Mumford.FunctionField ℚ

local instance sexticAlgebraField :
    Field N13MumfordKummerValue.L :=
  N13SexticIrreducible.sexticAlgebraField

private theorem exists_fixed_norm_unit
    (D₁ D₂ : N13Mumford.SemiMumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₂) :
    ∃ ε : Rˣ,
      algebraMap R F (ε : R) *
          ((α : F) *
            (conjugateFunctionUnit M α : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) ∧
      conjugate M (ε : R) = ε := by
  let αbar : Fˣ := conjugateFunctionUnit M α
  have hbar :=
    conjugate_principal_relation M D₁ D₂ α h
  have hnorm :
      (mumfordIdealUnit M D₁ *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) *
          toPrincipalIdeal R F (α * αbar) =
        mumfordIdealUnit M D₂ *
          mumfordIdealUnit M (conjugateSemiMumford M D₂) := by
    calc
      _ =
          (mumfordIdealUnit M D₁ *
              toPrincipalIdeal R F α) *
            (mumfordIdealUnit M (conjugateSemiMumford M D₁) *
              toPrincipalIdeal R F αbar) := by
                rw [map_mul]
                ac_rfl
      _ = _ := by
        rw [h]
        simpa [αbar] using hbar
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal R⁰ F)) hnorm
  simp only [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit] at hfrac
  simp only [conjugateSemiMumford_u,
    conjugateSemiMumford_v] at hfrac
  rw [mumfordIdeal_mul_conj_fractional M D₁,
    mumfordIdeal_mul_conj_fractional M D₂,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at hfrac
  change
    FractionalIdeal.spanSingleton R⁰
        (algebraMap R F (xClass M D₁.u) *
          ((α : F) * (αbar : F))) =
      FractionalIdeal.spanSingleton R⁰
        (algebraMap R F (xClass M D₂.u)) at hfrac
  obtain ⟨e, he⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
  rw [Units.smul_def, Algebra.smul_def] at he
  let ε : Rˣ := e
  have heq :
      algebraMap R F (ε : R) *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) := by
    change
      algebraMap R F e *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u)
    rw [← he]
    ring
  have hfixedField :
      functionConjugateEquiv M
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        (α : F) * (αbar : F) *
          algebraMap R F (xClass M D₁.u) := by
    simp only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, αbar, conjugateFunctionUnit_val]
    rw [functionConjugate_involutive]
    ring
  have hconjEq := congrArg (functionConjugateEquiv M) heq
  simp only [map_mul, functionConjugateEquiv_algebraMap,
    conjugate_xClass, hfixedField] at hconjEq
  have hnormNe :
      (α : F) * (αbar : F) *
          algebraMap R F (xClass M D₁.u) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero α.ne_zero αbar.ne_zero)
      (by
        simpa only [map_zero] using
          (IsFractionRing.injective R F).ne
            (xClass_ne_zero M D₁.u_monic.ne_zero))
  have hfix : conjugate M (ε : R) = ε := by
    apply IsFractionRing.injective R F
    apply mul_right_cancel₀ hnormNe
    calc
      algebraMap R F (conjugate M (ε : R)) *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) := hconjEq
      _ =
        algebraMap R F (ε : R) *
          ((α : F) * (αbar : F) *
            algebraMap R F (xClass M D₁.u)) := heq.symm
  exact ⟨ε, heq, hfix⟩

private theorem exists_integral_factor_triple
    (D₁ D₂ D₃ : N13Mumford.SemiMumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁ *
          mumfordIdealUnit M D₂ *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₃) :
    ∃ z w : R,
      z * w = xClass M (D₁.u * D₂.u * D₃.u) ∧
      algebraMap R F z =
        (α : F) * algebraMap R F
          (xClass M (D₁.u * D₂.u)) ∧
      algebraMap R F w =
        (↑α⁻¹ : F) * algebraMap R F (xClass M D₃.u) := by
  have hx₁ :
      algebraMap R F (xClass M D₁.u) ∈
        (mumfordIdealUnit M D₁ :
          FractionalIdeal R⁰ F) := by
    rw [coe_mumfordIdealUnit]
    exact FractionalIdeal.mem_coeIdeal_of_mem R⁰
      (xClass_mem_mumfordIdeal M D₁.u D₁.v)
  have hx₂ :
      algebraMap R F (xClass M D₂.u) ∈
        (mumfordIdealUnit M D₂ :
          FractionalIdeal R⁰ F) := by
    rw [coe_mumfordIdealUnit]
    exact FractionalIdeal.mem_coeIdeal_of_mem R⁰
      (xClass_mem_mumfordIdeal M D₂.u D₂.v)
  have hα :
      (α : F) ∈
        (toPrincipalIdeal R F α : FractionalIdeal R⁰ F) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hzprod :=
    FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mul_mem_mul hx₁ hx₂) hα
  have hfrac := congrArg
    (fun U : InvFrac M => (U : FractionalIdeal R⁰ F)) h
  simp only [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit] at hfrac
  simp only [coe_mumfordIdealUnit, coe_toPrincipalIdeal] at hzprod
  rw [hfrac] at hzprod
  obtain ⟨z, -, hzeq⟩ :=
    (FractionalIdeal.mem_coeIdeal R⁰).mp hzprod
  have hz :
      algebraMap R F z =
        (α : F) * algebraMap R F
          (xClass M (D₁.u * D₂.u)) := by
    rw [xClass_mul, map_mul]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hzeq
  have hrev :
      mumfordIdealUnit M D₃ *
          toPrincipalIdeal R F α⁻¹ =
        mumfordIdealUnit M D₁ * mumfordIdealUnit M D₂ := by
    rw [← h]
    simp only [mul_assoc, map_inv, mul_inv_cancel, mul_one]
  have hx₃ :
      algebraMap R F (xClass M D₃.u) ∈
        (mumfordIdealUnit M D₃ :
          FractionalIdeal R⁰ F) := by
    rw [coe_mumfordIdealUnit]
    exact FractionalIdeal.mem_coeIdeal_of_mem R⁰
      (xClass_mem_mumfordIdeal M D₃.u D₃.v)
  have hαinv :
      (↑α⁻¹ : F) ∈
        (toPrincipalIdeal R F α⁻¹ : FractionalIdeal R⁰ F) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hwprod := FractionalIdeal.mul_mem_mul hx₃ hαinv
  have hrevfrac := congrArg
    (fun U : InvFrac M => (U : FractionalIdeal R⁰ F)) hrev
  simp only [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit] at hrevfrac
  simp only [coe_mumfordIdealUnit, coe_toPrincipalIdeal] at hwprod
  rw [hrevfrac] at hwprod
  rw [← FractionalIdeal.coeIdeal_mul] at hwprod
  obtain ⟨w, -, hweq⟩ :=
    (FractionalIdeal.mem_coeIdeal R⁰).mp hwprod
  have hw :
      algebraMap R F w =
        (↑α⁻¹ : F) * algebraMap R F (xClass M D₃.u) := by
    simpa only [mul_comm] using hweq
  refine ⟨z, w, ?_, hz, hw⟩
  apply IsFractionRing.injective R F
  rw [map_mul, hz, hw, xClass_mul, xClass_mul,
    map_mul, map_mul, Units.val_inv_eq_inv_val]
  field_simp
  rw [xClass_mul, map_mul]
  ring

private theorem exists_fixed_norm_unit_triple
    (D₁ D₂ D₃ : N13Mumford.SemiMumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁ *
          mumfordIdealUnit M D₂ *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₃) :
    ∃ ε : Rˣ,
      algebraMap R F (ε : R) *
          ((α : F) *
            (conjugateFunctionUnit M α : F) *
            algebraMap R F
              (xClass M (D₁.u * D₂.u))) =
        algebraMap R F (xClass M D₃.u) ∧
      conjugate M (ε : R) = ε := by
  let αbar : Fˣ := conjugateFunctionUnit M α
  have hbar := congrArg (conjugateInvFrac M) h
  simp only [map_mul, conjugateInvFrac_mumfordIdealUnit,
    conjugateInvFrac_principal] at hbar
  have hnorm :
      (mumfordIdealUnit M D₁ *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) *
        (mumfordIdealUnit M D₂ *
          mumfordIdealUnit M (conjugateSemiMumford M D₂)) *
        toPrincipalIdeal R F (α * αbar) =
          mumfordIdealUnit M D₃ *
            mumfordIdealUnit M
              (conjugateSemiMumford M D₃) := by
    calc
      _ =
          (mumfordIdealUnit M D₁ *
              mumfordIdealUnit M D₂ *
              toPrincipalIdeal R F α) *
            (mumfordIdealUnit M
                (conjugateSemiMumford M D₁) *
              mumfordIdealUnit M
                (conjugateSemiMumford M D₂) *
              toPrincipalIdeal R F αbar) := by
                rw [map_mul]
                ac_rfl
      _ = _ := by
        rw [h]
        simpa [αbar] using hbar
  have hfrac := congrArg
    (fun U : InvFrac M => (U : FractionalIdeal R⁰ F)) hnorm
  simp only [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit, conjugateSemiMumford_u,
    conjugateSemiMumford_v] at hfrac
  rw [mumfordIdeal_mul_conj_fractional M D₁,
    mumfordIdeal_mul_conj_fractional M D₂,
    mumfordIdeal_mul_conj_fractional M D₃,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at hfrac
  change
    FractionalIdeal.spanSingleton R⁰
        (algebraMap R F (xClass M D₁.u) *
          algebraMap R F (xClass M D₂.u) *
          ((α : F) * (αbar : F))) =
      FractionalIdeal.spanSingleton R⁰
        (algebraMap R F (xClass M D₃.u)) at hfrac
  obtain ⟨ε, he⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
  rw [Units.smul_def, Algebra.smul_def] at he
  have heq :
      algebraMap R F (ε : R) *
          ((α : F) * (αbar : F) *
            algebraMap R F
              (xClass M (D₁.u * D₂.u))) =
        algebraMap R F (xClass M D₃.u) := by
    rw [xClass_mul, map_mul]
    rw [← he]
    ring
  have hfixedField :
      functionConjugateEquiv M
          ((α : F) * (αbar : F) *
            algebraMap R F
              (xClass M (D₁.u * D₂.u))) =
        (α : F) * (αbar : F) *
          algebraMap R F
            (xClass M (D₁.u * D₂.u)) := by
    simp only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, αbar, conjugateFunctionUnit_val]
    rw [functionConjugate_involutive]
    ring
  have hconjEq := congrArg (functionConjugateEquiv M) heq
  simp only [map_mul, functionConjugateEquiv_algebraMap,
    conjugate_xClass, hfixedField] at hconjEq
  have hnormNe :
      (α : F) * (αbar : F) *
          algebraMap R F
            (xClass M (D₁.u * D₂.u)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero α.ne_zero αbar.ne_zero)
      (by
        simpa only [map_zero] using
          (IsFractionRing.injective R F).ne
            (xClass_ne_zero M
              (mul_ne_zero D₁.u_monic.ne_zero
                D₂.u_monic.ne_zero)))
  have hfix : conjugate M (ε : R) = ε := by
    apply IsFractionRing.injective R F
    apply mul_right_cancel₀ hnormNe
    calc
      algebraMap R F (conjugate M (ε : R)) *
          ((α : F) * (αbar : F) *
            algebraMap R F
              (xClass M (D₁.u * D₂.u))) =
        algebraMap R F (xClass M D₃.u) := hconjEq
      _ =
        algebraMap R F (ε : R) *
          ((α : F) * (αbar : F) *
            algebraMap R F
              (xClass M (D₁.u * D₂.u))) := heq.symm
  exact ⟨ε, heq, hfix⟩

/-- The structural scalar-square relation behind principal invariance.
The witness `z` is the integral numerator of the principal multiplier. -/
theorem exists_scalar_square_product_of_principal_relation
    (D₁ D₂ : N13Mumford.Mumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁.toSemi *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₂.toSemi) :
    ∃ q : ℚˣ, ∃ z : R,
      N13MumfordKummerValue.thetaBranch z ≠ 0 ∧
      N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z ^ 2 := by
  obtain ⟨ε, hnorm, hfix⟩ :=
    exists_fixed_norm_unit D₁.toSemi D₂.toSemi α h
  obtain ⟨q, hε⟩ :=
    fixed_coordinate_unit_is_scalar M ε hfix
  obtain ⟨z, w, -, -, hzw, hz, hw⟩ :=
    exists_integral_factor_pair_of_principal_relation
      M D₁.toSemi D₂.toSemi α h
  have hzbarF :
      algebraMap R F (conjugate M z) =
        (conjugateFunctionUnit M α : F) *
          algebraMap R F (xClass M D₁.u) := by
    have hzconj := congrArg (functionConjugateEquiv M) hz
    simpa only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, conjugateFunctionUnit_val,
      toSemi_u] using hzconj
  have hnorm' :
      algebraMap R F (ε : R) *
          ((α : F) *
            (conjugateFunctionUnit M α : F) *
            algebraMap R F (xClass M D₁.u)) =
        algebraMap R F (xClass M D₂.u) := by
    simpa only [toSemi_u] using hnorm
  have hwbarF :
      algebraMap R F w =
        algebraMap R F (ε : R) *
          algebraMap R F (conjugate M z) := by
    calc
      algebraMap R F w =
          (↑α⁻¹ : F) *
            algebraMap R F (xClass M D₂.u) := hw
      _ =
          (↑α⁻¹ : F) *
            (algebraMap R F (ε : R) *
              ((α : F) *
                (conjugateFunctionUnit M α : F) *
                algebraMap R F (xClass M D₁.u))) := by
                  rw [hnorm']
      _ =
          algebraMap R F (ε : R) *
            ((conjugateFunctionUnit M α : F) *
              algebraMap R F (xClass M D₁.u)) := by
                rw [Units.val_inv_eq_inv_val]
                field_simp
      _ =
          algebraMap R F (ε : R) *
            algebraMap R F (conjugate M z) := by rw [hzbarF]
  have hwbar :
      w = (ε : R) * conjugate M z := by
    apply IsFractionRing.injective R F
    rw [map_mul]
    exact hwbarF
  have hεtheta :
      N13MumfordKummerValue.thetaBranch (ε : R) =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) := by
    rw [hε]
    change
      N13MumfordKummerValue.thetaBranch
          (xClass M (C (q : ℚ))) =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ)
    rw [N13MumfordKummerValue.thetaBranch_xClass]
    simp
  have hwtheta :
      N13MumfordKummerValue.thetaBranch w =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z := by
    have hθ := congrArg N13MumfordKummerValue.thetaBranch hwbar
    rw [map_mul, N13MumfordKummerValue.thetaBranch_conjugate,
      hεtheta] at hθ
    exact hθ
  have hprod :
      N13MumfordKummerValue.thetaBranch z *
          N13MumfordKummerValue.thetaBranch w =
        N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ := by
    have hθ := congrArg N13MumfordKummerValue.thetaBranch hzw
    simpa only [map_mul,
      N13MumfordKummerValue.thetaBranch_xClass,
      N13MumfordKummerValue.uTheta_eq_mk,
      toSemi_u] using hθ
  have hztheta :
      N13MumfordKummerValue.thetaBranch z ≠ 0 := by
    intro hzzero
    have hzero :
        N13MumfordKummerValue.uTheta D₁ *
            N13MumfordKummerValue.uTheta D₂ = 0 := by
      rw [← hprod, hzzero, zero_mul]
    exact
      (mul_ne_zero
        (N13MumfordKummerValue.uTheta_ne_zero D₁)
        (N13MumfordKummerValue.uTheta_ne_zero D₂)) hzero
  refine ⟨q, z, hztheta, ?_⟩
  rw [← hprod, hwtheta]
  ring

/-- Three Mumford ideals in a principal product relation satisfy the
scalar-square identity needed for additivity. -/
theorem exists_scalar_square_triple_of_principal_relation
    (D₁ D₂ D₃ : N13Mumford.Mumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁.toSemi *
          mumfordIdealUnit M D₂.toSemi *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₃.toSemi) :
    ∃ q : ℚˣ, ∃ z : R,
      N13MumfordKummerValue.thetaBranch z ≠ 0 ∧
      N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ *
          N13MumfordKummerValue.uTheta D₃ =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z ^ 2 := by
  obtain ⟨ε, hnorm, hfix⟩ :=
    exists_fixed_norm_unit_triple
      D₁.toSemi D₂.toSemi D₃.toSemi α h
  obtain ⟨q, hε⟩ :=
    fixed_coordinate_unit_is_scalar M ε hfix
  obtain ⟨z, w, hzw, hz, hw⟩ :=
    exists_integral_factor_triple
      D₁.toSemi D₂.toSemi D₃.toSemi α h
  have hzbarF :
      algebraMap R F (conjugate M z) =
        (conjugateFunctionUnit M α : F) *
          algebraMap R F
            (xClass M (D₁.u * D₂.u)) := by
    have hzconj := congrArg (functionConjugateEquiv M) hz
    simpa only [map_mul, functionConjugateEquiv_algebraMap,
      conjugate_xClass, conjugateFunctionUnit_val,
      toSemi_u] using hzconj
  have hnorm' :
      algebraMap R F (ε : R) *
          ((α : F) *
            (conjugateFunctionUnit M α : F) *
            algebraMap R F
              (xClass M (D₁.u * D₂.u))) =
        algebraMap R F (xClass M D₃.u) := by
    simpa only [toSemi_u] using hnorm
  have hwbarF :
      algebraMap R F w =
        algebraMap R F (ε : R) *
          algebraMap R F (conjugate M z) := by
    calc
      algebraMap R F w =
          (↑α⁻¹ : F) *
            algebraMap R F (xClass M D₃.u) := by
              simpa only [toSemi_u] using hw
      _ =
          (↑α⁻¹ : F) *
            (algebraMap R F (ε : R) *
              ((α : F) *
                (conjugateFunctionUnit M α : F) *
                algebraMap R F
                  (xClass M (D₁.u * D₂.u)))) := by
                    rw [hnorm']
      _ =
          algebraMap R F (ε : R) *
            ((conjugateFunctionUnit M α : F) *
              algebraMap R F
                (xClass M (D₁.u * D₂.u))) := by
                  rw [Units.val_inv_eq_inv_val]
                  field_simp
      _ =
          algebraMap R F (ε : R) *
            algebraMap R F (conjugate M z) := by rw [hzbarF]
  have hwbar :
      w = (ε : R) * conjugate M z := by
    apply IsFractionRing.injective R F
    rw [map_mul]
    exact hwbarF
  have hεtheta :
      N13MumfordKummerValue.thetaBranch (ε : R) =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) := by
    rw [hε]
    change
      N13MumfordKummerValue.thetaBranch
          (xClass M (C (q : ℚ))) =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ)
    rw [N13MumfordKummerValue.thetaBranch_xClass]
    simp
  have hwtheta :
      N13MumfordKummerValue.thetaBranch w =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z := by
    have hθ := congrArg N13MumfordKummerValue.thetaBranch hwbar
    rw [map_mul, N13MumfordKummerValue.thetaBranch_conjugate,
      hεtheta] at hθ
    exact hθ
  have hprod :
      N13MumfordKummerValue.thetaBranch z *
          N13MumfordKummerValue.thetaBranch w =
        N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ *
          N13MumfordKummerValue.uTheta D₃ := by
    have hθ := congrArg N13MumfordKummerValue.thetaBranch hzw
    simpa only [map_mul,
      N13MumfordKummerValue.thetaBranch_xClass,
      N13MumfordKummerValue.uTheta_eq_mk,
      toSemi_u] using hθ
  have hztheta :
      N13MumfordKummerValue.thetaBranch z ≠ 0 := by
    intro hzzero
    have hzero :
        N13MumfordKummerValue.uTheta D₁ *
            N13MumfordKummerValue.uTheta D₂ *
            N13MumfordKummerValue.uTheta D₃ = 0 := by
      rw [← hprod, hzzero, zero_mul]
    exact
      (mul_ne_zero
        (mul_ne_zero
          (N13MumfordKummerValue.uTheta_ne_zero D₁)
          (N13MumfordKummerValue.uTheta_ne_zero D₂))
        (N13MumfordKummerValue.uTheta_ne_zero D₃)) hzero
  refine ⟨q, z, hztheta, ?_⟩
  rw [← hprod, hwtheta]
  ring

/-- Multiplicativity of `u(θ)` modulo squares and scalars, stated directly
for a three-ideal principal relation. -/
theorem mumfordFakeClass_add_of_product_principal_relation
    (D₁ D₂ D₃ : N13Mumford.Mumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁.toSemi *
          mumfordIdealUnit M D₂.toSemi *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₃.toSemi) :
    N13MumfordKummerValue.mumfordFakeClass D₃ =
      N13MumfordKummerValue.mumfordFakeClass D₁ +
        N13MumfordKummerValue.mumfordFakeClass D₂ := by
  obtain ⟨q, z, hz, hsq⟩ :=
    exists_scalar_square_triple_of_principal_relation
      D₁ D₂ D₃ α h
  let zUnit : N13MumfordKummerValue.Lˣ :=
    Units.mk0 (N13MumfordKummerValue.thetaBranch z) hz
  have hunits :
      (N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ *
          N13MumfordKummerValue.uThetaUnit D₃) *
          (zUnit⁻¹) ^ 2 =
        FakeSquareClass.scalarUnitsMap
          (algebraMap ℚ N13MumfordKummerValue.L) q := by
    apply Units.ext
    change
      (N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ *
          N13MumfordKummerValue.uTheta D₃) *
          (N13MumfordKummerValue.thetaBranch z)⁻¹ ^ 2 =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ)
    rw [hsq]
    field_simp
  have htrivial :
      (((N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ *
          N13MumfordKummerValue.uThetaUnit D₃ :
          N13MumfordKummerValue.Lˣ)) :
        FakeSquareClass.Target
          (algebraMap ℚ N13MumfordKummerValue.L)) = 1 :=
    FakeSquareClass.eq_one_of_mul_sq_eq_scalar
      (algebraMap ℚ N13MumfordKummerValue.L)
      (N13MumfordKummerValue.uThetaUnit D₁ *
        N13MumfordKummerValue.uThetaUnit D₂ *
        N13MumfordKummerValue.uThetaUnit D₃)
      zUnit⁻¹ q hunits
  change
    (((N13MumfordKummerValue.uThetaUnit D₃ :
        N13MumfordKummerValue.Lˣ)) :
      FakeSquareClass.Target
        (algebraMap ℚ N13MumfordKummerValue.L)) =
      (((N13MumfordKummerValue.uThetaUnit D₁ :
          N13MumfordKummerValue.Lˣ)) :
        FakeSquareClass.Target
          (algebraMap ℚ N13MumfordKummerValue.L)) *
      (((N13MumfordKummerValue.uThetaUnit D₂ :
          N13MumfordKummerValue.Lˣ)) :
        FakeSquareClass.Target
          (algebraMap ℚ N13MumfordKummerValue.L))
  rw [FakeSquareClass.target_eq_iff_mul_eq_one]
  change
    QuotientGroup.mk'
        (FakeSquareClass.fakeSquareClassSubgroup
          (algebraMap ℚ N13MumfordKummerValue.L))
        (N13MumfordKummerValue.uThetaUnit D₃) *
      (QuotientGroup.mk'
          (FakeSquareClass.fakeSquareClassSubgroup
            (algebraMap ℚ N13MumfordKummerValue.L))
          (N13MumfordKummerValue.uThetaUnit D₁) *
        QuotientGroup.mk'
          (FakeSquareClass.fakeSquareClassSubgroup
            (algebraMap ℚ N13MumfordKummerValue.L))
          (N13MumfordKummerValue.uThetaUnit D₂)) = 1
  change
    QuotientGroup.mk'
        (FakeSquareClass.fakeSquareClassSubgroup
          (algebraMap ℚ N13MumfordKummerValue.L))
        (N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ *
          N13MumfordKummerValue.uThetaUnit D₃) = 1 at htrivial
  rw [map_mul, map_mul] at htrivial
  simpa only [mul_assoc, mul_comm, mul_left_comm] using htrivial

/-- A principal relation between affine Mumford ideals preserves the raw
fake-Kummer class.  No degree split and no infinity-order hypothesis is
needed. -/
theorem mumfordFakeClass_eq_of_principal_relation
    (D₁ D₂ : N13Mumford.Mumford ℚ)
    (α : Fˣ)
    (h :
      mumfordIdealUnit M D₁.toSemi *
          toPrincipalIdeal R F α =
        mumfordIdealUnit M D₂.toSemi) :
    N13MumfordKummerValue.mumfordFakeClass D₁ =
      N13MumfordKummerValue.mumfordFakeClass D₂ := by
  obtain ⟨q, z, hz, hsq⟩ :=
    exists_scalar_square_product_of_principal_relation D₁ D₂ α h
  let zUnit : N13MumfordKummerValue.Lˣ :=
    Units.mk0 (N13MumfordKummerValue.thetaBranch z) hz
  have hunits :
      N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ =
        FakeSquareClass.scalarUnitsMap
            (algebraMap ℚ N13MumfordKummerValue.L) q *
          zUnit ^ 2 := by
    apply Units.ext
    change
      N13MumfordKummerValue.uTheta D₁ *
          N13MumfordKummerValue.uTheta D₂ =
        algebraMap ℚ N13MumfordKummerValue.L (q : ℚ) *
          N13MumfordKummerValue.thetaBranch z ^ 2
    exact hsq
  let c₁ : FakeSquareClass.Target
      (algebraMap ℚ N13MumfordKummerValue.L) :=
    N13MumfordKummerValue.uThetaUnit D₁
  let c₂ : FakeSquareClass.Target
      (algebraMap ℚ N13MumfordKummerValue.L) :=
    N13MumfordKummerValue.uThetaUnit D₂
  have hcprod : c₁ * c₂ = 1 := by
    change
      ((N13MumfordKummerValue.uThetaUnit D₁ *
          N13MumfordKummerValue.uThetaUnit D₂ :
          N13MumfordKummerValue.Lˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13MumfordKummerValue.L)) = 1
    rw [hunits]
    change
      ((FakeSquareClass.scalarUnitsMap
          (algebraMap ℚ N13MumfordKummerValue.L) q :
          N13MumfordKummerValue.Lˣ) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) *
        ((zUnit ^ 2 : N13MumfordKummerValue.Lˣ) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) = 1
    rw [FakeSquareClass.scalar_eq_one,
      FakeSquareClass.square_eq_one, one_mul]
  change c₁ = c₂
  calc
    c₁ = c₁ * c₂ ^ 2 := by
      rw [FakeSquareClass.target_sq_eq_one, mul_one]
    _ = (c₁ * c₂) * c₂ := by rw [pow_two, mul_assoc]
    _ = c₂ := by rw [hcprod, one_mul]

/-- The raw fake-Kummer value depends only on the oriented Picard class.
The infinity equality in `classOf_eq_iff` is not needed after extracting
the finite principal-ideal relation. -/
theorem mumfordFakeClass_eq_of_classOf_eq
    (O : InfinityOrder M)
    (D₁ D₂ : N13Mumford.Mumford ℚ)
    (h :
      classOf M O D₁ = classOf M O D₂) :
    N13MumfordKummerValue.mumfordFakeClass D₁ =
      N13MumfordKummerValue.mumfordFakeClass D₂ := by
  obtain ⟨α, hIdeal, -⟩ :=
    (classOf_eq_iff M O D₁ D₂).mp h
  exact mumfordFakeClass_eq_of_principal_relation
    D₁ D₂ α hIdeal

/-- The raw fake-Kummer value turns addition of oriented Picard classes
into addition in the additive-tagged fake square-class target. -/
theorem mumfordFakeClass_add_of_class_add
    (O : InfinityOrder M)
    (D₁ D₂ D₃ : N13Mumford.Mumford ℚ)
    (h :
      classOf M O D₃ =
        classOf M O D₁ + classOf M O D₂) :
    N13MumfordKummerValue.mumfordFakeClass D₃ =
      N13MumfordKummerValue.mumfordFakeClass D₁ +
        N13MumfordKummerValue.mumfordFakeClass D₂ := by
  have hclass :
      QuotientGroup.mk'
          (principalOriented M O).range
          (mumfordRaw M D₁ * mumfordRaw M D₂) =
        QuotientGroup.mk'
          (principalOriented M O).range
          (mumfordRaw M D₃) := by
    rw [map_mul]
    exact h.symm
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  obtain ⟨z, hz, hmul⟩ := hclass
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
  have hIdeal := congrArg Prod.fst hmul
  apply mumfordFakeClass_add_of_product_principal_relation
    D₁ D₂ D₃ α
  simpa only [mumfordRaw, principalOriented,
    MonoidHom.prod_apply, Prod.fst_mul] using hIdeal

end

end MazurProof.N13MumfordKummerRelation


