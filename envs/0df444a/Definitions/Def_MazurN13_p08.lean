-- Prove2me | Definitions.Def_MazurN13_p08
-- name    : MazurN13_p08
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T01:37:30.139582+00:00
-- url     : https://prove2.me/theorems/b877d335-a405-4011-9e3e-aede6aab1d53
-- title:
--   Mazur order 13 (Huang FLT port), part 8/64
-- statement:
--   Part 8 of 64 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.N13MumfordKummerRelation`
--   - `FLT.Assumptions.MazurProof.N13LowDegreeKummerHom`
--   - `FLT.Assumptions.MazurProof.N13FullNormPair`
--   - `FLT.Assumptions.MazurProof.N13MumfordKummerNorm`
--   - `FLT.Assumptions.MazurProof.N13GlobalKummerNormalization`
--   - `FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare`
--   - `FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare`
--   - `FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`
--   - `FLT.Mathlib.RingTheory.Valuation.ValuationSubring`
--   - `FLT.DedekindDomain.AdicValuation`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p07
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.N13MumfordKummerRelation
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerRelation =====
section

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

theorem exists_fixed_norm_unit
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

theorem exists_integral_factor_triple
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

theorem exists_fixed_norm_unit_triple
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

end
end

-- module FLT.Assumptions.MazurProof.N13LowDegreeKummerHom
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LowDegreeKummerHom =====
section

/-!
# The N13 fake-Kummer homomorphism from low-degree semirepresentatives

The fake Kummer value depends on the affine Mumford ideal and the polynomial
`u`, but not on the separate infinity-balance inequalities.  The structural
Cantor reduction already gives every oriented Picard class a semirepresentative
with `deg u ≤ 2`.

We therefore attach to such a semirepresentative an auxiliary balanced
Mumford datum with the same `(u,v)` and infinity coordinate zero.  This datum
is used only to reuse the existing `u(θ)` and principal-relation theorems; its
oriented class is not substituted for the original semirepresentative's
class.  Principal relations are extracted from the original oriented
classes, where their actual integer infinity coordinates are retained.

This removes infinity balancing from the dependency chain of the N13
fake-Kummer homomorphism.
-/

namespace MazurProof.N13LowDegreeKummerHom

noncomputable section

open SexticMumford

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev O : SexticMumford.InfinityOrder M :=
  N13Infinity.positiveInfinityOrder ℚ

abbrev G : Type :=
  SexticMumford.ConcretePic M O

abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget

abbrev LowRep : Type :=
  SexticMumford.LowDegreeSemi M

/-- Forget the original infinity coordinate only for evaluation of `u(θ)`.
The affine ideal and all its proofs are unchanged. -/
def asMumford (D : LowRep) : N13Mumford.Mumford ℚ where
  u := D.toSemi.u
  v := D.toSemi.v
  nInf := 0
  u_monic := D.toSemi.u_monic
  deg_u := D.degree_le_two
  v_reduced := D.toSemi.v_reduced
  curve_dvd := D.toSemi.curve_dvd
  infinity_bound := by
    simpa using D.degree_le_two

@[simp] theorem asMumford_u (D : LowRep) :
    (asMumford D).u = D.toSemi.u := rfl

@[simp] theorem asMumford_v (D : LowRep) :
    (asMumford D).v = D.toSemi.v := rfl

@[simp] theorem asMumford_nInf (D : LowRep) :
    (asMumford D).nInf = 0 := rfl

theorem mumfordIdealUnit_asMumford (D : LowRep) :
    mumfordIdealUnit M (asMumford D).toSemi =
      mumfordIdealUnit M D.toSemi := by
  apply Units.ext
  rfl

/-- The oriented class uses the original integer infinity coordinate. -/
def lowClass (D : LowRep) : G :=
  semiMumfordClass M O D.toSemi

/-- The raw fake value uses only the shared affine data `(u,v)`. -/
def lowFakeClass (D : LowRep) : Target :=
  N13MumfordKummerValue.mumfordFakeClass (asMumford D)

/-- The low-degree semirepresentative of the identity. -/
def zeroLow : LowRep where
  toSemi := (SexticMumford.zero M).toSemi
  degree_le_two := (SexticMumford.zero M).deg_u

@[simp] theorem lowClass_zero :
    lowClass zeroLow = 0 := by
  change
    semiMumfordClass M O (SexticMumford.zero M).toSemi = 0
  rw [semiMumfordClass_toSemi, classOf_zero]

@[simp] theorem lowFakeClass_zero :
    lowFakeClass zeroLow = 0 := by
  change
    N13MumfordKummerValue.mumfordFakeClass
        (asMumford zeroLow) =
      0
  change
    Additive.ofMul
        ((((N13MumfordKummerValue.uThetaUnit
          (asMumford zeroLow) :
            N13MumfordKummerValue.Lˣ))) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      0
  have hu :
      N13MumfordKummerValue.uThetaUnit
          (asMumford zeroLow) = 1 := by
    apply Units.ext
    change
      N13MumfordKummerValue.uTheta (asMumford zeroLow) = 1
    simp [N13MumfordKummerValue.uTheta_eq_mk,
      asMumford, zeroLow]
  rw [hu]
  rfl

/-- Equality of original oriented classes gives equality of fake values.
Only the finite principal-ideal component is consumed by the existing
principal-relation theorem. -/
theorem lowFakeClass_eq_of_class_eq
    (D₁ D₂ : LowRep)
    (h : lowClass D₁ = lowClass D₂) :
    lowFakeClass D₁ = lowFakeClass D₂ := by
  obtain ⟨alpha, hIdeal, -⟩ :=
    (semiMumfordClass_eq_iff M O D₁.toSemi D₂.toSemi).mp h
  apply
    N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation
      (asMumford D₁) (asMumford D₂) alpha
  simpa only [mumfordIdealUnit_asMumford] using hIdeal

/-- Addition of original oriented classes gives multiplication of the
affine Mumford ideals modulo a principal ideal, hence addition of fake
values. -/
theorem lowFakeClass_add_of_class_add
    (D₁ D₂ D₃ : LowRep)
    (h : lowClass D₃ = lowClass D₁ + lowClass D₂) :
    lowFakeClass D₃ = lowFakeClass D₁ + lowFakeClass D₂ := by
  have hclass :
      QuotientGroup.mk'
          (principalOriented M O).range
          (semiMumfordRaw M D₁.toSemi *
            semiMumfordRaw M D₂.toSemi) =
        QuotientGroup.mk'
          (principalOriented M O).range
          (semiMumfordRaw M D₃.toSemi) := by
    rw [map_mul]
    exact h.symm
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  obtain ⟨z, hz, hmul⟩ := hclass
  obtain ⟨alpha, rfl⟩ := MonoidHom.mem_range.mp hz
  have hIdeal := congrArg Prod.fst hmul
  apply
    N13MumfordKummerRelation.mumfordFakeClass_add_of_product_principal_relation
      (asMumford D₁) (asMumford D₂) (asMumford D₃) alpha
  simpa only [semiMumfordRaw, principalOriented,
    MonoidHom.prod_apply, Prod.fst_mul,
    mumfordIdealUnit_asMumford] using hIdeal

/-- Phase I of structural reduction is already surjective onto the
oriented Picard group. -/
theorem lowClass_surjective :
    Function.Surjective lowClass := by
  intro P
  obtain ⟨D, hD⟩ :=
    exists_lowDegreeSemiRepresentative M O P
  exact ⟨D, hD⟩

/-- A chosen low-degree semirepresentative of an oriented Picard class. -/
def representative (P : G) : LowRep :=
  Function.surjInv lowClass_surjective P

@[simp] theorem lowClass_representative (P : G) :
    lowClass (representative P) = P :=
  Function.surjInv_eq lowClass_surjective P

/-- The N13 fake-Kummer homomorphism constructed without an infinity
balancing theorem. -/
def mumfordKummer : G →+ Target where
  toFun P := lowFakeClass (representative P)
  map_zero' := by
    have h :=
      lowFakeClass_eq_of_class_eq
        (representative 0) zeroLow
        (by rw [lowClass_representative, lowClass_zero])
    simpa using h
  map_add' P Q := by
    apply lowFakeClass_add_of_class_add
      (representative P) (representative Q)
        (representative (P + Q))
    rw [lowClass_representative, lowClass_representative,
      lowClass_representative]

@[simp] theorem mumfordKummer_apply (P : G) :
    mumfordKummer P = lowFakeClass (representative P) :=
  rfl

end

end MazurProof.N13LowDegreeKummerHom

end
end

-- module FLT.Assumptions.MazurProof.N13FullNormPair
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FullNormPair =====
section

/-!
# The full norm-pair target for N13

This file specializes the abstract even-sextic target to the sextic field
`L = ℚ[θ]`.  Its full target remembers `(α,s)` with `N(α)=s²`, before
forgetting `s` to obtain the existing fake square-class target.

The kernel of forgetting has at most the identity and the sign class
represented by `(1,-1)`.  This is target algebra only: it does not assert
the hard principal-genus theorem for the Picard Kummer map.
-/

namespace MazurProof.N13FullNormPair

noncomputable section

open N13SexticSquareclass

abbrev L : Type :=
  SexticAlgebra

local instance sexticAlgebraField : Field L :=
  N13SexticIrreducible.sexticAlgebraField

/-- The norm on units of the N13 sextic field. -/
def normUnits : Lˣ →* ℚˣ :=
  Units.map (Algebra.norm ℚ)

/-- Rational scalar units inside the sextic field. -/
def scalarUnits : ℚˣ →* Lˣ :=
  FakeSquareClass.scalarUnitsMap (algebraMap ℚ L)

theorem finrank_L :
    Module.finrank ℚ L = 6 := by
  change
    Module.finrank ℚ
      (AdjoinRoot N13SexticSquareclass.f) = 6
  rw [(AdjoinRoot.powerBasis
    (by
      simpa [N13SexticSquareclass.f] using
        (N13Mumford.f_monic (K := ℚ)).ne_zero)).finrank]
  simpa [N13SexticSquareclass.f] using
    (N13Mumford.f_natDegree (K := ℚ))

/-- A rational scalar has sextic norm `q⁶`. -/
@[simp] theorem normUnits_scalarUnits (q : ℚˣ) :
    normUnits (scalarUnits q) = q ^ 6 := by
  apply Units.ext
  change
    Algebra.norm ℚ (algebraMap ℚ L (q : ℚ)) =
      (q : ℚ) ^ 6
  simpa [finrank_L] using
    (Algebra.norm_algebraMap (R := ℚ) (S := L) (q : ℚ))

abbrev NormPair : Type :=
  EvenSexticNormPair.NormPair normUnits

abbrev FullTarget : Type :=
  EvenSexticNormPair.FullTarget
    normUnits scalarUnits normUnits_scalarUnits

abbrev FakeTarget : Type :=
  FakeSquareClass.Target (algebraMap ℚ L)

/-- Forget the chosen rational square root of the norm. -/
abbrev forget : FullTarget →* FakeTarget :=
  EvenSexticNormPair.forget
    normUnits scalarUnits normUnits_scalarUnits

theorem minusOne_sq :
    (-1 : ℚˣ) ^ 2 = 1 := by
  simp

/-- The possible extra sign class in the full target. -/
abbrev signClass : FullTarget :=
  QuotientGroup.mk'
      (EvenSexticNormPair.fullGauge
        normUnits scalarUnits normUnits_scalarUnits)
    (EvenSexticNormPair.signPair normUnits (-1) minusOne_sq)

/-- The only rational units with square one are `1` and `-1`. -/
theorem ratUnit_sq_eq_one
    (ε : ℚˣ) (hε : ε ^ 2 = 1) :
    ε = 1 ∨ ε = -1 := by
  have hval : ((ε : ℚ) ^ 2) = 1 := by
    exact congrArg (fun u : ℚˣ => (u : ℚ)) hε
  have hfactor :
      ((ε : ℚ) - 1) * ((ε : ℚ) + 1) = 0 := by
    calc
      ((ε : ℚ) - 1) * ((ε : ℚ) + 1) =
          (ε : ℚ) ^ 2 - 1 := by ring
      _ = 0 := by rw [hval]; norm_num
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    apply Units.ext
    change (ε : ℚ) = 1
    exact sub_eq_zero.mp hminus
  · right
    apply Units.ext
    change (ε : ℚ) = -1
    exact eq_neg_of_add_eq_zero_left hplus

/-- The forgetting kernel has exactly the two displayed alternatives; the
theorem does not require proving that those alternatives are distinct. -/
theorem forget_eq_one_iff (z : FullTarget) :
    forget z = 1 ↔ z = 1 ∨ z = signClass := by
  exact
    EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign
      normUnits scalarUnits normUnits_scalarUnits
      (-1 : ℚˣ) minusOne_sq ratUnit_sq_eq_one z

/-- The concrete full N13 target has exponent two. -/
@[simp] theorem fullTarget_sq_eq_one (z : FullTarget) :
    z ^ 2 = 1 :=
  EvenSexticNormPair.fullTarget_sq_eq_one
    normUnits scalarUnits normUnits_scalarUnits z

end

end MazurProof.N13FullNormPair

end
end

-- module FLT.Assumptions.MazurProof.N13MumfordKummerNorm
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerNorm =====
section

/-!
# The square norm of an N13 Mumford Kummer value

For a Mumford pair `(u,v)`, the relation

`f - v² = u w`

implies structurally that

`Norm(u(θ)) = Res(f,u) = Res(u,v)²`.

This is the global norm condition used by the weak two-descent.  The proof
uses functorial identities of the resultant; it neither splits `u` nor
separates its possible degrees.
-/

open Polynomial

namespace MazurProof.N13MumfordKummerNorm

noncomputable section

abbrev L : Type :=
  N13SexticSquareclass.SexticAlgebra

abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep

/-- The canonical rational square root supplied by the Mumford congruence. -/
def normRoot (D : LowRep) : ℚ :=
  D.toSemi.u.resultant D.toSemi.v

theorem v_sq_natDegree_lt_six (D : LowRep) :
    (D.toSemi.v ^ 2).natDegree < 6 := by
  by_cases hu0 : D.toSemi.u.natDegree = 0
  · have huone : D.toSemi.u = 1 :=
      D.toSemi.u_monic.natDegree_eq_zero.mp hu0
    have hvzero : D.toSemi.v = 0 := by
      have hred := D.toSemi.v_reduced
      have hzero : D.toSemi.v % (1 : ℚ[X]) = 0 := by
        exact EuclideanDomain.mod_one _
      rw [huone, hzero] at hred
      exact hred.symm
    rw [hvzero]
    norm_num
  · have huone : D.toSemi.u ≠ 1 := by
      intro h
      apply hu0
      rw [h, natDegree_one]
    have hvlt :
        D.toSemi.v.natDegree < D.toSemi.u.natDegree := by
      have hmod :=
        natDegree_modByMonic_lt D.toSemi.v
          D.toSemi.u_monic huone
      rw [modByMonic_eq_mod D.toSemi.v D.toSemi.u_monic,
        D.toSemi.v_reduced] at hmod
      exact hmod
    calc
      (D.toSemi.v ^ 2).natDegree =
          2 * D.toSemi.v.natDegree :=
        Polynomial.natDegree_pow _ _
      _ < 6 := by
        have hdu := D.degree_le_two
        omega

/-- The cofactor has the complementary degree.  This will later turn the
principal ideal of `u(θ)` into a square away from the discriminant. -/
theorem exists_curveFactor_degree (D : LowRep) :
    ∃ w : ℚ[X],
      N13Mumford.f ℚ - D.toSemi.v ^ 2 =
          D.toSemi.u * w ∧
      D.toSemi.u.natDegree + w.natDegree = 6 := by
  obtain ⟨w, hw⟩ := D.toSemi.curve_dvd
  change
    N13Mumford.f ℚ - D.toSemi.v ^ 2 =
      D.toSemi.u * w at hw
  have hleft :
      (N13Mumford.f ℚ - D.toSemi.v ^ 2).natDegree = 6 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt
      (by
        rw [N13Mumford.f_natDegree]
        exact v_sq_natDegree_lt_six D)]
    exact N13Mumford.f_natDegree (K := ℚ)
  have hprod : D.toSemi.u * w ≠ 0 := by
    intro hzero
    have := congrArg Polynomial.natDegree hzero
    rw [← hw, hleft, natDegree_zero] at this
    omega
  have hwzero : w ≠ 0 := fun hw0 => hprod (by rw [hw0, mul_zero])
  refine ⟨w, hw, ?_⟩
  calc
    D.toSemi.u.natDegree + w.natDegree =
        (D.toSemi.u * w).natDegree := by
      rw [Polynomial.natDegree_mul
        D.toSemi.u_monic.ne_zero hwzero]
    _ = 6 := by rw [← hw, hleft]

/-- The norm resultant is a square before passing to square classes. -/
theorem resultant_f_u_eq_normRoot_sq (D : LowRep) :
    (N13Mumford.f ℚ).resultant D.toSemi.u =
      normRoot D ^ 2 := by
  obtain ⟨w, hw, hdegree⟩ :=
    exists_curveFactor_degree D
  let f : ℚ[X] := N13Mumford.f ℚ
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  have hfdeg : f.natDegree = 6 :=
    by
      simpa only [f] using
        (N13Mumford.f_natDegree (K := ℚ))
  have hudeg : u.natDegree ≤ 2 :=
    D.degree_le_two
  have hv2le : (v ^ 2).natDegree ≤ 6 :=
    (v_sq_natDegree_lt_six D).le
  have hwdeg : w.natDegree + u.natDegree ≤ 6 := by
    rw [add_comm, hdegree]
  have hdecomp : f = v ^ 2 + u * w := by
    dsimp only [f, u, v]
    linear_combination hw
  have hsign :
      (-1 : ℚ) ^ (f.natDegree * u.natDegree) = 1 := by
    rw [hfdeg]
    conv_lhs => rw [show 6 * u.natDegree = 2 * (3 * u.natDegree) by omega]
    rw [pow_mul]
    norm_num
  have hpad :
      u.resultant (v ^ 2) u.natDegree 6 =
        u.resultant (v ^ 2) u.natDegree
          (v ^ 2).natDegree := by
    calc
      u.resultant (v ^ 2) u.natDegree 6 =
          u.resultant (v ^ 2) u.natDegree
            ((v ^ 2).natDegree +
              (6 - (v ^ 2).natDegree)) := by
        rw [Nat.add_sub_of_le hv2le]
      _ =
          u.coeff u.natDegree ^
              (6 - (v ^ 2).natDegree) *
            u.resultant (v ^ 2) u.natDegree
              (v ^ 2).natDegree := by
        rw [Polynomial.resultant_add_right_deg
          u (v ^ 2) u.natDegree (v ^ 2).natDegree
          (6 - (v ^ 2).natDegree) le_rfl]
      _ = _ := by
        simp only [u, D.toSemi.u_monic.coeff_natDegree,
          one_pow, one_mul]
  have hsquare :
      u.resultant (v ^ 2) u.natDegree
          (v ^ 2).natDegree =
        (u.resultant v u.natDegree v.natDegree) ^ 2 := by
    have hvpow :
        (v ^ 2).natDegree =
          v.natDegree + v.natDegree := by
      rw [Polynomial.natDegree_pow]
      omega
    rw [hvpow, pow_two]
    simpa only [pow_two] using
      (Polynomial.resultant_mul_right
        u v v u.natDegree le_rfl)
  change
    f.resultant u f.natDegree u.natDegree =
      (u.resultant v u.natDegree v.natDegree) ^ 2
  calc
    f.resultant u f.natDegree u.natDegree =
        (-1 : ℚ) ^ (f.natDegree * u.natDegree) *
          u.resultant f u.natDegree f.natDegree :=
      Polynomial.resultant_comm f u f.natDegree u.natDegree
    _ = u.resultant f u.natDegree 6 := by
      rw [hsign, one_mul, hfdeg]
    _ =
        u.resultant (v ^ 2 + u * w) u.natDegree 6 := by
      rw [← hdecomp]
    _ = u.resultant (v ^ 2) u.natDegree 6 := by
      exact Polynomial.resultant_add_mul_right
        u (v ^ 2) w u.natDegree 6 hwdeg le_rfl
    _ =
        u.resultant (v ^ 2) u.natDegree
          (v ^ 2).natDegree := hpad
    _ = _ := hsquare

/-- The actual low-degree Kummer value has rational square norm. -/
theorem norm_uTheta_eq_normRoot_sq (D : LowRep) :
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
      normRoot D ^ 2 := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :=
    PowerBasisDiscriminant.norm_aeval_adjoinRoot_eq_resultant
      (N13Mumford.f_monic (K := ℚ))
      N13SexticIrreducible.n13Mumford_f_irreducible
      D.toSemi.u
  calc
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
        (N13Mumford.f ℚ).resultant D.toSemi.u := by
      rw [N13MumfordKummerValue.uTheta_eq_mk]
      change
        Algebra.norm ℚ
            (AdjoinRoot.mk (N13Mumford.f ℚ) D.toSemi.u) =
          (N13Mumford.f ℚ).resultant D.toSemi.u
      rw [← AdjoinRoot.aeval_eq]
      exact hnorm
    _ = normRoot D ^ 2 :=
      resultant_f_u_eq_normRoot_sq D

theorem normRoot_ne_zero (D : LowRep) :
    normRoot D ≠ 0 := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :
      Algebra.norm ℚ
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr
      (N13MumfordKummerValue.uTheta_ne_zero
        (N13LowDegreeKummerHom.asMumford D))
  intro hzero
  apply hnorm
  calc
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
        normRoot D ^ 2 :=
      norm_uTheta_eq_normRoot_sq D
    _ = 0 := by rw [hzero]; simp

/-- The chosen square root of the norm, as a rational unit. -/
def normRootUnit (D : LowRep) : ℚˣ :=
  Units.mk0 (normRoot D) (normRoot_ne_zero D)

@[simp] theorem normRootUnit_val (D : LowRep) :
    (normRootUnit D : ℚ) = normRoot D :=
  rfl

/-- The genuine full norm pair attached to a low-degree Mumford
representative. -/
def mumfordNormPair (D : LowRep) :
    N13FullNormPair.NormPair :=
  ⟨(N13MumfordKummerValue.uThetaUnit
      (N13LowDegreeKummerHom.asMumford D),
    normRootUnit D), by
    apply Units.ext
    exact norm_uTheta_eq_normRoot_sq D⟩

@[simp] theorem mumfordNormPair_fst (D : LowRep) :
    EvenSexticNormPair.fstHom N13FullNormPair.normUnits
        (mumfordNormPair D) =
      N13MumfordKummerValue.uThetaUnit
        (N13LowDegreeKummerHom.asMumford D) :=
  rfl

@[simp] theorem mumfordNormPair_snd (D : LowRep) :
    EvenSexticNormPair.sndHom N13FullNormPair.normUnits
        (mumfordNormPair D) =
      normRootUnit D :=
  rfl

/-- Its class in the full even-sextic descent target. -/
def mumfordFullClass (D : LowRep) :
    N13FullNormPair.FullTarget :=
  QuotientGroup.mk'
    (EvenSexticNormPair.fullGauge
      N13FullNormPair.normUnits
      N13FullNormPair.scalarUnits
      N13FullNormPair.normUnits_scalarUnits)
    (mumfordNormPair D)

end

end MazurProof.N13MumfordKummerNorm

end
end

-- module FLT.Assumptions.MazurProof.N13GlobalKummerNormalization
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerNormalization =====
section

/-!
# Global primitive normalization of N13 Kummer values

A rational Mumford polynomial need not have integral coefficients.  We clear
all denominators simultaneously over `ℤ`, remove the polynomial content, and
evaluate the resulting primitive polynomial at the integral Gaussian-cubic
generator `α + 9`.

The resulting element lies in the actual absolute ring of integers and
differs from the original Kummer value by one nonzero rational scalar.
Primitivity and the degree bound are retained, and the norm of the integral
representative remains a rational square.  Thus denominator clearing is
separated cleanly from the subsequent ideal factorization.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GlobalKummerNormalization

noncomputable section

open N13GaussianFieldEquiv

abbrev L := N13GaussianCubicField.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

local instance intNormalizationMonoid :
    NormalizationMonoid ℤ :=
  UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid

local instance intNormalizedGCDMonoid :
    NormalizedGCDMonoid ℤ :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid ℤ

/-- Clear all rational denominators. -/
def integralNormalization (p : ℚ[X]) : ℤ[X] :=
  IsLocalization.integerNormalization
    (nonZeroDivisors ℤ) p

/-- The primitive integral representative of a rational polynomial,
well-defined up to sign. -/
def primitiveNormalization (p : ℚ[X]) : ℤ[X] :=
  (integralNormalization p).primPart

theorem integralNormalization_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    integralNormalization p ≠ 0 := by
  exact
    (IsFractionRing.integerNormalization_eq_zero_iff
      (A := ℤ) (K := ℚ)).not.mpr hp

theorem integralNormalization_content_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    (integralNormalization p).content ≠ 0 := by
  exact
    Polynomial.content_eq_zero_iff.not.mpr
      (integralNormalization_ne_zero hp)

theorem primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      (primitiveNormalization p).map
          (algebraMap ℤ ℚ) =
        C c * p := by
  let U₀ : ℤ[X] := integralNormalization p
  let U : ℤ[X] := primitiveNormalization p
  obtain ⟨b, hb, hclear⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  have hb0 : b ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbc :
      algebraMap ℤ ℚ b ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne hb0
  have hcontent :
      algebraMap ℤ ℚ U₀.content ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne
      (integralNormalization_content_ne_zero hp)
  let c : ℚ :=
    (algebraMap ℤ ℚ U₀.content)⁻¹ *
      algebraMap ℤ ℚ b
  refine
    ⟨c, mul_ne_zero (inv_ne_zero hcontent) hbc, ?_⟩
  have hdecomp :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ U₀.content) *
          U.map (algebraMap ℤ ℚ) := by
    simpa only [U₀, U, integralNormalization,
      primitiveNormalization, Polynomial.map_mul,
      Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap ℤ ℚ))
        U₀.eq_C_content_mul_primPart
  have hcleared :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
    simpa only [U₀, integralNormalization,
      Algebra.smul_def, Polynomial.algebraMap_apply] using
      hclear
  calc
    U.map (algebraMap ℤ ℚ) =
        1 * U.map (algebraMap ℤ ℚ) := by rw [one_mul]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
            C (algebraMap ℤ ℚ U₀.content)) *
          U.map (algebraMap ℤ ℚ) := by
      rw [← C_mul, inv_mul_cancel₀ hcontent,
        C_1, one_mul]
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ U₀.content) *
            U.map (algebraMap ℤ ℚ)) := by ring
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ b) * p) := by
      rw [← hdecomp, hcleared]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          C (algebraMap ℤ ℚ b)) * p := by ring
    _ = C c * p := by rw [← C_mul]

theorem primitiveNormalization_natDegree_le
    {p : ℚ[X]} (hdeg : p.natDegree ≤ 2) :
    (primitiveNormalization p).natDegree ≤ 2 := by
  rw [primitiveNormalization,
    Polynomial.natDegree_primPart]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_contra hcoeff
  have hnU :
      n ∈ (integralNormalization p).support :=
    Polynomial.mem_support_iff.mpr hcoeff
  have hnp :
      n ∈ p.support :=
    IsLocalization.integerNormalization_support
      (nonZeroDivisors ℤ) p hnU
  have hnle :
      n ≤ 2 :=
    (Polynomial.le_natDegree_of_mem_supp n hnp).trans
      hdeg
  omega

theorem primitiveNormalization_isPrimitive
    (p : ℚ[X]) :
    (primitiveNormalization p).IsPrimitive :=
  (integralNormalization p).isPrimitive_primPart

/-- The integral point corresponding to the sextic generator. -/
def integralTheta : integralClosure ℤ L :=
  ⟨gaussianTheta, gaussianTheta_integral⟩

/-- Evaluate an integral polynomial inside the actual absolute ring of
integers. -/
def integralEval (U : ℤ[X]) :
    integralClosure ℤ L :=
  aeval integralTheta U

@[simp] theorem coe_integralEval (U : ℤ[X]) :
    ((integralEval U : integralClosure ℤ L) : L) =
      eval₂ (algebraMap ℤ L) gaussianTheta U := by
  change
    (Subalgebra.val (integralClosure ℤ L))
        (eval₂
          (algebraMap ℤ (integralClosure ℤ L))
          integralTheta U) =
      eval₂ (algebraMap ℤ L) gaussianTheta U
  have h :=
    Polynomial.hom_eval₂ U
      (algebraMap ℤ (integralClosure ℤ L))
      (Subalgebra.val (integralClosure ℤ L)).toRingHom
      integralTheta
  have hmaps :
      (Subalgebra.val
          (integralClosure ℤ L)).toRingHom.comp
          (algebraMap ℤ (integralClosure ℤ L)) =
        algebraMap ℤ L :=
    RingHom.ext_int _ _
  calc
    (Subalgebra.val (integralClosure ℤ L))
        (eval₂
          (algebraMap ℤ (integralClosure ℤ L))
          integralTheta U) =
        eval₂
          ((Subalgebra.val
              (integralClosure ℤ L)).toRingHom.comp
            (algebraMap ℤ (integralClosure ℤ L)))
          ((Subalgebra.val
            (integralClosure ℤ L)) integralTheta) U :=
      h
    _ =
        eval₂ (algebraMap ℤ L) gaussianTheta U := by
      rw [hmaps]
      rfl

theorem integralEval_primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((integralEval (primitiveNormalization p) :
          integralClosure ℤ L) : L) =
        algebraMap ℚ L c *
          eval₂ (algebraMap ℚ L) gaussianTheta p := by
  obtain ⟨c, hc, hpoly⟩ :=
    primitiveNormalization_spec hp
  refine ⟨c, hc, ?_⟩
  calc
    ((integralEval (primitiveNormalization p) :
        integralClosure ℤ L) : L) =
        eval₂ (algebraMap ℤ L) gaussianTheta
          (primitiveNormalization p) := by
      rw [coe_integralEval]
    _ =
        eval₂ (algebraMap ℚ L) gaussianTheta
          ((primitiveNormalization p).map
            (algebraMap ℤ ℚ)) := by
      rw [Polynomial.eval₂_map,
        IsScalarTower.algebraMap_eq ℤ ℚ L]
    _ =
        eval₂ (algebraMap ℚ L) gaussianTheta
          (C c * p) := by rw [hpoly]
    _ =
        algebraMap ℚ L c *
          eval₂ (algebraMap ℚ L) gaussianTheta p := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]

/-- The global integral representative of a low-degree Kummer value. -/
def normalizedKummerInteger
    (D : N13LowDegreeKummerHom.LowRep) :
    integralClosure ℤ L :=
  integralEval
    (primitiveNormalization D.toSemi.u)

theorem normalizedKummerInteger_spec
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((normalizedKummerInteger D :
          integralClosure ℤ L) : L) =
        algebraMap ℚ L c *
          sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) := by
  have hu : D.toSemi.u ≠ 0 :=
    D.toSemi.u_monic.ne_zero
  obtain ⟨c, hc, hspec⟩ :=
    integralEval_primitiveNormalization_spec hu
  refine ⟨c, hc, ?_⟩
  rw [normalizedKummerInteger]
  rw [N13MumfordKummerValue.uTheta_eq_mk]
  change
    ((integralEval
        (primitiveNormalization D.toSemi.u) :
        integralClosure ℤ L) : L) =
      algebraMap ℚ L c *
        sexticEquivGaussian
          (N13SexticSquareclass.ofPoly D.toSemi.u)
  rw [sexticEquivGaussian_ofPoly]
  exact hspec

theorem normalizedKummerInteger_degree
    (D : N13LowDegreeKummerHom.LowRep) :
    (primitiveNormalization D.toSemi.u).natDegree ≤ 2 :=
  primitiveNormalization_natDegree_le D.degree_le_two

/-- The integral representative retains the square-norm condition; its
square root is simply rescaled by the cube of the rational normalization
factor. -/
theorem normalizedKummerInteger_norm_isSquare
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ s : ℚ,
      Algebra.norm ℚ
          (((normalizedKummerInteger D :
              integralClosure ℤ L) : L)) =
        s ^ 2 := by
  obtain ⟨c, hc, hspec⟩ :=
    normalizedKummerInteger_spec D
  refine
    ⟨c ^ 3 * N13MumfordKummerNorm.normRoot D, ?_⟩
  have hnorm :
      Algebra.norm ℚ
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) =
        N13MumfordKummerNorm.normRoot D ^ 2 :=
    N13MumfordKummerNorm.norm_uTheta_eq_normRoot_sq D
  have hnormGaussian :
      Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) =
        N13MumfordKummerNorm.normRoot D ^ 2 := by
    calc
      Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) =
          Algebra.norm ℚ
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) :=
        Algebra.norm_eq_of_algEquiv
          N13GaussianFieldEquiv.sexticEquivGaussian _
      _ = _ := hnorm
  rw [hspec, map_mul, Algebra.norm_algebraMap,
    N13GaussianFieldEquiv.finrank_Lg,
    hnormGaussian]
  ring

end

end MazurProof.N13GlobalKummerNormalization

end
end

-- module FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare =====
section

/-!
# The branch ideal of an N13 Mumford relation is a square

The identity behind the good-prime part of the two-descent is

`(u(θ), v(θ))² = (u(θ))`.

It follows without factoring `u`, splitting into its possible degrees, or
computing valuations.  If `f - v² = u w`, then any prime containing both
`u(θ)` and `w(θ)` also contains `v(θ)` and hence `f'(θ)`.  Thus, wherever
`f'(θ)` is a unit, `u(θ)` and `w(θ)` are coprime.  Bézout and
`u(θ)w(θ) = -v(θ)²` then give the displayed ideal identity.

For N13 we implement "away from the different" literally: start with the
integral monogenic order and invert `f'(θ)`.  No discriminant expansion or
prime-ideal table enters the proof.
-/

open Polynomial

namespace MazurProof.N13MumfordKummerIdealSquare

noncomputable section

variable {R : Type*} [CommRing R]

/-! The N13 monogenic order with its different inverted. -/

abbrev IntegralOrder : Type :=
  AdjoinRoot N13SexticIrreducible.fInt

def integralTheta : IntegralOrder :=
  AdjoinRoot.root N13SexticIrreducible.fInt

def differentGenerator : IntegralOrder :=
  AdjoinRoot.mk N13SexticIrreducible.fInt
    N13SexticIrreducible.fInt.derivative

abbrev GoodOrder : Type :=
  Localization.Away differentGenerator

end

end MazurProof.N13MumfordKummerIdealSquare

end
end

-- module FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare =====
section

/-!
# The good-locus square ideal of a normalized N13 Kummer value

Primitive normalization removes the arbitrary content of a rational
Mumford polynomial, but it does not make the other polynomial in the
Mumford pair integral.  We clear those remaining denominators
*homogeneously*: if

`f - v² = u w`

and `U = c u` is the primitive integral normalization, then a single
nonzero integer `d` can be chosen together with integral `V,W` so that

`d² f - V² = U W`.

After evaluating at the integral branch point and inverting the derivative
of `d² f`, the branch ideal `(U(θ),V(θ))` squares to `(U(θ))`.  This is the
principal ideal of the previously constructed `normalizedKummerInteger`.
Thus every denominator and bad-reduction prime is isolated in one
canonical localization; no prime factorization or valuation enumeration is
used.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GlobalKummerIdealSquare

noncomputable section

open N13GaussianFieldEquiv
open N13GlobalKummerNormalization

abbrev L := N13GaussianCubicField.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

abbrev O := integralClosure ℤ L

/-- Every rational polynomial has a nonzero integral scalar multiple with
integral coefficients. -/
theorem exists_integral_scalar_multiple (p : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ P : ℤ[X],
      P.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
  obtain ⟨b, hb, hP⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  exact
    ⟨b, mem_nonZeroDivisors_iff_ne_zero.mp hb,
      IsLocalization.integerNormalization
        (nonZeroDivisors ℤ) p, by
          simpa only [Algebra.smul_def,
            Polynomial.algebraMap_apply] using hP⟩

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Integral homogeneous Mumford data whose first polynomial is exactly the
primitive normalization used by `normalizedKummerInteger`. -/
structure ScaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) where
  scale : ℤ
  scale_ne_zero : scale ≠ 0
  v : ℤ[X]
  w : ℤ[X]
  curve :
    C (scale ^ 2) * N13SexticIrreducible.fInt -
        v ^ 2 =
      primitiveNormalization D.toSemi.u * w

/-- Simultaneous denominator clearing preserves the Mumford equation in
homogeneous form. -/
theorem exists_scaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) :
    Nonempty (ScaledIntegralMumford D) := by
  obtain ⟨w, hw⟩ := D.toSemi.curve_dvd
  change
    N13Mumford.f ℚ - D.toSemi.v ^ 2 =
      D.toSemi.u * w at hw
  obtain ⟨c, hc, hU⟩ :=
    primitiveNormalization_spec D.toSemi.u_monic.ne_zero
  obtain ⟨bV, hbV, V₀, hV₀⟩ :=
    exists_integral_scalar_multiple D.toSemi.v
  obtain ⟨bW, hbW, W₀, hW₀⟩ :=
    exists_integral_scalar_multiple (C c⁻¹ * w)
  let d : ℤ := bV * bW
  let V : ℤ[X] := C bW * V₀
  let W : ℤ[X] := (C bV) ^ 2 * C bW * W₀
  have hd : d ≠ 0 :=
    mul_ne_zero hbV hbW
  have hV :
      V.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ d) * D.toSemi.v := by
    simp only [V, d, Polynomial.map_mul, Polynomial.map_C,
      hV₀, map_mul]
    ring
  have hW :
      W.map (algebraMap ℤ ℚ) =
        C ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) * w := by
    simp only [W, d, Polynomial.map_mul, Polynomial.map_C,
      hW₀, map_mul, map_pow]
    rw [Polynomial.map_pow, Polynomial.map_C]
    ring
  refine ⟨⟨d, hd, V, W, ?_⟩⟩
  apply Polynomial.map_injective
    (f := algebraMap ℤ ℚ)
    (IsFractionRing.injective ℤ ℚ)
  simp only [Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, hV, hW, hU,
    map_pow]
  rw [N13SexticIrreducible.fInt_map_rat]
  have hcInv : c * c⁻¹ = 1 :=
    mul_inv_cancel₀ hc
  have hscalar :
      C c * C ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) =
        C (algebraMap ℤ ℚ d) ^ 2 := by
    rw [← C_mul, ← C_pow]
    congr 1
    calc
      c * ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) =
          (c * c⁻¹) * (algebraMap ℤ ℚ d) ^ 2 := by ring
      _ = _ := by rw [hcInv, one_mul]
  rw [show
    C (algebraMap ℤ ℚ d) ^ 2 *
          N13Mumford.f ℚ -
        (C (algebraMap ℤ ℚ d) * D.toSemi.v) ^ 2 =
      C (algebraMap ℤ ℚ d) ^ 2 *
        (N13Mumford.f ℚ - D.toSemi.v ^ 2) by ring,
    hw]
  rw [← hscalar]
  ring

/-- A fixed structural choice of the homogeneous integral Mumford data. -/
def scaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) :
    ScaledIntegralMumford D :=
  Classical.choice (exists_scaledIntegralMumford D)

/-- The homogeneously scaled integral curve polynomial. -/
def scaledCurve
    (D : N13LowDegreeKummerHom.LowRep) : ℤ[X] :=
  C ((scaledIntegralMumford D).scale ^ 2) *
    N13SexticIrreducible.fInt

theorem scaledCurve_relation
    (D : N13LowDegreeKummerHom.LowRep) :
    scaledCurve D -
        (scaledIntegralMumford D).v ^ 2 =
      primitiveNormalization D.toSemi.u *
        (scaledIntegralMumford D).w :=
  (scaledIntegralMumford D).curve

/-- The integral branch point is a root of the original sextic. -/
@[simp] theorem integralTheta_root_fInt :
    aeval integralTheta N13SexticIrreducible.fInt = 0 := by
  change
    integralEval N13SexticIrreducible.fInt = 0
  apply Subtype.ext
  have hrat :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.map
          (algebraMap ℤ ℚ)) = 0 := by
    rw [N13SexticIrreducible.fInt_map_rat]
    exact gaussianTheta_root_sextic
  rw [coe_integralEval]
  change
    eval₂ (algebraMap ℤ L) gaussianTheta
      N13SexticIrreducible.fInt = (0 : L)
  simpa only [eval₂_map,
      IsScalarTower.algebraMap_eq ℤ ℚ L] using hrat

/-- The derivative whose nonvanishing defines the good locus for this
normalized representative.  Its two factors are the denominator scale and
the ordinary different generator. -/
def badGenerator
    (D : N13LowDegreeKummerHom.LowRep) : O :=
  integralEval (scaledCurve D).derivative

theorem badGenerator_eq_scale_mul_different
    (D : N13LowDegreeKummerHom.LowRep) :
    badGenerator D =
      algebraMap ℤ O ((scaledIntegralMumford D).scale ^ 2) *
        integralEval N13SexticIrreducible.fInt.derivative := by
  simp only [badGenerator, scaledCurve, derivative_mul,
    derivative_C, zero_mul, zero_add, integralEval, map_mul,
    aeval_C]

theorem differentInteger_ne_zero :
    integralEval
      N13SexticIrreducible.fInt.derivative ≠ 0 := by
  have hrootQ :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ) = 0 := by
    simpa [N13SexticSquareclass.f] using
      gaussianTheta_root_sextic
  have hderivQ :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ).derivative ≠ 0 :=
    (N13Mumford.f_separable ℚ).eval₂_derivative_ne_zero
      (algebraMap ℚ L) hrootQ
  intro hzero
  apply hderivQ
  have hcoe :
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
        N13SexticIrreducible.fInt.derivative = 0 := by
    calc
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
          N13SexticIrreducible.fInt.derivative =
        ((integralEval
          N13SexticIrreducible.fInt.derivative : O) :
            N13GlobalKummerNormalization.L) :=
              (coe_integralEval _).symm
      _ = ((0 : O) :
          N13GlobalKummerNormalization.L) := by rw [hzero]
      _ = 0 := by rfl
  have hmaps :
      (algebraMap ℚ L).comp (algebraMap ℤ ℚ) =
        algebraMap ℤ
          N13GlobalKummerNormalization.L :=
    RingHom.ext_int _ _
  calc
    eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ).derivative =
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.map
          (algebraMap ℤ ℚ)).derivative := by
            rw [N13SexticIrreducible.fInt_map_rat]
    _ =
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.derivative.map
          (algebraMap ℤ ℚ)) := by
            rw [derivative_map]
    _ =
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
        N13SexticIrreducible.fInt.derivative := by
            rw [eval₂_map, hmaps]
    _ = 0 := hcoe

theorem badGenerator_ne_zero
    (D : N13LowDegreeKummerHom.LowRep) :
    badGenerator D ≠ 0 := by
  rw [badGenerator_eq_scale_mul_different]
  have hOinj :
      Function.Injective (algebraMap ℤ O) := by
    intro a b hab
    have habL :=
      congrArg
        (Subalgebra.val
          (integralClosure ℤ L)).toRingHom hab
    have hmapO :
        (Subalgebra.val
            (integralClosure ℤ L)).toRingHom.comp
            (algebraMap ℤ O) =
          algebraMap ℤ L :=
      RingHom.ext_int _ _
    have habZL :
        algebraMap ℤ L a = algebraMap ℤ L b := by
      rw [← hmapO]
      exact habL
    have hmapZL :
        algebraMap ℤ L =
          (algebraMap ℚ L).comp (algebraMap ℤ ℚ) :=
      RingHom.ext_int _ _
    rw [hmapZL] at habZL
    exact
      (IsFractionRing.injective ℤ ℚ)
        ((algebraMap ℚ L).injective habZL)
  have hscale :
      algebraMap ℤ O
          ((scaledIntegralMumford D).scale ^ 2) ≠ 0 := by
    simpa only [map_zero] using
      hOinj.ne
        (pow_ne_zero 2
          (scaledIntegralMumford D).scale_ne_zero)
  exact mul_ne_zero hscale differentInteger_ne_zero

/-- The ring obtained by removing exactly the denominator and different
locus attached to a normalized Mumford representative. -/
abbrev GoodOrder
    (D : N13LowDegreeKummerHom.LowRep) : Type :=
  Localization.Away (badGenerator D)

local instance goodOrderIsDomain
    (D : N13LowDegreeKummerHom.LowRep) :
    IsDomain (GoodOrder D) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (GoodOrder D)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (badGenerator_ne_zero D))

/-! ## The principal-ideal endpoint -/

end

end MazurProof.N13GlobalKummerIdealSquare

end
end

-- module FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic =====
section
/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/


/-!
# Basic

Material destined for Mathlib.
-/

section

theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R
end
end
end

-- module FLT.Mathlib.RingTheory.Valuation.ValuationSubring
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Mathlib.RingTheory.Valuation.ValuationSubring =====
section
/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
-/


/-!
# Valuation Subring

Material destined for Mathlib.
-/

section

variable {F : Type*} [Field F]

theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _

theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩

theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩
end
end
end

-- module FLT.DedekindDomain.AdicValuation
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false in
-- ===== FLT.DedekindDomain.AdicValuation =====
section
/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/


/-!

# Adic Completions

If `A` is a valued ring with field of fractions `K` there are two different
complete rings containing `A` one might define, the first is
`𝒪_v = {x ∈ K_v | v x ≤ 1}` (defined in Lean as `adicCompletionIntegers K v`)
and the second is the `v-adic` completion of `A`. In the case when `A` is a
Dedekind domain these definitions give isomorphic topological `A`-algebras.
This file makes some progress towards this.

## Main theorems/defs

* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_integers` : The closure of
    `A` in `K_v` is `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField` : The canonical
  isomorphism `A ⧸ v ≅ 𝓞ᵥ / v`.
* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_prodIntegers` : If `s` is
    a set of primes of `A`, then the closure of `A` in `∏_{v ∈ s} K_v` is `∏_{v ∈ s} 𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.denseRange_of_prodAlgebraMap` : If `s` is a finite set
    of primes of `A`, then `K` is dense in `∏_{v ∈ s} K_v`.
* We show (as an unnamed instance) `IsDiscreteValuationRing (𝒪[v.adicCompletion K])`
-/

section

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero

lemma exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  lift y to Multiplicative ℤ using hnz
  use y.natAbs
  apply lt_of_le_of_lt _ hyx
  rw [← ofAdd_toAdd y, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  change -((Multiplicative.toAdd y).natAbs : ℤ) ≤ Multiplicative.toAdd y
  omega

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

open scoped WithZero


-- could go in mathlib
instance : Valuation.IsRankOneDiscrete ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

/-- The maximal ideal of the integers of the completion of `v`. -/
noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)

lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl

instance : (v.completionIdeal K).LiesOver v.asIdeal := ⟨by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]⟩

-- shortcut instances for next def: needed after mathlib #34045
noncomputable instance : CommSemiring ↥(adicCompletionIntegers K v) := inferInstance
noncomputable instance : Field (adicCompletion K v) := inferInstance

-- dirty hack because of v4.29

namespace adicCompletion

-- IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
open scoped algebraMap in
theorem exists_uniformizer (v : HeightOneSpectrum A) :
    ∃ π : v.adicCompletionIntegers K, Valued.v π.1 = Multiplicative.ofAdd (- 1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  use π
  rw [← WithZero.exp, ← hπ, ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]

variable {K} in
theorem uniformizer_ne_zero {v : HeightOneSpectrum A}
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  simp [hπ]

-- shortcut instance for next theorem: needed after mathlib #34045
noncomputable instance : Ring (adicCompletion K v) := inferInstance

variable {K} in
open scoped Multiplicative in
theorem uniformizer_not_isUnit {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬IsUnit (π : v.adicCompletionIntegers K) := by
  rw [ValuationSubring.isUnit_iff_valued_eq_one, ← WithZero.coe_one, ← ofAdd_zero, hπ]
  apply ne_of_lt
  rw [WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  omega

theorem eq_pow_uniformizer_mul_unit {x : v.adicCompletionIntegers K} (hx : x ≠ 0)
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  have hx' : Valued.v x.1 ≠ 0 := by simp [hx]
  let m := - Multiplicative.toAdd (WithZero.unzero hx')
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv,
      inv_zpow', neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd,
      WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel₀ hx']
  let a : v.adicCompletionIntegers K := ⟨π ^ (-m) * x.val, (mem_adicCompletionIntegers _ K v).mpr (le_of_eq hpow)⟩
  refine ⟨m.toNat, (ValuationSubring.isUnit_of_valued_eq_one a hpow).unit, Subtype.ext ?_⟩
  change x.val = (π : v.adicCompletion K) ^ m.toNat * ((π : v.adicCompletion K) ^ (-m) * x.val)
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by simp [uniformizer_ne_zero hπ]
  rw [← mul_assoc, ← zpow_natCast, m.toNat_of_nonneg hm₀, ← zpow_add₀ hπ0, add_neg_cancel,
    zpow_zero, one_mul]

open scoped algebraMap in
theorem maximalIdeal_eq_span_uniformizer {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {(π : v.adicCompletionIntegers K)} := by
  refine (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (uniformizer_not_isUnit v hπ)) (fun x hx => ?_)
  by_cases hx₀ : x = 0
  · simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit K v hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self π hn

instance : Ring.DimensionLEOne (v.adicCompletionIntegers K) where
  maximalOfPrime {𝔭} h𝔭_ne_bot h𝔭_prime := by
    let ⟨x, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭_ne_bot
    let ⟨π, hπ⟩ := exists_uniformizer K v
    obtain ⟨n, ⟨u, rfl⟩⟩ := eq_pow_uniformizer_mul_unit K v hx.2 hπ
    simp only [Units.isUnit, Ideal.mul_unit_mem_iff_mem, ne_eq, mul_eq_zero, pow_eq_zero_iff',
      Units.ne_zero, or_false, not_and, Decidable.not_not] at hx
    by_cases hn : n = 0
    · simp only [hn, pow_zero, ← 𝔭.eq_top_iff_one, implies_true, and_true] at hx
      exact h𝔭_prime.ne_top hx |>.elim
    · rw [h𝔭_prime.pow_mem_iff_mem n (by omega), ← 𝔭.span_singleton_le_iff_mem,
        ← maximalIdeal_eq_span_uniformizer K v hπ] at hx
      exact IsLocalRing.maximalIdeal_le h𝔭_prime.ne_top hx.1

open scoped algebraMap in
instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  apply IsPrincipalIdealRing.of_prime
  intro P hP
  by_cases hP_bot : P = ⊥
  · exact hP_bot ▸ bot_isPrincipal
  · let ⟨π, hπ⟩ := exists_uniformizer K v
    use π
    rw [IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_bot)]
    exact maximalIdeal_eq_span_uniformizer K v hπ

instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    let ⟨π, hπ⟩ := exists_uniformizer K v
    rw [maximalIdeal_eq_span_uniformizer K v hπ]
    intro h
    simp only [Ideal.span_singleton_eq_bot] at h
    exact uniformizer_ne_zero hπ h

open scoped Valued in
instance : IsDiscreteValuationRing (𝒪[v.adicCompletion K]) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))

lemma mem_completionIdeal_pow {n : ℕ} (x : v.adicCompletionIntegers K) :
    x ∈ (v.completionIdeal K) ^ n ↔ Valued.v x.val ≤ ↑(Multiplicative.ofAdd (-(n : ℤ))) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  unfold completionIdeal
  rw [maximalIdeal_eq_span_uniformizer K v hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hvalπ_pow : (Valued.v π.val) ^ n = (Multiplicative.ofAdd (-n : ℤ)) := by
    rw [hπ]
    norm_num
    norm_cast
    rw [← ofAdd_nsmul, Nat.smul_one_eq_cast]
  constructor
  · rintro ⟨a, rfl⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ofAdd_neg,
      WithZero.coe_inv]
    apply mul_le_of_le_one_of_le a.prop <| le_of_eq hvalπ_pow
  · intro hx
    set a := x.val / (π ^ n) with ha'
    have ha : Valued.v a ≤ 1 := by
      rwa [ha', Valuation.map_div, Valuation.map_pow, hvalπ_pow,
        div_le_one₀ (WithZero.zero_lt_coe _)]
    use ⟨a, ha⟩
    apply Subtype.val_injective
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ha']
    rw [div_mul_eq_mul_div₀, mul_div_cancel_right₀]
    apply pow_ne_zero n
    norm_cast
    exact uniformizer_ne_zero hπ

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum
end
end
end


