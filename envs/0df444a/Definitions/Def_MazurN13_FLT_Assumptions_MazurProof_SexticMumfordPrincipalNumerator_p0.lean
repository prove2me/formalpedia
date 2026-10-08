-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrincipalNumerator_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrincipalNumerator_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:02:01.210291+00:00
-- url     : https://prove2.me/theorems/610bdcf2-97e1-4ed7-8300-0e9f401d4f9d
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdealConjugation_p0

set_option autoImplicit false




/-!
# Integral numerators from principal relations

For a principal relation between two Mumford ideals, multiplying the
principal generator by the first `u`-polynomial clears all affine
denominator.  The proof is ideal-theoretic: the first Mumford ideal times its
hyperelliptic conjugate is the principal ideal `(u)`.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem exists_numerator_mem_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z : CoordinateRing M,
      z ∈ mumfordIdeal M D₂.u D₂.v ∧
        algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) := by
  have hx :
      algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) ∈
        (mumfordIdealUnit M D₁ :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
    rw [coe_mumfordIdealUnit]
    exact FractionalIdeal.mem_coeIdeal_of_mem (CoordinateRing M)⁰
      (xClass_mem_mumfordIdeal M D₁.u D₁.v)
  have hα :
      (α : FunctionField M) ∈
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hprod := FractionalIdeal.mul_mem_mul hx hα
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) h
  rw [Units.val_mul, coe_toPrincipalIdeal, coe_mumfordIdealUnit,
    coe_mumfordIdealUnit] at hfrac
  rw [coe_mumfordIdealUnit, coe_toPrincipalIdeal] at hprod
  rw [hfrac] at hprod
  obtain ⟨z, hzmem, hzeq⟩ :=
    (FractionalIdeal.mem_coeIdeal (CoordinateRing M)⁰).mp hprod
  exact ⟨z, hzmem, by simpa [mul_comm] using hzeq⟩

theorem exists_integral_numerator_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z : CoordinateRing M,
      algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) := by
  obtain ⟨z, -, hz⟩ :=
    exists_numerator_mem_of_principal_relation M D₁ D₂ α h
  exact ⟨z, hz⟩

theorem reverse_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M D₂ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α⁻¹ =
        mumfordIdealUnit M D₁ := by
  rw [← h]
  simp only [mul_assoc, map_inv, mul_inv_cancel, mul_one]

theorem exists_integral_conumerator_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ w : CoordinateRing M,
      algebraMap (CoordinateRing M) (FunctionField M) w =
        (↑α⁻¹ : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₂.u) := by
  exact exists_integral_numerator_of_principal_relation M D₂ D₁ α⁻¹
    (reverse_principal_relation M D₁ D₂ α h)

theorem exists_integral_factor_pair_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z w : CoordinateRing M,
      z ∈ mumfordIdeal M D₂.u D₂.v ∧
      w ∈ mumfordIdeal M D₁.u D₁.v ∧
      z * w = xClass M (D₁.u * D₂.u) ∧
      algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) ∧
      algebraMap (CoordinateRing M) (FunctionField M) w =
        (↑α⁻¹ : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₂.u) := by
  obtain ⟨z, hzmem, hzeq⟩ :=
    exists_numerator_mem_of_principal_relation M D₁ D₂ α h
  obtain ⟨w, hwmem, hweq⟩ :=
    exists_numerator_mem_of_principal_relation M D₂ D₁ α⁻¹
      (reverse_principal_relation M D₁ D₂ α h)
  refine ⟨z, w, hzmem, hwmem, ?_, hzeq, hweq⟩
  apply IsFractionRing.injective (CoordinateRing M) (FunctionField M)
  rw [map_mul, hzeq, hweq, xClass_mul, map_mul]
  change
    ((α : FunctionField M) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u)) *
      ((↑α⁻¹ : FunctionField M) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u)) =
      algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u)
  rw [Units.val_inv_eq_inv_val]
  field_simp

end

end MazurProof.SexticMumford


