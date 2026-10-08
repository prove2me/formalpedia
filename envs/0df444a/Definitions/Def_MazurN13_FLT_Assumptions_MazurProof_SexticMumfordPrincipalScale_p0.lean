-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrincipalScale_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrincipalScale_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:03:24.227984+00:00
-- url     : https://prove2.me/theorems/d20dd218-44a8-4731-b7b2-d29394ae00ed
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrincipalNumerator_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0

set_option autoImplicit false




/-!
# Cancelling a principal scale between Mumford ideals

If a principal fractional-ideal relation scales the first polynomial
generator to a unit multiple of the second, the associated integral
Mumford ideals satisfy the cross-multiplied equality.  Contracting that
equality to the polynomial subring recovers equality of the monic
`u`-polynomials.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u v

theorem scaled_ideal_eq_of_principal_scale
    {R : Type u} [CommRing R]
    {L : Type v} [Field L] [Algebra R L] [IsFractionRing R L]
    (I₁ I₂ : Ideal R) (α : Lˣ) (u₁ u₂ c d : R)
    (hIdeal :
      (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (α : L) = I₂)
    (hscale : (α : L) * algebraMap R L u₁ =
      algebraMap R L u₂ * algebraMap R L c)
    (hunit : c * d = 1) :
    I₁ * Ideal.span ({u₂} : Set R) =
      I₂ * Ideal.span ({u₁} : Set R) := by
  apply (FractionalIdeal.coeIdeal_inj (K := L)).mp
  have hc : IsUnit c := IsUnit.of_mul_eq_one d hunit
  have hspan_c :
      FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) = 1 := by
    calc
      FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) =
          (Ideal.span ({c} : Set R) : FractionalIdeal R⁰ L) :=
        (FractionalIdeal.coeIdeal_span_singleton c).symm
      _ = (⊤ : Ideal R) := by
        rw [Ideal.span_singleton_eq_top.mpr hc]
      _ = 1 := by simp
  calc
    ((I₁ * Ideal.span ({u₂} : Set R) : Ideal R) :
          FractionalIdeal R⁰ L) =
        (I₁ : FractionalIdeal R⁰ L) *
          (Ideal.span ({u₂} : Set R) : FractionalIdeal R⁰ L) :=
      FractionalIdeal.coeIdeal_mul I₁ (Ideal.span ({u₂} : Set R))
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₂) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₂) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) := by
      rw [hspan_c, mul_one]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰
            (algebraMap R L u₂ * algebraMap R L c) := by
      rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰
            ((α : L) * algebraMap R L u₁) := by
      rw [hscale]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          (FractionalIdeal.spanSingleton R⁰ (α : L) *
            FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁)) := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ =
        ((I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (α : L)) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁) := by
      rw [mul_assoc]
    _ =
        (I₂ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁) := by
      rw [hIdeal]
    _ =
        (I₂ : FractionalIdeal R⁰ L) *
          (Ideal.span ({u₁} : Set R) : FractionalIdeal R⁰ L) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        ((I₂ * Ideal.span ({u₁} : Set R) : Ideal R) :
          FractionalIdeal R⁰ L) := by
      exact
        (FractionalIdeal.coeIdeal_mul I₂
          (Ideal.span ({u₁} : Set R))).symm

theorem mumford_u_eq_of_principal_scale
    {K : Type u} [Field K] (M : Model K)
    (D₁ D₂ : SemiMumford M) (α : (FunctionField M)ˣ)
    (c d : CoordinateRing M)
    (hIdeal :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂)
    (hscale :
      (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) =
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u) *
          algebraMap (CoordinateRing M) (FunctionField M) c)
    (hunit : c * d = 1) :
    D₁.u = D₂.u := by
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) hIdeal
  rw [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit, coe_mumfordIdealUnit] at hfrac
  have hscaled := scaled_ideal_eq_of_principal_scale
    (mumfordIdeal M D₁.u D₁.v)
    (mumfordIdeal M D₂.u D₂.v)
    α (xClass M D₁.u) (xClass M D₂.u) c d
    hfrac hscale hunit
  have h₁₂ := u_dvd_of_scaled_mumfordIdeal_eq
    M D₁.u D₁.v D₂.u D₂.v hscaled
  have h₂₁ := u_dvd_of_scaled_mumfordIdeal_eq
    M D₂.u D₂.v D₁.u D₁.v hscaled.symm
  exact Polynomial.eq_of_monic_of_associated D₁.u_monic D₂.u_monic
    (associated_of_dvd_dvd h₁₂ h₂₁)

end

end MazurProof.SexticMumford


