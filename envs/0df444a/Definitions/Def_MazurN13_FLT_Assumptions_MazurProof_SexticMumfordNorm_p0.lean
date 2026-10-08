-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:50:28.9977+00:00
-- url     : https://prove2.me/theorems/d0ac97f1-7b35-4f3f-811f-2e803a1ea9ba
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordNorm source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordNorm

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordNorm
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0

set_option autoImplicit false




/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem xClass_injective (M : Model K) :
    Function.Injective (xClass M) := by
  intro p q hpq
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  exact xClass_ne_zero M hsub (by
    rw [xClass_sub, hpq, sub_self])

theorem norm_mul (M : Model K) (z w : CoordinateRing M) :
    norm M (z * w) = norm M z * norm M w := by
  simp only [norm, map_mul]
  ring

@[simp] theorem norm_xClass (M : Model K) (p : K[X]) :
    norm M (xClass M p) = xClass M (p ^ 2) := by
  calc
    norm M (xClass M p) = xClass M p * xClass M p := by
      simp only [norm, conjugate_xClass]
    _ = xClass M (p * p) := (xClass_mul M p p).symm
    _ = xClass M (p ^ 2) := by rw [pow_two]

theorem norm_eq_xClass_coeff (M : Model K) (z : CoordinateRing M) :
    norm M z =
      xClass M
        ((coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f) := by
  conv_lhs =>
    rw [← recompose M z]
  exact norm_recompose M (coeff0 M z) (coeffY M z)

@[simp] theorem coeffY_xClass_mul (M : Model K)
    (a : K[X]) (z : CoordinateRing M) :
    coeffY M (xClass M a * z) = a * coeffY M z := by
  rw [show xClass M a =
    algebraMap K[X] (CoordinateRing M) a from rfl]
  rw [← Algebra.smul_def, map_smul]
  rfl

@[simp] theorem coeffY_ySubClass (M : Model K) (v : K[X]) :
    coeffY M (ySubClass M v) = 1 := by
  simp [ySubClass]

theorem dvd_of_xClass_mul_ySubClass_mem_span
    (M : Model K) (u a v : K[X])
    (h : xClass M a * ySubClass M v ∈
      Ideal.span ({xClass M u} : Set (CoordinateRing M))) :
    u ∣ a := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨coeffY M t, ?_⟩
  have hc := congrArg (coeffY M) ht
  rw [coeffY_xClass_mul, coeffY_ySubClass, mul_one,
    coeffY_xClass_mul] at hc
  exact hc

theorem u_dvd_of_scaled_mumfordIdeal_eq
    (M : Model K) (u₁ v₁ u₂ v₂ : K[X])
    (h :
      mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) =
        mumfordIdeal M u₂ v₂ *
          Ideal.span ({xClass M u₁} : Set (CoordinateRing M))) :
    u₁ ∣ u₂ := by
  have hyv :
      ySubClass M v₁ ∈ mumfordIdeal M u₁ v₁ :=
    Ideal.subset_span (by simp)
  have hu :
      xClass M u₂ ∈
        Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.subset_span (by simp)
  have hmem :
      ySubClass M v₁ * xClass M u₂ ∈
        mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.mul_mem_mul hyv hu
  rw [h] at hmem
  have hspan :
      xClass M u₂ * ySubClass M v₁ ∈
        Ideal.span ({xClass M u₁} : Set (CoordinateRing M)) := by
    rw [mul_comm]
    exact Ideal.mul_le_right hmem
  exact dvd_of_xClass_mul_ySubClass_mem_span M u₁ u₂ v₁ hspan

end

end MazurProof.SexticMumford


