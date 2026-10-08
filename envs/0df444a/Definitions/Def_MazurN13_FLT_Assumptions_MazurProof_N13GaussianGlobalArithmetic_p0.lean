-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalArithmetic_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalArithmetic_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:46:33.070305+00:00
-- url     : https://prove2.me/theorems/75289f1b-d5c0-4496-ae75-dc41af49e7c1
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

set_option autoImplicit false




/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/

open Polynomial

namespace MazurProof.N13GaussianGlobalArithmetic

noncomputable section

abbrev GI := GaussianInt

/-- The standard Gaussian generator. -/
def i : GI := Zsqrtd.sqrtd

/-- The Gaussian prime above `13` at which the cubic is ramified. -/
def pi : GI := 3 - 2 * i

/-- The cubic Gaussian factor of the actual N13 sextic. -/
def g : GI[X] :=
  X ^ 3 + C (2 - 2 * i) * X ^ 2 +
    C (-1 - 2 * i) * X - 1

/-- The conjugate Gaussian cubic. -/
def gConj : GI[X] :=
  X ^ 3 + C (2 + 2 * i) * X ^ 2 +
    C (-1 + 2 * i) * X - 1

/-- Coefficient guard for the only N13 sextic used in this development. -/
def n13F : GI[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 +
    X ^ 2 + 2 * X + 1

/-- The translate for which the ramified cubic is Eisenstein. -/
def h : GI[X] :=
  g.comp (X + C 9)

@[simp] theorem i_sq : i ^ 2 = -1 := by
  rfl

/-- The displayed cubic and its conjugate recover the exact N13 sextic. -/
theorem g_mul_conj :
    g * gConj = n13F := by
  have hCi : (C i : GI[X]) ^ 2 = -1 := by
    rw [← map_pow, i_sq, map_neg, map_one]
  simp only [g, gConj, n13F, map_add, map_sub, map_mul,
    map_ofNat, map_neg, map_one]
  ring_nf
  rw [hCi]
  ring

@[simp] theorem pi_norm : Zsqrtd.norm pi = 13 := by
  norm_num [pi, i, Zsqrtd.norm]

theorem pi_ne_zero : pi ≠ 0 := by
  intro hp
  have hnorm := congrArg Zsqrtd.norm hp
  rw [pi_norm] at hnorm
  norm_num at hnorm

/-- An element of Gaussian prime norm is irreducible.  Here the only fixed
arithmetic input is primality of `13`. -/
theorem pi_irreducible : Irreducible pi := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm pi).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [pi_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm :
        (Zsqrtd.norm pi).natAbs =
          (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
      simpa [Zsqrtd.norm_mul, Int.natAbs_mul] using
        congrArg (fun z : GI => (Zsqrtd.norm z).natAbs) hab
    rw [pi_norm] at hnorm
    have hp13 : Nat.Prime 13 := by
      decide
    rcases hp13.eq_one_or_self_of_dvd
        (Zsqrtd.norm a).natAbs
        ⟨(Zsqrtd.norm b).natAbs, hnorm⟩ with ha | ha
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      norm_num at hnorm
      rw [ha] at hnorm
      omega

theorem pi_prime : Prime pi :=
  irreducible_iff_prime.mp pi_irreducible

theorem g_degree : g.degree = 3 := by
  unfold g
  compute_degree!

theorem g_natDegree : g.natDegree = 3 := by
  unfold g
  compute_degree!

@[simp] theorem g_coeff_zero : g.coeff 0 = -1 := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

@[simp] theorem g_coeff_one : g.coeff 1 = -1 - 2 * i := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

@[simp] theorem g_coeff_two : g.coeff 2 = 2 - 2 * i := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

@[simp] theorem g_coeff_three : g.coeff 3 = 1 := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

theorem g_monic : g.Monic := by
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff,
    g_natDegree, g_coeff_three]

/-- Relative Gaussian discriminant of the cubic. -/
theorem g_discr : g.discr = pi ^ 2 := by
  rw [Polynomial.discr_of_degree_eq_three g_degree]
  rw [g_coeff_zero, g_coeff_one, g_coeff_two, g_coeff_three]
  ext <;> norm_num [pi, i, pow_two, pow_succ]

/-- Exact factored coefficient form of the translated cubic. -/
theorem h_explicit :
    h =
      X ^ 3 +
        C (pi ^ 2 * (1 + 2 * i)) * X ^ 2 +
        C (pi * (70 + 34 * i)) * X +
        C (pi * (231 + 94 * i)) := by
  have h2 :
      (27 : GI) + (2 - 2 * i) =
        pi ^ 2 * (1 + 2 * i) := by
    ext <;> norm_num [pi, i, pow_two]
  have h1 :
      (243 : GI) + 18 * (2 - 2 * i) + (-1 - 2 * i) =
        pi * (70 + 34 * i) := by
    ext <;> norm_num [pi, i]
  have h0 :
      (729 : GI) + 81 * (2 - 2 * i) +
          9 * (-1 - 2 * i) - 1 =
        pi * (231 + 94 * i) := by
    ext <;> norm_num [pi, i]
  calc
    h =
        (X + C 9) ^ 3 +
          C (2 - 2 * i) * (X + C 9) ^ 2 +
          C (-1 - 2 * i) * (X + C 9) - 1 := by
      simp [h, g]
    _ =
        X ^ 3 +
          C ((27 : GI) + (2 - 2 * i)) * X ^ 2 +
          C ((243 : GI) + 18 * (2 - 2 * i) +
            (-1 - 2 * i)) * X +
          C ((729 : GI) + 81 * (2 - 2 * i) +
            9 * (-1 - 2 * i) - 1) := by
      simp only [map_add, map_sub, map_mul, map_ofNat,
        map_neg, map_one]
      ring
    _ = _ := by rw [h2, h1, h0]

theorem h_monic : h.Monic :=
  g_monic.comp_X_add_C 9

theorem h_natDegree : h.natDegree = 3 := by
  simp [h, Polynomial.natDegree_comp, g_natDegree]

theorem h_degree : h.degree = 3 :=
  (degree_eq_iff_natDegree_eq h_monic.ne_zero).mpr h_natDegree

@[simp] theorem h_coeff_zero :
    h.coeff 0 = pi * (231 + 94 * i) := by
  rw [h_explicit]
  simp

@[simp] theorem h_coeff_one :
    h.coeff 1 = pi * (70 + 34 * i) := by
  rw [h_explicit]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  norm_num

@[simp] theorem h_coeff_two :
    h.coeff 2 = pi ^ 2 * (1 + 2 * i) := by
  rw [h_explicit]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  norm_num

@[simp] theorem h_coeff_three :
    h.coeff 3 = 1 := by
  simpa [h_natDegree] using h_monic.coeff_natDegree

/-- Translation preserves the computed discriminant; here this is verified
directly from the cubic formula. -/
theorem h_discr : h.discr = pi ^ 2 := by
  rw [Polynomial.discr_of_degree_eq_three h_degree]
  rw [h_coeff_zero, h_coeff_one, h_coeff_two, h_coeff_three]
  ext <;> norm_num [pi, i, pow_two, pow_succ]

theorem pi_not_dvd_constantQuotient :
    ¬ pi ∣ (231 + 94 * i) := by
  rintro ⟨d, hd⟩
  have hnorm := congrArg Zsqrtd.norm hd
  rw [Zsqrtd.norm_mul, pi_norm] at hnorm
  have hc : Zsqrtd.norm (231 + 94 * i : GI) = 62197 := by
    norm_num [i, Zsqrtd.norm]
  rw [hc] at hnorm
  omega

theorem pi_span_prime :
    (Ideal.span ({pi} : Set GI)).IsPrime :=
  (Ideal.span_singleton_prime pi_ne_zero).mpr pi_prime

/-- The translated cubic is Eisenstein at the unique displayed ramified
Gaussian prime. -/
theorem h_eisenstein :
    h.IsEisensteinAt (Ideal.span ({pi} : Set GI)) := by
  apply h_monic.isEisensteinAt_of_mem_of_notMem pi_span_prime.ne_top
  · intro n hn
    rw [h_natDegree] at hn
    interval_cases n
    · rw [h_coeff_zero, Ideal.mem_span_singleton]
      exact dvd_mul_right pi _
    · rw [h_coeff_one, Ideal.mem_span_singleton]
      exact dvd_mul_right pi _
    · rw [h_coeff_two, Ideal.mem_span_singleton]
      exact ⟨pi * (1 + 2 * i), by ring⟩
  · intro hmem
    rw [h_coeff_zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨d, hd⟩
    apply pi_not_dvd_constantQuotient
    refine ⟨d, ?_⟩
    apply mul_left_cancel₀ pi_ne_zero
    calc
      pi * (231 + 94 * i) = pi ^ 2 * d := hd
      _ = pi * (pi * d) := by ring

end

end MazurProof.N13GaussianGlobalArithmetic


