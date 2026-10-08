-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerIdealSquare_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerIdealSquare_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:14:26.413004+00:00
-- url     : https://prove2.me/theorems/cc1927c9-1833-47f3-b5f0-8985b465eed2
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticIrreducible_p0
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false




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

theorem span_pair_sq_eq_span_left_of_coprime
    (x y z : R)
    (hrel : x * z = -(y ^ 2))
    (hcoprime : Ideal.span ({x, z} : Set R) = ⊤) :
    Ideal.span ({x, y} : Set R) ^ 2 =
      Ideal.span ({x} : Set R) := by
  rw [pow_two, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro t ht
    have hxspan :
        x ∈ Ideal.span ({x} : Set R) :=
      Ideal.subset_span (Set.mem_singleton x)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_right x _ hxspan
    · exact Ideal.mul_mem_right y _ hxspan
    · exact Ideal.mul_mem_left _ y hxspan
    · have hy2 :
          y ^ 2 ∈ Ideal.span ({x} : Set R) := by
        rw [← neg_mem_iff, ← hrel]
        exact Ideal.mul_mem_right z _ hxspan
      rw [pow_two] at hy2
      exact hy2
  · rw [Ideal.span_le]
    intro t ht
    have ht' : t = x := Set.mem_singleton_iff.mp ht
    have hone :
        (1 : R) ∈ Ideal.span ({x, z} : Set R) := by
      rw [hcoprime]
      exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hone
    have hxx :
        x * x ∈
          Ideal.span ({x * x, x * y, y * x, y * y} : Set R) :=
      Ideal.subset_span (by simp)
    have hyy :
        y * y ∈
          Ideal.span ({x * x, x * y, y * x, y * y} : Set R) :=
      Ideal.subset_span (by simp)
    have hsum :
        a * (x * x) - b * (y * y) ∈
          Ideal.span ({x * x, x * y, y * x, y * y} : Set R) :=
      Ideal.sub_mem _
        (Ideal.mul_mem_left _ _ hxx)
        (Ideal.mul_mem_left _ _ hyy)
    have hproduct :
        (a * x + b * z) * x ∈
          Ideal.span ({x * x, x * y, y * x, y * y} : Set R) := by
      have heq :
          (a * x + b * z) * x =
            a * (x * x) - b * (y * y) := by
        calc
          (a * x + b * z) * x =
              a * (x * x) + b * (x * z) := by ring
          _ = a * (x * x) - b * (y * y) := by
            rw [hrel]
            simp only [pow_two]
            ring
      rw [heq]
      exact hsum
    have hxmem :
        x ∈ Ideal.span
          ({x * x, x * y, y * x, y * y} : Set R) := by
      simpa only [hab, one_mul] using hproduct
    change
      t ∈ Ideal.span
        ({x * x, x * y, y * x, y * y} : Set R)
    rw [ht']
    exact hxmem

theorem span_pair_eq_top_of_unit_jacobian
    (x y z dx dy dz jac : R)
    (hrel : x * z = -(y ^ 2))
    (hjac :
      jac = 2 * y * dy + dx * z + x * dz)
    (hunit : IsUnit jac) :
    Ideal.span ({x, z} : Set R) = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ :=
    Ideal.exists_le_maximal
      (Ideal.span ({x, z} : Set R)) hne
  have hx : x ∈ P :=
    hle (Ideal.subset_span (by simp))
  have hz : z ∈ P :=
    hle (Ideal.subset_span (by simp))
  have hy2 : y ^ 2 ∈ P := by
    rw [← neg_mem_iff, ← hrel]
    exact P.mul_mem_right z hx
  have hy : y ∈ P :=
    hPmax.isPrime.mem_of_pow_mem 2 hy2
  have hjacmem : jac ∈ P := by
    rw [hjac]
    exact P.add_mem
      (P.add_mem
        (by
          have := P.mul_mem_left (2 * dy) hy
          simpa only [mul_assoc, mul_comm, mul_left_comm] using this)
        (P.mul_mem_left dx hz))
      (P.mul_mem_right dz hx)
  exact (Ideal.notMem_of_isUnit P hunit) hjacmem

theorem mumfordBranchIdeal_sq
    {S : Type*} [CommRing S] [Algebra R S]
    (f u v w : R[X]) (θ : S)
    (hroot : aeval θ f = 0)
    (hcurve : f - v ^ 2 = u * w)
    (hunit : IsUnit (aeval θ f.derivative)) :
    Ideal.span ({aeval θ u, aeval θ v} : Set S) ^ 2 =
      Ideal.span ({aeval θ u} : Set S) := by
  have hrel :
      aeval θ u * aeval θ w = -(aeval θ v ^ 2) := by
    have h := congrArg (aeval θ) hcurve
    simpa only [map_sub, map_pow, map_mul, hroot, zero_sub] using h.symm
  have hderivPoly :
      f.derivative =
        C 2 * v * v.derivative +
          u.derivative * w + u * w.derivative := by
    have h := congrArg Polynomial.derivative hcurve
    simp only [derivative_sub, derivative_pow,
      derivative_mul] at h
    norm_num at h
    linear_combination h
  have hjac :
      aeval θ f.derivative =
        2 * aeval θ v * aeval θ v.derivative +
          aeval θ u.derivative * aeval θ w +
          aeval θ u * aeval θ w.derivative := by
    rw [hderivPoly]
    simp only [map_add, map_mul, map_ofNat]
  exact span_pair_sq_eq_span_left_of_coprime
    (aeval θ u) (aeval θ v) (aeval θ w) hrel
    (span_pair_eq_top_of_unit_jacobian
      (aeval θ u) (aeval θ v) (aeval θ w)
      (aeval θ u.derivative) (aeval θ v.derivative)
      (aeval θ w.derivative) (aeval θ f.derivative)
      hrel hjac hunit)

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

def goodTheta : GoodOrder :=
  algebraMap IntegralOrder GoodOrder integralTheta

theorem aeval_goodTheta
    (p : ℤ[X]) :
    aeval goodTheta p =
      algebraMap IntegralOrder GoodOrder
        (AdjoinRoot.mk N13SexticIrreducible.fInt p) := by
  rw [aeval_def]
  calc
    eval₂ (algebraMap ℤ GoodOrder) goodTheta p =
        algebraMap IntegralOrder GoodOrder
          (eval₂ (algebraMap ℤ IntegralOrder) integralTheta p) := by
      have h :=
        (Polynomial.hom_eval₂ p
          (algebraMap ℤ IntegralOrder)
          (algebraMap IntegralOrder GoodOrder)
          integralTheta).symm
      simpa only [goodTheta,
        IsScalarTower.algebraMap_eq ℤ IntegralOrder GoodOrder] using h
    _ =
        algebraMap IntegralOrder GoodOrder
          (AdjoinRoot.mk N13SexticIrreducible.fInt p) := by
      rw [← aeval_def, integralTheta, AdjoinRoot.aeval_eq]

theorem goodTheta_root :
    aeval goodTheta N13SexticIrreducible.fInt = 0 := by
  rw [aeval_goodTheta, AdjoinRoot.mk_self, map_zero]

theorem goodTheta_derivative_isUnit :
    IsUnit
      (aeval goodTheta
        N13SexticIrreducible.fInt.derivative) := by
  rw [aeval_goodTheta]
  exact
    IsLocalization.Away.algebraMap_isUnit
      differentGenerator

/-- Any integral Mumford relation on the N13 curve has square branch ideal
after the different is inverted. -/
theorem n13_goodBranchIdeal_sq
    (u v w : ℤ[X])
    (hcurve :
      N13SexticIrreducible.fInt - v ^ 2 = u * w) :
    Ideal.span
          ({aeval goodTheta u, aeval goodTheta v} :
            Set GoodOrder) ^ 2 =
      Ideal.span
        ({aeval goodTheta u} : Set GoodOrder) := by
  exact mumfordBranchIdeal_sq
    N13SexticIrreducible.fInt u v w goodTheta
    goodTheta_root hcurve goodTheta_derivative_isUnit

end

end MazurProof.N13MumfordKummerIdealSquare


