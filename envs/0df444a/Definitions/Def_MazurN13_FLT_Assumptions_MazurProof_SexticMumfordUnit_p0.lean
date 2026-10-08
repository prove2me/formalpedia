-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordUnit_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordUnit_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:55:25.328241+00:00
-- url     : https://prove2.me/theorems/845eb88e-c759-4353-9ba0-a9a4e061d7a0
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordUnit source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordUnit

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordUnit
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdeal_p0
import Mathlib.RingTheory.FractionalIdeal.Inverse

set_option autoImplicit false




/-!
# Explicit invertibility of Mumford ideals on a smooth sextic

For a semi-Mumford pair `(u,v)`, squarefreeness of the sextic gives
`(u, 2v, (f-v²)/u) = 1`.  Consequently `(u,Y-v) (u,Y+v) = (u)`,
which packages the Mumford ideal as a unit fractional ideal.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

theorem mumford_bezout (D : SemiMumford M) :
    ∃ w a b c : K[X],
      M.f - D.v ^ 2 = D.u * w ∧
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  classical
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcop : IsCoprime D.u (EuclideanDomain.gcd (2 * D.v) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact D.u_monic.ne_zero hzero.1
    · intro z hz hzu hzg
      have hz2v : z ∣ 2 * D.v :=
        hzg.trans (EuclideanDomain.gcd_dvd_left (2 * D.v) w)
      have hzw : z ∣ w :=
        hzg.trans (EuclideanDomain.gcd_dvd_right (2 * D.v) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq : C (2 : K) = (2 : K[X]) := by
          exact map_natCast (C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr M.two_ne_zero)
      have hzv : z ∣ D.v := by
        rcases hz.prime.dvd_mul.mp hz2v with hz2 | hzv
        · exact (hz.not_isUnit (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzv
      have hzzSub : z * z ∣ M.f - D.v ^ 2 := by
        rw [hw]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ D.v ^ 2 := by
        simpa only [pow_two] using mul_dvd_mul hzv hzv
      have hzzF : z * z ∣ M.f := by
        simpa only [sub_add_cancel] using dvd_add hzzSub hzzSq
      exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        M.ne_zero).mp M.squarefree z hz) hzzF
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨w, a,
    b * EuclideanDomain.gcdA (2 * D.v) w,
    b * EuclideanDomain.gcdB (2 * D.v) w, hw, ?_⟩
  rw [← hab, EuclideanDomain.gcd_eq_gcd_ab]
  ring

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass M v ∈ mumfordIdeal M u v := by
  exact Ideal.subset_span (by simp)

theorem mumfordIdeal_mul_conj_integral (D : SemiMumford M) :
    mumfordIdeal M D.u D.v * mumfordIdeal M D.u (-D.v) =
      Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M D.u D.v
  let J := mumfordIdeal M D.u (-D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨p₀ * q₀ * xClass M D.u +
        p₀ * qY * ySubClass M (-D.v) +
        pY * q₀ * ySubClass M D.v +
        pY * qY * xClass M w, ?_⟩
    rw [← hpEq, ← hqEq]
    simp only [ySubClass, xClass_neg, sub_neg_eq_add] at hpEq hqEq ⊢
    have hgraph :
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
          xClass M D.u * xClass M w := by
      calc
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
            yClass M ^ 2 - xClass M D.v ^ 2 := by ring
        _ = xClass M M.f - xClass M (D.v ^ 2) := by
          rw [yClass_sq, xClass_pow]
        _ = xClass M (M.f - D.v ^ 2) := by rw [xClass_sub]
        _ = xClass M (D.u * w) := by rw [hw]
        _ = xClass M D.u * xClass M w := by rw [xClass_mul]
    linear_combination pY * qY * hgraph
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨w, a, b, c, hw, hbez⟩ := mumford_bezout M D
    have huI : xClass M D.u ∈ I :=
      xClass_mem_mumfordIdeal M D.u D.v
    have huJ : xClass M D.u ∈ J :=
      xClass_mem_mumfordIdeal M D.u (-D.v)
    have hvI : ySubClass M D.v ∈ I :=
      ySubClass_mem_mumfordIdeal M D.u D.v
    have hvJ : ySubClass M (-D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal M D.u (-D.v)
    have hu2 : xClass M D.u * xClass M D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass M D.u * xClass M (2 * D.v) ∈ I * J := by
      have hp : xClass M D.u * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm : ySubClass M D.v * xClass M D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add, xClass_mul]
      change xClass M D.u * (2 * xClass M D.v) =
        xClass M D.u * (yClass M + xClass M D.v) -
          (yClass M - xClass M D.v) * xClass M D.u
      ring
    have huw : xClass M D.u * xClass M w ∈ I * J := by
      have hg : ySubClass M D.v * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      convert hg using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add]
      calc
        xClass M D.u * xClass M w = xClass M (D.u * w) := by
          rw [xClass_mul]
        _ = xClass M (M.f - D.v ^ 2) := by rw [hw]
        _ = xClass M M.f - xClass M (D.v ^ 2) := by rw [xClass_sub]
        _ = yClass M ^ 2 - xClass M D.v ^ 2 := by
          rw [yClass_sq, xClass_pow]
        _ = (yClass M - xClass M D.v) *
            (yClass M + xClass M D.v) := by ring
    have ha : xClass M a * (xClass M D.u * xClass M D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M a) hu2
    have hb : xClass M b *
        (xClass M D.u * xClass M (2 * D.v)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M b) huv
    have hc : xClass M c * (xClass M D.u * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M c) huw
    have hsum := Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M D.u * xClass M D.u) +
            xClass M b * (xClass M D.u * xClass M (2 * D.v)) +
            xClass M c * (xClass M D.u * xClass M w) =
          xClass M D.u := by
      calc
        _ = xClass M D.u *
            xClass M (a * D.u + b * (2 * D.v) + c * w) := by
              simp only [xClass_add, xClass_mul]
              ring
        _ = xClass M D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass M D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

def mumfordIdealUnit (D : SemiMumford M) : InvFrac M :=
  Units.mkOfMulEqOne
    (mumfordIdeal M D.u D.v :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
    ((mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        (FunctionField M) (xClass_ne_zero M D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford M) :
    (mumfordIdealUnit M D :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      mumfordIdeal M D.u D.v := rfl

end

end MazurProof.SexticMumford


