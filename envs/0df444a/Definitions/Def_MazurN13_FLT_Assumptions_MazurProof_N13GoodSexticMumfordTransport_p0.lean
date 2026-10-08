-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodSexticMumfordTransport_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodSexticMumfordTransport_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:59:49.055219+00:00
-- url     : https://prove2.me/theorems/dcec02fc-cdbc-483d-9c6c-48d020721b3c
-- title:
--   FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodSexticCoordinateEquiv_p0

set_option autoImplicit false




/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit in the base field, so it does not change the generated
ideal.
-/

open Polynomial

namespace MazurProof.N13GoodSexticMumfordTransport

noncomputable section

open N13GoodSexticCoordinateEquiv

/-- Multiplying one generator of a two-generated ideal by a unit does not
change the ideal. -/
theorem span_pair_mul_right_unit
    {R : Type*} [CommRing R] (x a y : R) (ha : IsUnit a) :
    Ideal.span {x, a * y} = Ideal.span {x, y} := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      exact Ideal.mul_mem_left _ a (Ideal.subset_span (by simp))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hay : a * y ∈ Ideal.span {x, a * y} :=
        Ideal.subset_span (by simp)
      have hby : b * (a * y) ∈ Ideal.span {x, a * y} :=
        Ideal.mul_mem_left _ b hay
      simpa [← mul_assoc, hba] using hby

universe u

variable {K : Type u} [Field K] [CharZero K]

local notation "ModelK" =>
  N13GoodSexticCoordinateEquiv.M (K := K)

local notation "SexticRingK" =>
  N13GoodSexticCoordinateEquiv.SexticRing (K := K)

local notation "toSexticK" =>
  N13GoodSexticCoordinateEquiv.toSextic (K := K)

local notation "sexticXHomK" =>
  N13GoodSexticCoordinateEquiv.sexticXHom (K := K)

/-- The sextic graph polynomial corresponding to a generalized graph
polynomial `v`. -/
def completedGraph (v : K[X]) : K[X] :=
  2 * v + N13GeneralizedMumfordIntegral.hPoly

private theorem two_mul_invTwo :
    (2 : SexticRingK) *
        (algebraMap K SexticRingK) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat (algebraMap K SexticRingK) 2, ← map_mul]
  norm_num

/-- Under completion of the square, the generalized graph generator is
`1 / 2` times the corresponding sextic graph generator. -/
@[simp] theorem toSextic_ySubClass (v : K[X]) :
    toSexticK
        (N13GeneralizedMumfordIntegral.ySubClass v) =
      (algebraMap K SexticRingK) (2 : K)⁻¹ *
        SexticMumford.ySubClass ModelK (completedGraph v) := by
  simp only [N13GeneralizedMumfordIntegral.ySubClass, map_sub,
    N13GoodSexticCoordinateEquiv.toSextic_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    N13GoodSexticCoordinateEquiv.goodYInSextic,
    SexticMumford.ySubClass, completedGraph, Algebra.smul_def]
  have hhalf :
      (algebraMap K SexticRingK) (1 / 2 : K) =
        (algebraMap K SexticRingK) (2 : K)⁻¹ := by
    norm_num
  have hx :
      SexticMumford.xClass ModelK
          (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
        2 * SexticMumford.xClass ModelK v +
          SexticMumford.xClass ModelK
            N13GeneralizedMumfordIntegral.hPoly := by
    change sexticXHomK
        (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
      2 * sexticXHomK v +
        sexticXHomK N13GeneralizedMumfordIntegral.hPoly
    rw [map_add, map_mul, map_ofNat]
  rw [hhalf, hx]
  let a : SexticRingK :=
    (algebraMap K SexticRingK) (2 : K)⁻¹
  let Y : SexticRingK := SexticMumford.yClass ModelK
  let H : SexticRingK :=
    SexticMumford.xClass ModelK
      N13GeneralizedMumfordIntegral.hPoly
  let V : SexticRingK :=
    SexticMumford.xClass ModelK v
  change a * (Y - H) - V = a * (Y - (2 * V + H))
  have ha : 2 * a = 1 := two_mul_invTwo
  linear_combination V * ha

private theorem invTwo_isUnit :
    IsUnit ((algebraMap K SexticRingK) (2 : K)⁻¹) := by
  exact
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K)⁻¹ ≠ 0)).map
      (algebraMap K SexticRingK)

/-- Completion of the square maps each generalized Mumford graph ideal
exactly onto the corresponding sextic Mumford graph ideal. -/
theorem map_mumfordIdeal (u v : K[X]) :
    Ideal.map toSexticK
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal ModelK u (completedGraph v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    SexticMumford.mumfordIdeal, Ideal.map_span, Set.image_pair,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    toSextic_ySubClass]
  exact span_pair_mul_right_unit _ _ _ invTwo_isUnit

/-- Congruent graph polynomials define the same sextic graph ideal. -/
theorem sextic_mumfordIdeal_eq_of_dvd_sub
    (u v w : K[X]) (hvw : u ∣ v - w) :
    SexticMumford.mumfordIdeal ModelK u v =
      SexticMumford.mumfordIdeal ModelK u w := by
  obtain ⟨q, hq⟩ := hvw
  have hxsub :
      SexticMumford.xClass ModelK (v - w) =
        SexticMumford.xClass ModelK v -
          SexticMumford.xClass ModelK w := by
    change sexticXHomK (v - w) =
      sexticXHomK v - sexticXHomK w
    exact map_sub sexticXHomK v w
  have hxmul :
      SexticMumford.xClass ModelK (u * q) =
        SexticMumford.xClass ModelK u *
          SexticMumford.xClass ModelK q := by
    change sexticXHomK (u * q) =
      sexticXHomK u * sexticXHomK q
    exact map_mul sexticXHomK u q
  have hyw :
      SexticMumford.ySubClass ModelK w =
        SexticMumford.ySubClass ModelK v +
          SexticMumford.xClass ModelK u *
            SexticMumford.xClass ModelK q := by
    unfold SexticMumford.ySubClass
    rw [← hxmul, ← hq, hxsub]
    ring
  have hyv :
      SexticMumford.ySubClass ModelK v =
        SexticMumford.ySubClass ModelK w -
          SexticMumford.xClass ModelK u *
            SexticMumford.xClass ModelK q := by
    rw [hyw]
    ring
  have hxv :
      SexticMumford.xClass ModelK u ∈
        SexticMumford.mumfordIdeal ModelK u v :=
    SexticMumford.xClass_mem_mumfordIdeal ModelK u v
  have hxw :
      SexticMumford.xClass ModelK u ∈
        SexticMumford.mumfordIdeal ModelK u w :=
    SexticMumford.xClass_mem_mumfordIdeal ModelK u w
  have hyvmem :
      SexticMumford.ySubClass ModelK v ∈
        SexticMumford.mumfordIdeal ModelK u v := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hywmem :
      SexticMumford.ySubClass ModelK w ∈
        SexticMumford.mumfordIdeal ModelK u w := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hmulv :
      SexticMumford.xClass ModelK u *
          SexticMumford.xClass ModelK q ∈
        SexticMumford.mumfordIdeal ModelK u v := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal ModelK u v)
        (SexticMumford.xClass ModelK q) hxv
  have hmulw :
      SexticMumford.xClass ModelK u *
          SexticMumford.xClass ModelK q ∈
        SexticMumford.mumfordIdeal ModelK u w := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal ModelK u w)
        (SexticMumford.xClass ModelK q) hxw
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxw
    · rw [hz, hyv]
      exact Ideal.sub_mem
        (SexticMumford.mumfordIdeal ModelK u w)
        hywmem
        hmulw
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxv
    · rw [hz, hyw]
      exact Ideal.add_mem
        (SexticMumford.mumfordIdeal ModelK u v)
        hyvmem
        hmulv

/-- The reduced sextic graph polynomial attached to generalized data. -/
def reducedCompletedGraph (u v : K[X]) : K[X] :=
  completedGraph v % u

private theorem dvd_sub_mod (p u : K[X]) :
    u ∣ p - p % u := by
  refine ⟨p / u, ?_⟩
  have h := EuclideanDomain.mod_add_div p u
  calc
    p - p % u = (p % u + u * (p / u)) - p % u := by
      rw [h]
    _ = u * (p / u) := by ring

/-- The exact transport theorem with the sextic graph polynomial reduced
modulo `u`, as required by the standard Mumford representation. -/
theorem map_mumfordIdeal_reduced (u v : K[X]) :
    Ideal.map toSexticK
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal ModelK u
        (reducedCompletedGraph u v) := by
  rw [map_mumfordIdeal]
  exact sextic_mumfordIdeal_eq_of_dvd_sub _ _ _
    (dvd_sub_mod (completedGraph v) u)

/-- Completing the square carries the generalized Mumford equation to the
standard sextic equation. -/
theorem completedGraph_curve_eq
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    N13Mumford.f K - completedGraph D.v ^ 2 =
      D.u * (-4 * D.w) := by
  rw [N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs
    (K := K)]
  unfold completedGraph
  linear_combination -4 * D.curve_eq

/-- Reducing the completed graph polynomial modulo `u` preserves the
sextic divisibility relation. -/
theorem reducedCompletedGraph_curve_dvd
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    D.u ∣ N13Mumford.f K -
      reducedCompletedGraph D.u D.v ^ 2 := by
  let V : K[X] := completedGraph D.v
  let Vred : K[X] := reducedCompletedGraph D.u D.v
  obtain ⟨q, hq⟩ := dvd_sub_mod V D.u
  change V - Vred = D.u * q at hq
  refine ⟨-4 * D.w + q * (V + Vred), ?_⟩
  calc
    N13Mumford.f K - Vred ^ 2 =
        (N13Mumford.f K - V ^ 2) +
          (V - Vred) * (V + Vred) := by ring
    _ =
        D.u * (-4 * D.w) +
          (D.u * q) * (V + Vred) := by
      rw [completedGraph_curve_eq D, hq]
    _ = D.u * (-4 * D.w + q * (V + Vred)) := by ring

/-- A generalized Mumford representative over a characteristic-zero field,
written as a standard reduced sextic semirepresentative. -/
def toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    SexticMumford.SemiMumford ModelK where
  u := D.u
  v := reducedCompletedGraph D.u D.v
  nInf := nInf
  u_monic := D.u_monic
  v_reduced := by
    apply (Polynomial.mod_eq_self_iff D.u_monic.ne_zero).2
    exact Polynomial.degree_mod_lt _ D.u_monic.ne_zero
  curve_dvd := by
    simpa only [N13Mumford.model_f] using
      reducedCompletedGraph_curve_dvd D

@[simp] theorem toSexticSemi_u
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).u = D.u := rfl

@[simp] theorem toSexticSemi_v
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).v =
      reducedCompletedGraph D.u D.v := rfl

@[simp] theorem toSexticSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).nInf = nInf := rfl

/-- The reduced standard semirepresentative has exactly the transported
generalized graph ideal. -/
theorem map_mumfordIdeal_toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    Ideal.map toSexticK
        (N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) =
      SexticMumford.mumfordIdeal ModelK
        (toSexticSemi D nInf).u
        (toSexticSemi D nInf).v := by
  simpa only [toSexticSemi_u, toSexticSemi_v] using
    map_mumfordIdeal_reduced D.u D.v

end

end MazurProof.N13GoodSexticMumfordTransport


