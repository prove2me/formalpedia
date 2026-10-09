-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:06:47.61085+00:00
-- url     : https://prove2.me/theorems/9fe37fa0-7e1d-4a1a-b8f1-f4cf655d9ad3
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphJacobian_p0
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false




/-!
# Two-chart closures of integral N13 infinity graphs

An integral polynomial graph on the ordinary infinity chart can be
homogenized with the weights

`u ↦ X² u(X⁻¹)`, `v ↦ X³ v(X⁻¹)`, `w ↦ X⁴ w(X⁻¹)`.

`Polynomial.reflect` implements these three weighted reversals.  Reflecting
the infinity semigraph identity at total weight six gives the affine
semigraph identity, while on the Laurent overlap the two graph generators
differ by the units `x²` and `x³`.  Thus every bounded integral infinity
graph supplies an invertible root-free two-chart line.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityGraphTwoChart

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev Base : Type :=
  N13IntegralInfinityChart.Base

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityGraphJacobian.InfinityFractionalIdeal

abbrev GraphData : Type :=
  N13IntegralInfinityGraphJacobian.GraphData

def affineU (D : GraphData) : R₂[X] :=
  D.u.reflect 2

def affineV (D : GraphData) : R₂[X] :=
  D.v.reflect 3

def affineW (D : GraphData) : R₂[X] :=
  D.w.reflect 4

private theorem hBase_natDegree_le :
    N13IntegralInfinityChart.hBase.natDegree ≤ 3 := by
  unfold N13IntegralInfinityChart.hBase
  compute_degree <;> norm_num

private theorem rhsBase_natDegree_le :
    N13IntegralInfinityChart.rhsBase.natDegree ≤ 6 := by
  unfold N13IntegralInfinityChart.rhsBase
  compute_degree <;> norm_num

private theorem reflect_X_pow
    (N n : ℕ)
    (h : n ≤ N) :
    ((X : R₂[X]) ^ n).reflect N = X ^ (N - n) := by
  simpa [revAt_le h] using
    (reflect_monomial N n (R := R₂))

private theorem reflect_hBase :
    N13IntegralInfinityChart.hBase.reflect 3 =
      N13GeneralizedMumfordIntegral.hPoly (R := R₂) := by
  simp [N13IntegralInfinityChart.hBase,
    N13GeneralizedMumfordIntegral.hPoly, reflect_add]

private theorem reflect_rhsBase :
    N13IntegralInfinityChart.rhsBase.reflect 6 =
      N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) := by
  have hX :
      (X : R₂[X]).reflect 6 = X ^ 5 := by
    simpa using reflect_X_pow 6 1 (by norm_num)
  have hX2 :
      ((X : R₂[X]) ^ 2).reflect 6 = X ^ 4 := by
    simpa using reflect_X_pow 6 2 (by norm_num)
  rw [N13IntegralInfinityChart.rhsBase,
    N13GeneralizedMumfordIntegral.rhsPoly,
    reflect_add, hX, hX2]

/-- Weighted reflection turns the infinity semigraph equation into the
affine semigraph equation. -/
theorem affine_curve_eq
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2)
    (hv : D.v.natDegree ≤ 3)
    (hw : D.w.natDegree ≤ 4) :
    affineV D ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV D -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
      affineU D * affineW D := by
  have hvv :
      (D.v ^ 2).reflect 6 =
        D.v.reflect 3 * D.v.reflect 3 := by
    simpa [pow_two] using
      (reflect_mul D.v D.v hv hv)
  have hhv :
      (N13IntegralInfinityChart.hBase * D.v).reflect 6 =
        N13IntegralInfinityChart.hBase.reflect 3 *
          D.v.reflect 3 := by
    simpa using
      (reflect_mul
        N13IntegralInfinityChart.hBase D.v
        hBase_natDegree_le hv)
  have huw :
      (D.u * D.w).reflect 6 =
        D.u.reflect 2 * D.w.reflect 4 := by
    simpa using
      (reflect_mul D.u D.w hu hw)
  calc
    affineV D ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV D -
          N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
        (D.v ^ 2).reflect 6 +
          (N13IntegralInfinityChart.hBase * D.v).reflect 6 -
          N13IntegralInfinityChart.rhsBase.reflect 6 := by
            rw [hvv, hhv, reflect_hBase, reflect_rhsBase]
            simp [affineV, pow_two]
    _ =
        (D.v ^ 2 +
            N13IntegralInfinityChart.hBase * D.v -
            N13IntegralInfinityChart.rhsBase).reflect 6 := by
          rw [reflect_sub, reflect_add]
    _ = (D.u * D.w).reflect 6 := by rw [D.curve_eq]
    _ = affineU D * affineW D := by
          rw [huw]
          rfl

def affineGraphData
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2)
    (hv : D.v.natDegree ≤ 3)
    (hw : D.w.natDegree ≤ 4) :
    N13IntegralGraphJacobian.GraphData where
  u := affineU D
  v := affineV D
  w := affineW D
  curve_eq := affine_curve_eq D hu hv hw

theorem affineU_ne_zero
    (D : GraphData)
    (hu : D.u ≠ 0) :
    affineU D ≠ 0 := by
  intro hzero
  apply hu
  exact Polynomial.reflect_eq_zero_iff.mp hzero

def infinityIdeal (D : GraphData) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    N13IntegralInfinityGraphJacobian.xClassHom
    N13IntegralInfinityGraphJacobian.yClass
    D.u D.v

def affineIdeal
    (D : GraphData) :
    Ideal N13IntegralGraphJacobian.IntegralRing :=
  GeneralizedGraphIdealCore.graphIdeal
    N13GeneralizedMumfordIntegral.xClassHom
    N13GeneralizedMumfordIntegral.yClass
    (affineU D) (affineV D)

abbrev GenericModel : SexticMumford.Model
    N13TwoAdicCoordinateBaseChange.Q₂ :=
  N13GoodSexticCoordinateEquiv.M
    (K := N13TwoAdicCoordinateBaseChange.Q₂)

/-- The generic fibre of the affine half of an infinity graph is its
coefficient-extended, completed-square sextic graph. -/
theorem map_affineIdeal
    (D : GraphData) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (affineIdeal D) =
      SexticMumford.mumfordIdeal GenericModel
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineU D))
        (N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly (affineV D))) := by
  rw [N13TwoAdicCoordinateBaseChange.integralToSextic,
    ← Ideal.map_map]
  change
    Ideal.map N13GoodSexticCoordinateEquiv.toSextic
        (Ideal.map N13TwoAdicCoordinateBaseChange.extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (affineU D) (affineV D))) = _
  rw [N13TwoAdicCoordinateBaseChange.map_mumfordIdeal,
    N13GoodSexticMumfordTransport.map_mumfordIdeal]

/-- If weighted reflection recovers a nonzero scalar multiple of a Mumford
horizontal equation and the reflected ordinate recovers its graph modulo
that equation, then the affine half has exactly the prescribed generic
graph ideal. -/
theorem map_affineIdeal_eq_mumfordIdeal
    (E : GraphData)
    (D : SexticMumford.SemiMumford GenericModel)
    (c : N13TwoAdicCoordinateBaseChange.Q₂)
    (hc : c ≠ 0)
    (hu :
      N13TwoAdicCoordinateBaseChange.mapPoly (affineU E) =
        C c * D.u)
    (hv :
      D.u ∣
        N13GoodSexticMumfordTransport.completedGraph
            (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E)) -
          D.v) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (affineIdeal E) =
      SexticMumford.mumfordIdeal GenericModel D.u D.v := by
  rw [map_affineIdeal, hu]
  have hunit :
      IsUnit
        (SexticMumford.xClass GenericModel (C c)) := by
    change
      IsUnit
        (algebraMap N13TwoAdicCoordinateBaseChange.Q₂
          (SexticMumford.CoordinateRing GenericModel) c)
    exact
      (isUnit_iff_ne_zero.mpr hc).map
        (algebraMap N13TwoAdicCoordinateBaseChange.Q₂
          (SexticMumford.CoordinateRing GenericModel))
  change
    GeneralizedGraphIdealCore.graphIdeal
        (SexticMumford.xClassHom GenericModel)
        (SexticMumford.yClass GenericModel)
        (C c * D.u)
        (N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E))) =
      GeneralizedGraphIdealCore.graphIdeal
        (SexticMumford.xClassHom GenericModel)
        (SexticMumford.yClass GenericModel) D.u D.v
  rw [GeneralizedGraphIdealCore.graphIdeal_mul_left_eq_of_isUnit
      (SexticMumford.xClassHom GenericModel)
      (SexticMumford.yClass GenericModel)
      (C c) D.u
      (N13GoodSexticMumfordTransport.completedGraph
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E)))
      hunit,
    GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
      (SexticMumford.xClassHom GenericModel)
      (SexticMumford.yClass GenericModel)
      D.u D.v
      (N13GoodSexticMumfordTransport.completedGraph
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E)))
      hv]

theorem infinityIdeal_isUnit
    (D : GraphData)
    (hu : D.u ≠ 0) :
    IsUnit (infinityIdeal D : InfinityFractionalIdeal) := by
  exact
    N13IntegralInfinityGraphJacobian.graphIdeal_isUnit D hu

theorem affineIdeal_isUnit
    (D : GraphData)
    (hdu : D.u.natDegree ≤ 2)
    (hdv : D.v.natDegree ≤ 3)
    (hdw : D.w.natDegree ≤ 4)
    (hu : D.u ≠ 0) :
    IsUnit
      (affineIdeal D :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  exact
    N13IntegralGraphJacobian.graphIdeal_isUnit
      (affineGraphData D hdu hdv hdw)
      (affineU_ne_zero D hu)

private theorem tOverlap_isUnit :
    IsUnit N13OrdinaryCurveOverlap.tOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨N13OrdinaryCurveOverlap.xOverlap,
      N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap⟩

/-- The infinity horizontal coordinate map evaluates polynomials at the
Laurent-overlap coordinate `t`. -/
theorem xClassHom_on_overlap
    (p : Base) :
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap)
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      p.eval₂
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
        N13OrdinaryCurveOverlap.tOverlap := by
  let f : Base →+* N13OrdinaryCurveOverlap.InfinityOverlap :=
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap).comp
        N13IntegralInfinityGraphJacobian.xClassHom
  let g : Base →+* N13OrdinaryCurveOverlap.InfinityOverlap :=
    Polynomial.eval₂RingHom
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.tOverlap
  have hfg : f = g := by
    ext r <;>
      simp [f, g,
        N13IntegralInfinityGraphJacobian.xClassHom,
        N13IntegralInfinityPointSpread.xClassHom,
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap,
        N13OrdinaryCurveOverlap.tOverlap,
        N13IntegralInfinityChart.tClass]
  exact congrArg (fun φ : Base →+* _ => φ p) hfg

/-- Evaluating a bounded weighted reflection on the affine overlap equals
the original polynomial evaluated at `t=x⁻¹`, multiplied by `xⁿ`. -/
theorem reflect_on_overlap
    (n : ℕ)
    (p : Base)
    (hp : p.natDegree ≤ n) :
    N13OrdinaryCurveOverlap.affineCoeffMap (p.reflect n) =
      N13OrdinaryCurveOverlap.xOverlap ^ n *
        p.eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.tOverlap := by
  letI : Invertible N13OrdinaryCurveOverlap.tOverlap :=
    tOverlap_isUnit.invertible
  have hinv :
      ⅟N13OrdinaryCurveOverlap.tOverlap =
        N13OrdinaryCurveOverlap.xOverlap := by
    exact
      invOf_eq_right_inv
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hreflect :=
    Polynomial.eval₂_reflect_mul_pow
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.tOverlap n p hp
  rw [hinv] at hreflect
  change
    (p.reflect n).eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.xOverlap =
      N13OrdinaryCurveOverlap.xOverlap ^ n *
        p.eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.tOverlap
  calc
    (p.reflect n).eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.xOverlap =
        1 *
          ((p.reflect n).eval₂
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            N13OrdinaryCurveOverlap.xOverlap) := by simp
    _ =
        (N13OrdinaryCurveOverlap.xOverlap ^ n *
            N13OrdinaryCurveOverlap.tOverlap ^ n) *
          ((p.reflect n).eval₂
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            N13OrdinaryCurveOverlap.xOverlap) := by
          rw [← mul_pow,
            mul_comm N13OrdinaryCurveOverlap.xOverlap
              N13OrdinaryCurveOverlap.tOverlap,
            N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap,
            one_pow, one_mul]
    _ =
        N13OrdinaryCurveOverlap.xOverlap ^ n *
          (((p.reflect n).eval₂
              N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              N13OrdinaryCurveOverlap.xOverlap) *
            N13OrdinaryCurveOverlap.tOverlap ^ n) := by ring
    _ =
        N13OrdinaryCurveOverlap.xOverlap ^ n *
          p.eval₂
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            N13OrdinaryCurveOverlap.tOverlap := by rw [hreflect]

theorem affineU_on_overlap
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (affineU D)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
            (N13IntegralInfinityGraphJacobian.xClassHom D.u) := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    show affineU D = D.u.reflect 2 by rfl,
    reflect_on_overlap 2 D.u hu, xClassHom_on_overlap]

theorem affineV_on_overlap
    (D : GraphData)
    (hv : D.v.natDegree ≤ 3) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (GeneralizedGraphIdealCore.ySubClass
          N13GeneralizedMumfordIntegral.xClassHom
          N13GeneralizedMumfordIntegral.yClass
          (affineV D)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
            (GeneralizedGraphIdealCore.ySubClass
              N13IntegralInfinityGraphJacobian.xClassHom
              N13IntegralInfinityGraphJacobian.yClass
              D.v) := by
  simp only [GeneralizedGraphIdealCore.ySubClass, map_sub,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  rw [show affineV D = D.v.reflect 3 by rfl,
    reflect_on_overlap 3 D.v hv, xClassHom_on_overlap]
  simp only [N13IntegralInfinityGraphJacobian.yClass,
    N13IntegralInfinityPointSpread.yClass,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.vOverlap]
  ring

private theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        (u : A) (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.mul_mem_left _
        (v : A) (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have h :
          (u : A) * a ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((u⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm
    · rw [hz]
      have h :
          (v : A) * b ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((v⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm

/-- The affine weighted closure and the integral infinity graph define the
same ideal on the Laurent overlap. -/
theorem ideals_agree_on_overlap
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2)
    (hv : D.v.natDegree ≤ 3) :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineIdeal D) =
      Ideal.map
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
        (infinityIdeal D) := by
  simp only [affineIdeal, infinityIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    Ideal.map_span, Set.image_pair]
  rw [affineU_on_overlap D hu, affineV_on_overlap D hv]
  let ux :
      N13OrdinaryCurveOverlap.InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hux2 :
      ((ux ^ 2 :
          N13OrdinaryCurveOverlap.InfinityOverlapˣ) :
        N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap ^ 2 := by
    change
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) ^ 2 =
        N13OrdinaryCurveOverlap.xOverlap ^ 2
    rw [hux]
  have hux3 :
      ((ux ^ 3 :
          N13OrdinaryCurveOverlap.InfinityOverlapˣ) :
        N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap ^ 3 := by
    change
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) ^ 3 =
        N13OrdinaryCurveOverlap.xOverlap ^ 3
    rw [hux]
  have hs :=
    span_pair_unit_mul
      (ux ^ 2) (ux ^ 3)
      ((algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap)
          (N13IntegralInfinityGraphJacobian.xClassHom D.u))
      ((algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap)
          (GeneralizedGraphIdealCore.ySubClass
            N13IntegralInfinityGraphJacobian.xClassHom
            N13IntegralInfinityGraphJacobian.yClass D.v))
  rw [hux2, hux3] at hs
  exact hs

/-- A bounded nonzero integral infinity graph gives a root-free invertible
line on the two ordinary integral charts. -/
def twoChartLine
    (D : GraphData)
    (hdu : D.u.natDegree ≤ 2)
    (hdv : D.v.natDegree ≤ 3)
    (hdw : D.w.natDegree ≤ 4)
    (hu : D.u ≠ 0) :
    N13IntegralInfinityPointSpread.TwoChartLine where
  affineIdeal := affineIdeal D
  infinityIdeal := infinityIdeal D
  affine_isUnit := affineIdeal_isUnit D hdu hdv hdw hu
  infinity_isUnit := infinityIdeal_isUnit D hu
  overlap_eq := ideals_agree_on_overlap D hdu hdv

end

end MazurProof.N13IntegralInfinityGraphTwoChart


