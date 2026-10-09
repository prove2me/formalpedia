-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphTwoChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphTwoChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:30:53.644985+00:00
-- url     : https://prove2.me/theorems/40e29c8d-43a4-44cc-a7dc-feb8fa38cfdb
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphTwoChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphTwoChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphTwoChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSaturation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalizationIdealPatch_p0

set_option autoImplicit false




/-!
# Two-chart closure of a vertical N13 infinity graph

A recovered vertical graph has infinity ideal

`(m(v), t - (a + c v))`.

After the substitutions `t=x⁻¹` and `v=x⁻³y`, clearing weights gives the
affine generators `x⁶m(x⁻³y)` and
`x³(t-a-cv) = x²-a x³-cy`.  The direct reciprocal kernel also contains a
monic quadratic equation in `t`; its weighted reflection has constant
coefficient one.  Adding this third, redundant overlap generator keeps the
affine support inside `D(x)`.

The infinity ideal is invertible on `D(x)`.  The principal-localization
patching theorem then proves that the three-generated affine closure is
invertible globally.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve

abbrev InfinityCurve : Type :=
  N13OrdinaryCurveOverlap.InfinityCurve

abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap

abbrev AffineFunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField

abbrev VerticalGraph : Type :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph

/-- Weighted reflection of the redundant monic reciprocal equation. -/
def affineReciprocal (u : R₂[X]) : AffineCurve :=
  N13GeneralizedMumfordIntegral.xClassHom (u.reflect 2)

/-- The weight-six affine transform of the vertical equation `m(v)`. -/
def affineVerticalEquation (E : VerticalGraph) : AffineCurve :=
  N13GeneralizedMumfordIntegral.yClass ^ 2 +
    N13GeneralizedMumfordIntegral.xClassHom
        (C (E.m.coeff 1) * X ^ 3) *
      N13GeneralizedMumfordIntegral.yClass +
    N13GeneralizedMumfordIntegral.xClassHom
      (C (E.m.coeff 0) * X ^ 6)

/-- The weight-three affine transform of `t-(a+cv)`. -/
def affineLinearEquation (E : VerticalGraph) : AffineCurve :=
  N13OrdinaryCurveOverlap.xClass ^ 2 -
    algebraMap R₂ AffineCurve E.a *
      N13OrdinaryCurveOverlap.xClass ^ 3 -
    algebraMap R₂ AffineCurve E.c *
      N13GeneralizedMumfordIntegral.yClass

/-- Three-generated affine closure of a vertical graph, including the
redundant reciprocal equation that removes support at `x=0`. -/
def affineIdeal (u : R₂[X]) (E : VerticalGraph) :
    Ideal AffineCurve :=
  Ideal.span
    ({affineReciprocal u,
      affineVerticalEquation E,
      affineLinearEquation E} : Set AffineCurve)

/-- Weighted reflection of the reciprocal generator on the overlap. -/
theorem affineReciprocal_on_overlap
    (u : R₂[X])
    (huDegree : u.natDegree ≤ 2) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineReciprocal u) =
      N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass u) := by
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (u.reflect 2)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityGraphJacobian.xClassHom u)
  rw [
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13IntegralInfinityGraphTwoChart.reflect_on_overlap
      2 u huDegree,
    N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap]

/-- The vertical quadratic generator changes by the unit `x⁶` on the
ordinary overlap. -/
theorem affineVerticalEquation_on_overlap
    (E : VerticalGraph)
    (hmDegree : E.m.natDegree = 2) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineVerticalEquation E) =
      N13OrdinaryCurveOverlap.xOverlap ^ 6 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.U E) := by
  have hmShape :=
    N13IntegralInfinityGraphSaturation.monic_quadratic_eq
      E.m E.m_monic hmDegree
  have hU :
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.U E) =
        N13OrdinaryCurveOverlap.vOverlap ^ 2 +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              (E.m.coeff 1) *
            N13OrdinaryCurveOverlap.vOverlap +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            (E.m.coeff 0) := by
    rw [N13IntegralInfinityVerticalGraphJacobian.U, hmShape]
    simp [N13IntegralInfinityGraphJacobian.yClass,
      N13IntegralInfinityPointSpread.yClass,
      N13OrdinaryCurveOverlap.vOverlap,
      N13IntegralInfinityGraphSaturation.coefficientToInfinityOverlap_eq_algebraMap_R₂]
  rw [affineVerticalEquation]
  simp only [map_add, map_mul, map_pow,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap_C,
    N13OrdinaryCurveOverlap.affineCoeffMap_X]
  rw [hU]
  change
    (N13OrdinaryCurveOverlap.xOverlap ^ 3 *
          N13OrdinaryCurveOverlap.vOverlap) ^ 2 +
        (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              (E.m.coeff 1) *
            N13OrdinaryCurveOverlap.xOverlap ^ 3) *
          (N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap) +
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            (E.m.coeff 0) *
          N13OrdinaryCurveOverlap.xOverlap ^ 6 =
      N13OrdinaryCurveOverlap.xOverlap ^ 6 *
        (N13OrdinaryCurveOverlap.vOverlap ^ 2 +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              (E.m.coeff 1) *
            N13OrdinaryCurveOverlap.vOverlap +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            (E.m.coeff 0))
  ring

/-- The vertical linear generator changes by the unit `x³` on the
ordinary overlap. -/
theorem affineLinearEquation_on_overlap
    (E : VerticalGraph) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineLinearEquation E) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.G E) := by
  have hG :
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.G E) =
        N13OrdinaryCurveOverlap.tOverlap -
          (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.a +
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.c *
              N13OrdinaryCurveOverlap.vOverlap) := by
    simp [N13IntegralInfinityVerticalGraphJacobian.G,
      N13IntegralInfinityVerticalGraphJacobian.L,
      N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
      N13IntegralInfinityChart.tClass,
      N13IntegralInfinityGraphJacobian.yClass,
      N13IntegralInfinityPointSpread.yClass,
      N13OrdinaryCurveOverlap.tOverlap,
      N13OrdinaryCurveOverlap.vOverlap,
      N13IntegralInfinityGraphSaturation.coefficientToInfinityOverlap_eq_algebraMap_R₂]
  rw [affineLinearEquation]
  simp only [map_sub, map_mul, map_pow,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineYImage,
    N13IntegralInfinityGraphSaturation.affineToInfinityOverlap_algebraMap_R₂,
    hG]
  change
    N13OrdinaryCurveOverlap.xOverlap ^ 2 -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.a *
            N13OrdinaryCurveOverlap.xOverlap ^ 3 -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.c *
          (N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (N13OrdinaryCurveOverlap.tOverlap -
          (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.a +
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.c *
              N13OrdinaryCurveOverlap.vOverlap))
  have htx :=
    N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hxt :
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
          N13OrdinaryCurveOverlap.tOverlap =
        N13OrdinaryCurveOverlap.xOverlap ^ 2 := by
    calc
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.tOverlap =
          N13OrdinaryCurveOverlap.xOverlap ^ 2 *
            (N13OrdinaryCurveOverlap.tOverlap *
              N13OrdinaryCurveOverlap.xOverlap) := by ring
      _ = N13OrdinaryCurveOverlap.xOverlap ^ 2 := by rw [htx, mul_one]
  linear_combination -hxt

/-- The three-generated affine closure and the vertical graph ideal agree
after restricting to the ordinary overlap. -/
theorem ideals_agree_on_overlap
    (u : R₂[X])
    (E : VerticalGraph)
    (huDegree : u.natDegree ≤ 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineIdeal u E) =
      Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        E.ideal := by
  let f :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
  let g : InfinityCurve →+* InfinityOverlap :=
    algebraMap InfinityCurve InfinityOverlap
  let J : Ideal InfinityOverlap :=
    Ideal.map g E.ideal
  have huJ :
      g (N13IntegralInfinityReduction.integralBaseClass u) ∈ J :=
    Ideal.mem_map_of_mem g huMem
  have hmJ :
      g (N13IntegralInfinityVerticalGraphJacobian.U E) ∈ J := by
    apply Ideal.mem_map_of_mem g
    rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal]
    exact Ideal.subset_span (by
      left
      rfl)
  have hGJ :
      g (N13IntegralInfinityVerticalGraphJacobian.G E) ∈ J := by
    apply Ideal.mem_map_of_mem g
    rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal]
    exact Ideal.subset_span (by
      right
      rfl)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · change f (affineReciprocal u) ∈ J
      rw [affineReciprocal_on_overlap u huDegree]
      exact Ideal.mul_mem_left J _ huJ
    · change f (affineVerticalEquation E) ∈ J
      rw [affineVerticalEquation_on_overlap E hmDegree]
      exact Ideal.mul_mem_left J _ hmJ
    · change f (affineLinearEquation E) ∈ J
      rw [affineLinearEquation_on_overlap E]
      exact Ideal.mul_mem_left J _ hGJ
  · rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal,
      Ideal.map_span, Set.image_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hgen :
          f (affineVerticalEquation E) ∈
            Ideal.map f (affineIdeal u E) :=
        Ideal.mem_map_of_mem f
          (Ideal.subset_span (by
            right
            left
            rfl))
      rw [affineVerticalEquation_on_overlap E hmDegree] at hgen
      exact
        (Ideal.unit_mul_mem_iff_mem
          (Ideal.map f (affineIdeal u E))
          (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow 6)).mp
          (by
            simpa [N13IntegralInfinityVerticalGraphJacobian.U] using hgen)
    · have hgen :
          f (affineLinearEquation E) ∈
            Ideal.map f (affineIdeal u E) :=
        Ideal.mem_map_of_mem f
          (Ideal.subset_span (by
            right
            right
            rfl))
      rw [affineLinearEquation_on_overlap E] at hgen
      exact
        (Ideal.unit_mul_mem_iff_mem
          (Ideal.map f (affineIdeal u E))
          (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow 3)).mp
          (by
            simpa [N13IntegralInfinityVerticalGraphJacobian.G,
              N13IntegralInfinityVerticalGraphJacobian.L] using hgen)

/-- The reflected reciprocal generator makes `x` a unit modulo the affine
vertical closure. -/
theorem affineIdeal_xUnitMod
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2) :
    N13IntegralInfinityGraphSaturation.XUnitMod
      (affineIdeal u E) := by
  let q : AffineCurve :=
    -N13GeneralizedMumfordIntegral.xClassHom
      (C (u.coeff 1) + C (u.coeff 0) * X)
  refine ⟨q, ?_⟩
  have hgen :
      affineReciprocal u ∈ affineIdeal u E :=
    Ideal.subset_span (by
      left
      rfl)
  rw [affineReciprocal,
    N13IntegralInfinityGraphSaturation.reflect_two_eq_one_add_X_mul
      u hu huDegree] at hgen
  convert hgen using 1
  simp only [q, N13OrdinaryCurveOverlap.xClass,
    N13GeneralizedMumfordIntegral.xClassHom_apply,
    map_add, map_mul, map_one]
  ring

/-- The three-generated affine closure is finitely generated. -/
theorem affineIdeal_fg
    (u : R₂[X])
    (E : VerticalGraph) :
    (affineIdeal u E).FG := by
  refine
    ⟨{affineReciprocal u,
        affineVerticalEquation E,
        affineLinearEquation E}, ?_⟩
  simp [affineIdeal]

/-- A vertical infinity graph plus its redundant monic reciprocal equation
has an invertible affine two-chart closure. -/
theorem affineIdeal_isUnit
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    IsUnit
      (affineIdeal u E :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  let K := FractionRing InfinityOverlap
  letI : Algebra AffineCurve InfinityOverlap :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap.toAlgebra
  letI : IsLocalization
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
      InfinityOverlap := by
    let e :
        N13OrdinaryCurveOverlap.AffineOverlap ≃ₐ[AffineCurve]
          InfinityOverlap :=
      { N13OrdinaryCurveOverlap.overlapEquiv with
        commutes' := fun z =>
          N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap z }
    exact
      IsLocalization.isLocalization_of_algEquiv
        (Submonoid.powers N13OrdinaryCurveOverlap.xClass) e
  letI : IsFractionRing AffineCurve K :=
    N13LocalizationIdealPatch.fractionRing_of_localization_fractionRing
      (A := AffineCurve) (B := InfinityOverlap) (K := K)
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
  letI : IsFractionRing InfinityCurve K :=
    N13LocalizationIdealPatch.fractionRing_of_localization_fractionRing
      (A := InfinityCurve) (B := InfinityOverlap) (K := K)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
  have hInfinityK :
      IsUnit
        (E.ideal : FractionalIdeal InfinityCurve⁰ K) := by
    let e :=
      FractionalIdeal.canonicalEquiv
        InfinityCurve⁰
        N13IntegralInfinityVerticalGraphJacobian.FunctionField K
    have hmap :=
      (N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit E).map
        e.toRingHom
    change
      IsUnit
        (e
          (E.ideal :
            FractionalIdeal InfinityCurve⁰
              N13IntegralInfinityVerticalGraphJacobian.FunctionField)) at hmap
    rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
    exact hmap
  have hInfinityOverlap :
      IsUnit
        (Ideal.map
            (algebraMap InfinityCurve InfinityOverlap)
            E.ideal :
          FractionalIdeal InfinityOverlap⁰ K) := by
    have hmap :=
      hInfinityK.map
        (N13LocalizationIdealPatch.extendFractional
          (A := InfinityCurve) (B := InfinityOverlap) (K := K)
          (Submonoid.powers N13IntegralInfinityChart.tClass))
    rw [N13LocalizationIdealPatch.extendFractional,
      FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.extended_coeIdeal_eq_map] at hmap
    exact hmap
  have hAffineOverlap :
      IsUnit
        (Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap
            (affineIdeal u E) :
          FractionalIdeal InfinityOverlap⁰ K) := by
    rw [ideals_agree_on_overlap
      u E huDegree.le hmDegree huMem]
    exact hInfinityOverlap
  have hAffineK :
      IsUnit
        (affineIdeal u E :
          FractionalIdeal AffineCurve⁰ K) := by
    apply
      N13LocalizationIdealPatch.ideal_isUnit_of_localized_isUnit
        (A := AffineCurve) (B := InfinityOverlap) (K := K)
        N13OrdinaryCurveOverlap.xClass
        (affineIdeal u E)
        (affineIdeal_fg u E)
    · obtain ⟨q, hq⟩ :=
        affineIdeal_xUnitMod u E hu huDegree
      exact ⟨q, by simpa [mul_comm] using hq⟩
    · rw [N13LocalizationIdealPatch.extendFractional,
        FractionalIdeal.extendedHom'_apply,
        FractionalIdeal.extended_coeIdeal_eq_map]
      exact hAffineOverlap
  letI : Algebra
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
    N13IntegralFractionalHull.integralToRational.toAlgebra
  letI : IsFractionRing
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
    N13IntegralFractionalHull.functionField_isFractionRing
  let e :=
    FractionalIdeal.canonicalEquiv
      AffineCurve⁰ K AffineFunctionField
  have hmap := hAffineK.map e.toRingHom
  change
    IsUnit
      (e
        (affineIdeal u E :
          FractionalIdeal AffineCurve⁰ K)) at hmap
  rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
  exact hmap

/-- Package a recovered vertical infinity graph and its weighted affine
closure as an actual invertible line on the two ordinary integral charts.
The reciprocal equation `u` is redundant on the overlap, but it is what
removes affine support at `x = 0` and hence makes the affine closure
invertible on the whole chart. -/
def twoChartLine
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    N13IntegralInfinityPointSpread.TwoChartLine where
  affineIdeal := affineIdeal u E
  infinityIdeal := E.ideal
  affine_isUnit :=
    affineIdeal_isUnit u E hu huDegree hmDegree huMem
  infinity_isUnit :=
    N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit E
  overlap_eq :=
    ideals_agree_on_overlap u E huDegree.le hmDegree huMem

end

end MazurProof.N13IntegralInfinityVerticalGraphTwoChart


