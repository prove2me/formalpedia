-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSaturation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSaturation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:09:50.536641+00:00
-- url     : https://prove2.me/theorems/c715f5c6-cda7-4b5d-90ce-30666df694d4
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphSpread_p0
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false




/-!
# Vertical saturation of reflected N13 infinity graphs

A monic graph on the integral infinity chart has quotient
`R₂[X] / (u)`, hence its quotient has no torsion from a nonzero base
scalar.  For a monic quadratic `u`, weighted reflection also makes the
affine coordinate `x` a unit modulo the reflected graph ideal.  These two
facts, together with equality on the ordinary overlap, show that the
reflected affine ideal is the canonical vertical contraction of its
generic fibre.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityGraphSaturation

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev Base : Type :=
  N13IntegralInfinityChart.Base

abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap

abbrev GraphData : Type :=
  N13IntegralInfinityGraphJacobian.GraphData

local instance integralRationalAlgebra :
    Algebra N13IntegralModelContraction.IntegralRing
      N13IntegralModelContraction.RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      N13IntegralModelContraction.RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

abbrev GraphResidue (D : GraphData) : Type :=
  Base ⧸ Ideal.span ({D.u} : Set Base)

private theorem graph_root_relation
    (D : GraphData) :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) D.v) = 0 := by
  change
    (X ^ 2 +
          C N13IntegralInfinityChart.hBase * X -
        C N13IntegralInfinityChart.rhsBase).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change
    Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base))
      (D.v ^ 2 +
        N13IntegralInfinityChart.hBase * D.v -
        N13IntegralInfinityChart.rhsBase) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

def graphEval (D : GraphData) :
    InfinityCurve →+* GraphResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) D.v)
    (graph_root_relation D)

@[simp] theorem graphEval_xClass
    (D : GraphData) (p : Base) :
    graphEval D
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) p := by
  change graphEval D
      (AdjoinRoot.of
        N13IntegralInfinityChart.infinityCurvePoly p) = _
  exact AdjoinRoot.lift_of (graph_root_relation D)

@[simp] theorem graphEval_yClass
    (D : GraphData) :
    graphEval D N13IntegralInfinityGraphJacobian.yClass =
      Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set Base)) D.v :=
  AdjoinRoot.lift_root (graph_root_relation D)

@[simp] theorem graphEval_baseClass
    (D : GraphData) (p : Base) :
    graphEval D
        (N13IntegralInfinityReduction.integralBaseClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) p := by
  change graphEval D
      (N13IntegralInfinityGraphJacobian.xClassHom p) = _
  exact graphEval_xClass D p

@[simp] theorem graphEval_vClass
    (D : GraphData) :
    graphEval D N13IntegralInfinityChart.vClass =
      Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set Base)) D.v := by
  change graphEval D N13IntegralInfinityGraphJacobian.yClass = _
  exact graphEval_yClass D

@[simp] theorem graphEval_ySubClass
    (D : GraphData) :
    graphEval D
        (GeneralizedGraphIdealCore.ySubClass
          N13IntegralInfinityGraphJacobian.xClassHom
          N13IntegralInfinityGraphJacobian.yClass D.v) = 0 := by
  simp [GeneralizedGraphIdealCore.ySubClass]

theorem infinityIdeal_le_ker
    (D : GraphData) :
    N13IntegralInfinityGraphTwoChart.infinityIdeal D ≤
      RingHom.ker (graphEval D) := by
  apply Ideal.span_le.mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change graphEval D
      (N13IntegralInfinityGraphJacobian.xClassHom D.u) = 0
    rw [graphEval_xClass, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  · exact graphEval_ySubClass D

theorem ker_graphEval
    (D : GraphData) :
    RingHom.ker (graphEval D) =
      N13IntegralInfinityGraphTwoChart.infinityIdeal D := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : Base :=
      N13IntegralInfinityReduction.integralCoeff0 z
    let q : Base :=
      N13IntegralInfinityReduction.integralCoeffV z
    have hz' :
        graphEval D
          (N13IntegralInfinityReduction.integralBaseClass p +
            N13IntegralInfinityReduction.integralBaseClass q *
              N13IntegralInfinityChart.vClass) = 0 := by
      rw [N13IntegralInfinityReduction.integral_recompose]
      exact hz
    have hquot :
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base))
          (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, graphEval_baseClass,
        graphEval_vClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu :
        N13IntegralInfinityGraphJacobian.xClassHom D.u ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D :=
      GeneralizedGraphIdealCore.xClass_mem_graphIdeal
        N13IntegralInfinityGraphJacobian.xClassHom
        N13IntegralInfinityGraphJacobian.yClass D.u D.v
    have hv :
        GeneralizedGraphIdealCore.ySubClass
            N13IntegralInfinityGraphJacobian.xClassHom
            N13IntegralInfinityGraphJacobian.yClass D.v ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D :=
      GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
        N13IntegralInfinityGraphJacobian.xClassHom
        N13IntegralInfinityGraphJacobian.yClass D.u D.v
    have hbase :
        N13IntegralInfinityGraphJacobian.xClassHom (p + q * D.v) ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D := by
      rw [hs, map_mul, mul_comm]
      exact Ideal.mul_mem_left _ _ hu
    have hgraph :
        N13IntegralInfinityGraphJacobian.xClassHom q *
            GeneralizedGraphIdealCore.ySubClass
              N13IntegralInfinityGraphJacobian.xClassHom
              N13IntegralInfinityGraphJacobian.yClass D.v ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D :=
      Ideal.mul_mem_left _ _ hv
    rw [← N13IntegralInfinityReduction.integral_recompose z]
    have hdecomp :
        N13IntegralInfinityReduction.integralBaseClass p +
            N13IntegralInfinityReduction.integralBaseClass q *
              N13IntegralInfinityChart.vClass =
          N13IntegralInfinityGraphJacobian.xClassHom (p + q * D.v) +
            N13IntegralInfinityGraphJacobian.xClassHom q *
              GeneralizedGraphIdealCore.ySubClass
                N13IntegralInfinityGraphJacobian.xClassHom
                N13IntegralInfinityGraphJacobian.yClass D.v := by
      change
        N13IntegralInfinityGraphJacobian.xClassHom p +
            N13IntegralInfinityGraphJacobian.xClassHom q *
              N13IntegralInfinityGraphJacobian.yClass =
          N13IntegralInfinityGraphJacobian.xClassHom (p + q * D.v) +
            N13IntegralInfinityGraphJacobian.xClassHom q *
              (N13IntegralInfinityGraphJacobian.yClass -
                N13IntegralInfinityGraphJacobian.xClassHom D.v)
      simp only [map_add, map_mul]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact infinityIdeal_le_ker D

/-- A monic infinity graph ideal is saturated with respect to every
nonzero scalar from the two-adic base. -/
theorem infinityIdeal_scalarSaturated
    (D : GraphData)
    (hu : D.u.Monic)
    (r : R₂) (hr : r ≠ 0)
    (z : InfinityCurve)
    (hz :
      algebraMap R₂ InfinityCurve r * z ∈
        N13IntegralInfinityGraphTwoChart.infinityIdeal D) :
    z ∈ N13IntegralInfinityGraphTwoChart.infinityIdeal D := by
  letI : Module.Free R₂ (GraphResidue D) :=
    hu.free_quotient
  have hker :
      algebraMap R₂ InfinityCurve r * z ∈
        RingHom.ker (graphEval D) := by
    rw [ker_graphEval]
    exact hz
  have hmap :
      graphEval D (algebraMap R₂ InfinityCurve r * z) = 0 :=
    hker
  have hscalar :
      r • graphEval D z =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) (C r) *
          graphEval D z := by
    obtain ⟨p, hp⟩ :=
      Ideal.Quotient.mk_surjective (graphEval D z)
    rw [← hp]
    change
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) (r • p) =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) (C r) *
          Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) p
    rw [Polynomial.smul_eq_C_mul]
    exact
      (Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set Base))).map_mul (C r) p
  have hsmul : r • graphEval D z = 0 := by
    rw [hscalar]
    have hscalarMap :
        graphEval D (algebraMap R₂ InfinityCurve r) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set Base)) (C r) := by
      change graphEval D
        (N13IntegralInfinityGraphJacobian.xClassHom (C r)) = _
      exact graphEval_xClass D (C r)
    simpa only [map_mul, hscalarMap] using hmap
  have heval : graphEval D z = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hr
  rw [← ker_graphEval D, RingHom.mem_ker]
  exact heval

/-- Saturation by base scalars is preserved when an ordinary ring is
localized in a horizontal element. -/
theorem scalarSaturated_map_localization
    {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    (M : Submonoid S)
    [IsLocalization M T]
    {I : Ideal S}
    (hI :
      ∀ (r : R), r ≠ 0 → ∀ z : S,
        algebraMap R S r * z ∈ I → z ∈ I) :
    ∀ (r : R), r ≠ 0 → ∀ z : T,
      algebraMap R T r * z ∈
          Ideal.map (algebraMap S T) I →
        z ∈ Ideal.map (algebraMap S T) I := by
  intro r hr z hz
  obtain ⟨⟨a, s⟩, hzs⟩ :=
    IsLocalization.surj M z
  let J : Ideal T :=
    Ideal.map (algebraMap S T) I
  have hraMap :
      algebraMap S T (algebraMap R S r * a) ∈ J := by
    have hmul :
        algebraMap S T (s : S) *
            (algebraMap R T r * z) ∈ J :=
      Ideal.mul_mem_left J _ hz
    have heq :
        algebraMap S T (algebraMap R S r * a) =
          algebraMap S T (s : S) *
            (algebraMap R T r * z) := by
      rw [map_mul, IsScalarTower.algebraMap_apply R S T, ← hzs]
      ring
    rw [heq]
    exact hmul
  have hraDenom :
      ∃ q ∈ M, (q : S) * (algebraMap R S r * a) ∈ I := by
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hraMap
    exact hraMap
  obtain ⟨q, hq, hqra⟩ := hraDenom
  have hqa : (q : S) * a ∈ I := by
    apply hI r hr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hqra
  have hqaMap :
      algebraMap S T ((q : S) * a) ∈ J :=
    Ideal.mem_map_of_mem (algebraMap S T) hqa
  have haMap : algebraMap S T a ∈ J := by
    apply
      (Ideal.unit_mul_mem_iff_mem J
        (IsLocalization.map_units T ⟨q, hq⟩)).mp
    simpa only [map_mul] using hqaMap
  have hzsMem :
      z * algebraMap S T (s : S) ∈ J := by
    rw [hzs]
    exact haMap
  apply
    (Ideal.unit_mul_mem_iff_mem J
      (IsLocalization.map_units T s)).mp
  simpa only [mul_comm] using hzsMem

/-- The affine coordinate is a unit in the quotient by `I`. -/
def XUnitMod (I : Ideal AffineCurve) : Prop :=
  ∃ q : AffineCurve,
    1 - q * N13OrdinaryCurveOverlap.xClass ∈ I

/-- A monic polynomial of degree two is determined by its two lower
coefficients. -/
theorem monic_quadratic_eq
    (u : R₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    u = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
  have hc₂ : u.coeff 2 = 1 := by
    calc
      u.coeff 2 = u.coeff u.natDegree :=
        congrArg u.coeff hdeg.symm
      _ = 1 := hu.coeff_natDegree
  have hdegree : u.degree ≤ 2 := by
    rw [degree_eq_natDegree hu.ne_zero, hdeg]
    norm_num
  calc
    u =
        C (u.coeff 2) * X ^ 2 +
          C (u.coeff 1) * X +
          C (u.coeff 0) :=
      u.eq_quadratic_of_degree_le_two hdegree
    _ = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
      rw [hc₂, C_1]
      ring

/-- A monic quadratic reflects to a polynomial with constant coefficient
one and an explicit remaining multiple of `X`. -/
theorem reflect_two_eq_one_add_X_mul
    (u : R₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    u.reflect 2 =
      1 + X * (C (u.coeff 1) + C (u.coeff 0) * X) := by
  have hshape := monic_quadratic_eq u hu hdeg
  have hX2 :
      ((X : R₂[X]) ^ 2).reflect 2 = 1 := by
    simpa using
      (reflect_monomial 2 2 (R := R₂))
  have hCX :
      (C (u.coeff 1) * X : R₂[X]).reflect 2 =
        C (u.coeff 1) * X := by
    simpa using
      (reflect_C_mul_X_pow
        (R := R₂) 2 1 (c := u.coeff 1))
  calc
    u.reflect 2 =
        (X ^ 2 + C (u.coeff 1) * X +
          C (u.coeff 0)).reflect 2 :=
      congrArg (fun p : R₂[X] => p.reflect 2) hshape
    _ =
        (X ^ 2).reflect 2 +
          (C (u.coeff 1) * X).reflect 2 +
          (C (u.coeff 0)).reflect 2 := by
            rw [reflect_add, reflect_add]
    _ = 1 + X * (C (u.coeff 1) + C (u.coeff 0) * X) := by
      rw [hX2, hCX, reflect_C]
      ring

/-- Reflection of a monic quadratic has constant coefficient one, so the
affine coordinate is invertible modulo the reflected graph ideal. -/
theorem affineIdeal_xUnitMod
    (D : GraphData)
    (hu : D.u.Monic)
    (hdeg : D.u.natDegree = 2) :
    XUnitMod
      (N13IntegralInfinityGraphTwoChart.affineIdeal D) := by
  let q : AffineCurve :=
    -N13GeneralizedMumfordIntegral.xClassHom
      (C (D.u.coeff 1) + C (D.u.coeff 0) * X)
  refine ⟨q, ?_⟩
  have hgen :
      N13GeneralizedMumfordIntegral.xClassHom
          (N13IntegralInfinityGraphTwoChart.affineU D) ∈
        N13IntegralInfinityGraphTwoChart.affineIdeal D :=
    GeneralizedGraphIdealCore.xClass_mem_graphIdeal
      N13GeneralizedMumfordIntegral.xClassHom
      N13GeneralizedMumfordIntegral.yClass
      (N13IntegralInfinityGraphTwoChart.affineU D)
      (N13IntegralInfinityGraphTwoChart.affineV D)
  rw [N13IntegralInfinityGraphTwoChart.affineU,
    reflect_two_eq_one_add_X_mul D.u hu hdeg] at hgen
  convert hgen using 1
  simp only [q, N13OrdinaryCurveOverlap.xClass,
    N13GeneralizedMumfordIntegral.xClassHom_apply,
    map_add, map_mul, map_one]
  ring

theorem mem_of_x_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    {z : AffineCurve}
    (hz : N13OrdinaryCurveOverlap.xClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := hx
  have h₁ := Ideal.mul_mem_left I z hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1 <;> ring

theorem mem_of_x_pow_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    (n : ℕ) {z : AffineCurve}
    (hz : N13OrdinaryCurveOverlap.xClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_x_mul_mem hx
      convert hz using 1 <;> simp only [pow_succ] <;> ring

/-- Localizing at `x` loses no ideal information when `x` is already a
unit modulo the ideal. -/
theorem comap_map_affineOverlap_eq_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap)
        (Ideal.map
          (algebraMap AffineCurve
            N13OrdinaryCurveOverlap.AffineOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap z ∈
        Ideal.map
          (algebraMap AffineCurve
            N13OrdinaryCurveOverlap.AffineOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_x_pow_mul_mem hx n hmz
  · exact Ideal.le_comap_map

/-- The actual affine-to-infinity overlap map is the localization map
followed by the chart equivalence. -/
private theorem affineToInfinityOverlap_eq_comp :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13OrdinaryCurveOverlap.overlapEquiv.toRingHom.comp
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap) := by
  apply DFunLike.ext _ _
  intro z
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap z =
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap z)
  exact
    (N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap
      z).symm

/-- Restriction to the actual ordinary overlap loses no information from
an affine ideal when `x` is already a unit modulo that ideal. -/
theorem affineOverlapContracted_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I) =
      I := by
  let loc :
      AffineCurve →+*
        N13OrdinaryCurveOverlap.AffineOverlap :=
    algebraMap AffineCurve
      N13OrdinaryCurveOverlap.AffineOverlap
  let e :
      N13OrdinaryCurveOverlap.AffineOverlap →+*
        InfinityOverlap :=
    N13OrdinaryCurveOverlap.overlapEquiv.toRingHom
  have he :
      Ideal.comap e (Ideal.map e (Ideal.map loc I)) =
        Ideal.map loc I := by
    rw [Ideal.comap_map_of_surjective e
      N13OrdinaryCurveOverlap.overlapEquiv.surjective]
    have hker : RingHom.ker e = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e).mp
        N13OrdinaryCurveOverlap.overlapEquiv.injective
    rw [← RingHom.ker_eq_comap_bot, hker, sup_bot_eq]
  rw [affineToInfinityOverlap_eq_comp,
    ← Ideal.map_map, ← Ideal.comap_comap, he]
  exact comap_map_affineOverlap_eq_of_xUnitMod hx

@[simp] theorem affineToInfinityOverlap_algebraMap_R₂
    (r : R₂) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (algebraMap R₂ AffineCurve r) =
      algebraMap R₂ InfinityOverlap r := by
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (C r)) =
      _
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13OrdinaryCurveOverlap.affineCoeffMap_C]
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r
  exact IsScalarTower.algebraMap_apply R₂ InfinityCurve InfinityOverlap r

@[simp] theorem infinityOverlap_algebraMap_R₂
    (r : R₂) :
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r := by
  exact IsScalarTower.algebraMap_apply R₂ InfinityCurve InfinityOverlap r

/-- The named coefficient map is the ordinary scalar map into the
infinity overlap. -/
@[simp] theorem coefficientToInfinityOverlap_eq_algebraMap_R₂
    (r : R₂) :
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r =
      algebraMap R₂ InfinityOverlap r := by
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r
  exact infinityOverlap_algebraMap_R₂ r

/-- A monic quadratic infinity graph with a bounded ordinate has a
vertically saturated reflected affine closure. -/
theorem affineIdeal_scalarSaturated
    (D : GraphData)
    (hu : D.u.Monic)
    (hdeg : D.u.natDegree = 2)
    (hv : D.v.natDegree ≤ 3)
    (r : R₂) (hr : r ≠ 0)
    (z : AffineCurve)
    (hz :
      algebraMap R₂ AffineCurve r * z ∈
        N13IntegralInfinityGraphTwoChart.affineIdeal D) :
    z ∈ N13IntegralInfinityGraphTwoChart.affineIdeal D := by
  let Ia :=
    N13IntegralInfinityGraphTwoChart.affineIdeal D
  let Ii :=
    N13IntegralInfinityGraphTwoChart.infinityIdeal D
  let f :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
  let g : InfinityCurve →+* InfinityOverlap :=
    algebraMap InfinityCurve InfinityOverlap
  have hoverlap :
      Ideal.map f Ia = Ideal.map g Ii := by
    exact
      N13IntegralInfinityGraphTwoChart.ideals_agree_on_overlap
        D hdeg.le hv
  have hInfOverlap :
      ∀ (s : R₂), s ≠ 0 → ∀ w : InfinityOverlap,
        algebraMap R₂ InfinityOverlap s * w ∈ Ideal.map g Ii →
          w ∈ Ideal.map g Ii := by
    exact
      scalarSaturated_map_localization
        (R := R₂) (S := InfinityCurve) (T := InfinityOverlap)
        (Submonoid.powers N13IntegralInfinityChart.tClass)
        (infinityIdeal_scalarSaturated D hu)
  have hrzOverlap :
      algebraMap R₂ InfinityOverlap r * f z ∈
        Ideal.map g Ii := by
    rw [← hoverlap]
    have hm := Ideal.mem_map_of_mem f hz
    simpa only [f, Ia, map_mul,
      affineToInfinityOverlap_algebraMap_R₂]
      using hm
  have hzOverlap :
      f z ∈ Ideal.map g Ii :=
    hInfOverlap r hr (f z) hrzOverlap
  have hzComap :
      z ∈ Ideal.comap f (Ideal.map f Ia) := by
    change f z ∈ Ideal.map f Ia
    rw [hoverlap]
    exact hzOverlap
  rw [affineOverlapContracted_of_xUnitMod
    (affineIdeal_xUnitMod D hu hdeg)] at hzComap
  exact hzComap

/-- A vertically saturated ideal is recovered exactly after extension to
the generic fibre and contraction. -/
theorem contractIdeal_eq_of_map_eq_of_scalarSaturated
    {I : Ideal N13IntegralModelContraction.IntegralRing}
    {J : Ideal N13IntegralModelContraction.RationalRing}
    (hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic I =
        J)
    (hsat :
      ∀ (r : R₂), r ≠ 0 →
        ∀ z : N13IntegralModelContraction.IntegralRing,
          algebraMap R₂
              N13IntegralModelContraction.IntegralRing r * z ∈ I →
            z ∈ I) :
    N13IntegralModelContraction.contractIdeal J = I := by
  apply le_antisymm
  · intro z hz
    change
      N13TwoAdicCoordinateBaseChange.integralToSextic z ∈ J at hz
    rw [← hmap] at hz
    change
      algebraMap N13IntegralModelContraction.IntegralRing
          N13IntegralModelContraction.RationalRing z ∈
        Ideal.map
          (algebraMap N13IntegralModelContraction.IntegralRing
            N13IntegralModelContraction.RationalRing) I at hz
    letI :
        IsLocalization
          N13IntegralModelContraction.verticalScalars
          N13IntegralModelContraction.RationalRing :=
      N13IntegralModelContraction.rationalRing_isLocalization
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      N13IntegralModelContraction.verticalScalars] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    change
      ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
        algebraMap R₂
          N13IntegralModelContraction.IntegralRing r = m at hm
    obtain ⟨r, hr, rfl⟩ := hm
    exact
      hsat r (mem_nonZeroDivisors_iff_ne_zero.mp hr) z hmz
  · intro z hz
    change
      N13TwoAdicCoordinateBaseChange.integralToSextic z ∈ J
    rw [← hmap]
    exact Ideal.mem_map_of_mem
      N13TwoAdicCoordinateBaseChange.integralToSextic hz

/-- The reflected affine closure of a monic quadratic infinity graph is
the canonical contraction of any generic ideal that it extends to. -/
theorem contractIdeal_eq_affineIdeal
    (J : Ideal N13IntegralModelContraction.RationalRing)
    (D : GraphData)
    (hu : D.u.Monic)
    (hdeg : D.u.natDegree = 2)
    (hv : D.v.natDegree ≤ 3)
    (hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityGraphTwoChart.affineIdeal D) =
        J) :
    N13IntegralModelContraction.contractIdeal J =
      N13IntegralInfinityGraphTwoChart.affineIdeal D :=
  contractIdeal_eq_of_map_eq_of_scalarSaturated hmap
    (affineIdeal_scalarSaturated D hu hdeg hv)

/-- Once the reflected graph is the canonical contraction, its
divisorial hull is a unit fractional ideal. -/
theorem divisorialHull_isUnit_of_reciprocalGraph
    (J : Ideal N13IntegralModelContraction.RationalRing)
    (D : GraphData)
    (hu : D.u.Monic)
    (hdeg : D.u.natDegree = 2)
    (hv : D.v.natDegree ≤ 3)
    (hw : D.w.natDegree ≤ 4)
    (hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityGraphTwoChart.affineIdeal D) =
        J) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) := by
  exact
    N13IntegralGraphSpread.divisorialHull_isUnit_of_contractIdeal_eq_isUnit
        J
        (N13IntegralInfinityGraphTwoChart.affineIdeal D)
        (contractIdeal_eq_affineIdeal J D hu hdeg hv hmap)
        (N13IntegralInfinityGraphTwoChart.affineIdeal_isUnit
          D hdeg.le hv hw hu.ne_zero)

end

end MazurProof.N13IntegralInfinityGraphSaturation


