-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:23:57.62827+00:00
-- url     : https://prove2.me/theorems/a057e696-d62e-410c-a318-9deade2ed259
-- title:
--   FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConcreteGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p2
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralAffinePointSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityPointSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalizationIdealPatch_p0
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false




/-!
# Proper two-chart closure of a finite N13 affine divisor

An invertible ideal on the affine chart need not by itself record its
behaviour at infinity.  For an ideal with finite support over the two-adic
coefficient ring, however, the affine coordinate is integral in the
quotient.  A monic equation for that coordinate reflects to an equation with
constant coefficient one on the infinity chart.  Hence the infinity
uniformizer is a unit modulo the contracted overlap ideal.

The principal-localization patching theorem then upgrades invertibility on
the punctured infinity chart to invertibility on the full infinity chart.
This supplies proper extensions for finite N13 graph ideals, including
integral affine points and the finite irreducible quadratic branch, without
choosing reciprocal coordinates.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13FiniteAffineTwoChart

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The integral two-adic coefficient ring of the good N13 model. -/
abbrev R₂ : Type :=
  N13FiniteContractIdealInvertible.R₂

/-- The two-adic coefficient field of the generic N13 model. -/
abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

/-- The good sextic model used by the canonical Mumford contraction. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13FiniteContractIdealInvertible.Model

/-- The ordinary affine integral chart. -/
abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve

/-- The ordinary infinity integral chart. -/
abbrev InfinityCurve : Type :=
  N13OrdinaryCurveOverlap.InfinityCurve

/-- The common principal-open overlap, expressed in infinity coordinates. -/
abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap

/-- The canonical function field used for affine fractional ideals. -/
abbrev AffineFunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField

/-- Affine fractional ideals in the canonical N13 function field. -/
abbrev AffineFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal

/-- Infinity-chart fractional ideals in its canonical fraction field. -/
abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityPointSpread.InfinityFractionalIdeal

/-- The canonical affine integral lattice attached to a generic Mumford
graph.  Keeping the contraction as an ordinary ideal makes it directly
usable as the affine component of a two-chart line. -/
def finiteAffineIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal AffineCurve :=
  N13IntegralModelContraction.contractIdeal
    (N13CanonicalContractionQuotient.graphIdeal D)

/-- Extending the canonical affine lattice to the generic coefficient field
recovers the Mumford graph ideal literally. -/
@[simp] theorem map_finiteAffineIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (finiteAffineIdeal D) =
      N13CanonicalContractionQuotient.graphIdeal D := by
  simpa [finiteAffineIdeal] using
    N13IntegralModelContraction.map_contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)

/-- Finite quadratic support makes the canonical affine lattice invertible. -/
theorem finiteAffineIdeal_isUnit
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (AffineCurve ⧸ finiteAffineIdeal D)) :
    IsUnit
      (finiteAffineIdeal D : AffineFractionalIdeal) := by
  simpa [finiteAffineIdeal] using
    N13FiniteContractIdealInvertible.contractIdeal_isUnit_of_finite_quadratic
      D hdeg hfinite

/-- The infinity-chart closure of an affine ideal is obtained by restricting
to the ordinary overlap and contracting back to the infinity chart. -/
def infinityClosure
    (I : Ideal AffineCurve) : Ideal InfinityCurve :=
  (Ideal.map
      N13OrdinaryCurveOverlap.affineToInfinityOverlap I).under
    InfinityCurve

/-- Restricting the contracted infinity closure back to `D(t)` recovers the
localized affine ideal exactly. -/
theorem map_infinityClosure
    (I : Ideal AffineCurve) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (infinityClosure I) =
      Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap I := by
  simpa [infinityClosure] using
    (IsLocalization.map_under
      (R := InfinityCurve)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
      InfinityOverlap
      (Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap I))

/-- Weighted reflection in the infinity variable converts a monic affine
equation into the same equation on the overlap, up to the invertible power
of `x = t⁻¹`. -/
theorem infinityReflect_mul_xPow_on_overlap
    (p : R₂[X]) :
    (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass
            (p.reflect p.natDegree)) *
        N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) := by
  letI : Invertible N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.invertible
  have hinv :
      ⅟N13OrdinaryCurveOverlap.xOverlap =
        N13OrdinaryCurveOverlap.tOverlap := by
    exact
      invOf_eq_right_inv
        (by simp [mul_comm])
  have hreflect :=
    Polynomial.eval₂_reflect_mul_pow
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.xOverlap
      p.natDegree p le_rfl
  rw [hinv] at hreflect
  rw [show
      N13IntegralInfinityReduction.integralBaseClass
          (p.reflect p.natDegree) =
        N13IntegralInfinityGraphJacobian.xClassHom
          (p.reflect p.natDegree) by rfl,
    N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  simpa [N13OrdinaryCurveOverlap.affineCoeffMap] using hreflect

/-- A monic polynomial reflects at its degree to a polynomial with constant
coefficient one.  Separating that constant term exposes the infinity
uniformizer needed by the patching argument. -/
theorem reflect_natDegree_eq_one_add_X_mul
    (p : R₂[X]) (hp : p.Monic) :
    p.reflect p.natDegree =
      1 + X * (p.reflect p.natDegree).divX := by
  have hcoeff :
      (p.reflect p.natDegree).coeff 0 = 1 := by
    rw [Polynomial.coeff_reflect]
    simpa using hp.coeff_natDegree
  calc
    p.reflect p.natDegree =
        X * (p.reflect p.natDegree).divX +
          C ((p.reflect p.natDegree).coeff 0) :=
      (Polynomial.X_mul_divX_add _).symm
    _ = 1 + X * (p.reflect p.natDegree).divX := by
      rw [hcoeff, C_1]
      ring

/-- Finite affine support forces the infinity coordinate `t` to be a unit
modulo the contracted infinity closure.  A monic equation for `x` reflects
to a relation with constant coefficient one in `t`. -/
theorem infinityClosure_tUnitMod_of_finite
    (I : Ideal AffineCurve)
    (hfinite :
      Module.Finite R₂ (AffineCurve ⧸ I)) :
    ∃ a : InfinityCurve,
      1 - N13IntegralInfinityChart.tClass * a ∈
        infinityClosure I := by
  letI : Module.Finite R₂ (AffineCurve ⧸ I) :=
    hfinite
  let xbar : AffineCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  obtain ⟨p, hpMonic, hpEval⟩ :=
    IsIntegral.of_finite R₂ xbar
  have hpMem :
      N13GeneralizedMumfordIntegral.xClassHom p ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass p) = 0
    rw [← N13ConcreteGraphRecovery.quotient_aeval_integralX]
    exact hpEval
  let r : R₂[X] :=
    p.reflect p.natDegree
  have hrMem :
      N13IntegralInfinityReduction.integralBaseClass r ∈
        infinityClosure I := by
    change
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass r) ∈
        Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I
    have hpMap :
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
            (N13GeneralizedMumfordIntegral.xClassHom p) ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I :=
      Ideal.mem_map_of_mem
        N13OrdinaryCurveOverlap.affineToInfinityOverlap hpMem
    have hprod :
        (algebraMap InfinityCurve InfinityOverlap)
              (N13IntegralInfinityReduction.integralBaseClass r) *
            N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I := by
      change
        (algebraMap InfinityCurve InfinityOverlap)
              (N13IntegralInfinityReduction.integralBaseClass
                (p.reflect p.natDegree)) *
            N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I
      rw [infinityReflect_mul_xPow_on_overlap p]
      exact hpMap
    exact
      (Ideal.unit_mul_mem_iff_mem
        (Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I)
        (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow
          p.natDegree)).mp
        (by simpa [mul_comm] using hprod)
  let q : InfinityCurve :=
    -N13IntegralInfinityReduction.integralBaseClass r.divX
  refine ⟨q, ?_⟩
  change
    N13IntegralInfinityReduction.integralBaseClass
        (p.reflect p.natDegree) ∈
      infinityClosure I at hrMem
  rw [reflect_natDegree_eq_one_add_X_mul p hpMonic] at hrMem
  convert hrMem using 1
  simp only [q, N13IntegralInfinityReduction.integralBaseClass,
    map_add, map_mul, map_one]
  rw [show
    (algebraMap
        N13IntegralInfinityReduction.IntegralBase
        N13IntegralInfinityReduction.IntegralRing) X =
      N13IntegralInfinityChart.tClass by rfl]
  rw [mul_neg, sub_neg_eq_add]

/-- An invertible affine divisor with finite support has an invertible
closure on the ordinary infinity chart.

The finite quotient supplies a monic equation for the affine coordinate.
After reflection, that equation makes `t` a unit modulo the infinity
closure; invertibility on `D(t)` then patches across `t = 0`. -/
theorem infinityClosure_isUnit_of_finite
    (I : Ideal AffineCurve)
    (hI : IsUnit (I : AffineFractionalIdeal))
    (hfinite :
      Module.Finite R₂ (AffineCurve ⧸ I)) :
    IsUnit
      (infinityClosure I : InfinityFractionalIdeal) := by
  letI : Algebra
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
    N13IntegralFractionalHull.integralToRational.toAlgebra
  letI : IsFractionRing
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
    N13IntegralFractionalHull.functionField_isFractionRing
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
  have hAffineK :
      IsUnit (I : FractionalIdeal AffineCurve⁰ K) := by
    let e :=
      FractionalIdeal.canonicalEquiv
        AffineCurve⁰ AffineFunctionField K
    have hmap := hI.map e.toRingHom
    change
      IsUnit
        (e (I : FractionalIdeal AffineCurve⁰ AffineFunctionField)) at hmap
    rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
    exact hmap
  have hAffineOverlap :
      IsUnit
        (Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I :
          FractionalIdeal InfinityOverlap⁰ K) := by
    have hmap :=
      hAffineK.map
        (N13LocalizationIdealPatch.extendFractional
          (A := AffineCurve) (B := InfinityOverlap) (K := K)
          (Submonoid.powers N13OrdinaryCurveOverlap.xClass))
    rw [N13LocalizationIdealPatch.extendFractional,
      FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.extended_coeIdeal_eq_map] at hmap
    exact hmap
  have hmod :=
    infinityClosure_tUnitMod_of_finite I hfinite
  have hInfinityK :
      IsUnit
        (infinityClosure I :
          FractionalIdeal InfinityCurve⁰ K) := by
    apply
      N13LocalizationIdealPatch.ideal_isUnit_of_localized_isUnit
        (A := InfinityCurve) (B := InfinityOverlap) (K := K)
        N13IntegralInfinityChart.tClass
        (infinityClosure I)
        (infinityClosure I).fg_of_isNoetherianRing
        hmod
    rw [N13LocalizationIdealPatch.extendFractional,
      FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.extended_coeIdeal_eq_map,
      map_infinityClosure]
    exact hAffineOverlap
  let e :=
    FractionalIdeal.canonicalEquiv
      InfinityCurve⁰ K N13IntegralInfinityPointSpread.FunctionField
  have hmap := hInfinityK.map e.toRingHom
  change
    IsUnit
      (e (infinityClosure I :
        FractionalIdeal InfinityCurve⁰ K)) at hmap
  rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
  exact hmap

/-- The contracted infinity closure and an invertible affine ideal assemble
to a proper line on the two ordinary charts. -/
def twoChartLineOfInfinityClosure
    (I : Ideal AffineCurve)
    (hI : IsUnit (I : AffineFractionalIdeal))
    (hfinite : Module.Finite R₂ (AffineCurve ⧸ I)) :
    N13IntegralInfinityPointSpread.TwoChartLine where
  affineIdeal := I
  infinityIdeal := infinityClosure I
  affine_isUnit := hI
  infinity_isUnit :=
    infinityClosure_isUnit_of_finite I hI hfinite
  overlap_eq := (map_infinityClosure I).symm

/-! ## Integral affine point lines -/

/-- The quotient by the monic graph ideal of an integral affine point is
finite over the two-adic coefficient ring. -/
theorem integralPointIdeal_quotient_finite
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Module.Finite R₂
      (AffineCurve ⧸
        N13IntegralAffinePointSpread.pointIdeal P) := by
  let D :=
    N13IntegralAffinePointSpread.integralSemiGraph P
  letI : Module.Finite R₂
      (N13GeneralizedMumfordIntegral.MumfordResidue D) :=
    D.u_monic.finite_quotient
  exact
    Module.Finite.equiv
      (N13GeneralizedMumfordIntegral.mumfordQuotientAlgEquiv
        D).symm.toLinearEquiv

/-- An integral affine point has an actual proper two-chart line, obtained
by closing its literal affine graph ideal through the ordinary overlap. -/
def integralPointTwoChartLine
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  twoChartLineOfInfinityClosure
    (N13IntegralAffinePointSpread.pointIdeal P)
    (N13IntegralAffinePointSpread.pointIdeal_isUnit P)
    (integralPointIdeal_quotient_finite P)

/-- The affine generic fibre of the proper integral point line is exactly
the standard sextic point graph. -/
@[simp] theorem map_integralPointTwoChartLine_affineIdeal
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (integralPointTwoChartLine P).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).u
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralAffinePointSpread.pointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).u
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).v
  exact N13IntegralAffinePointSpread.map_pointIdeal P

/-! ## Finite quadratic lines -/

/-- A finite quadratic Mumford graph has an actual proper two-chart integral
line whose affine generic fibre is the original graph ideal. -/
def finiteQuadraticTwoChartLine
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (AffineCurve ⧸ finiteAffineIdeal D)) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  twoChartLineOfInfinityClosure
    (finiteAffineIdeal D)
    (finiteAffineIdeal_isUnit D hdeg hfinite)
    hfinite

/-- The affine generic fibre of the finite quadratic proper line is exactly
the original Mumford graph ideal. -/
@[simp] theorem map_finiteQuadraticTwoChartLine_affineIdeal
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (AffineCurve ⧸ finiteAffineIdeal D)) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (finiteQuadraticTwoChartLine D hdeg hfinite).affineIdeal =
      N13CanonicalContractionQuotient.graphIdeal D := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (finiteAffineIdeal D) =
      N13CanonicalContractionQuotient.graphIdeal D
  exact map_finiteAffineIdeal D

end

end MazurProof.N13FiniteAffineTwoChart


