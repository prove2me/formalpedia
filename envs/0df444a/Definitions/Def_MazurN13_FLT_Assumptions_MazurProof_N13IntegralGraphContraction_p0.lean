-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphContraction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphContraction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:13:57.156153+00:00
-- url     : https://prove2.me/theorems/16fdf887-8f75-4767-a530-c82e966f0968
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralGraphContraction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralGraphContraction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralGraphContraction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFractionalHull_p0

set_option autoImplicit false




/-!
# Exact contraction of integral N13 graph ideals

Coefficient extension and contraction already fix a smooth integral
generalized Mumford graph ideal.  Completion of the square is a coordinate
ring equivalence, so it cancels formally from a further extension and
contraction.  Hence the standard sextic graph contracts to the original
integral graph exactly.

This is a representative-level equality.  It does not construct an
integral graph from a generic Picard class.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralGraphContraction

noncomputable section

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂

/-- The integral graph ideal attached to generalized Mumford data. -/
def graphIdeal (D : SmoothMumford₂) : Ideal IntegralRing :=
  N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v

/-- The integral graph ideal attached to arbitrary generalized Mumford
data. -/
def semiGraphIdeal (D : SemiMumford₂) : Ideal IntegralRing :=
  N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v

/-- A bijective second coordinate change cancels from extension followed by
contraction. -/
private theorem comap_map_comp_of_bijective
    {A B C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hg : Function.Bijective g)
    (I : Ideal A)
    (hI : (I.map f).comap f = I) :
    (I.map (g.comp f)).comap (g.comp f) = I := by
  calc
    (I.map (g.comp f)).comap (g.comp f) =
        (((I.map f).map g).comap g).comap f := by
      rw [Ideal.map_map, Ideal.comap_comap]
    _ = (I.map f).comap f := by
      rw [(I.map f).comap_map_of_bijective g hg]
    _ = I := hI

/-- Extension followed by contraction fixes an integral graph ideal. -/
theorem contractIdeal_map_graphIdeal
    (D : SmoothMumford₂) :
    N13IntegralModelContraction.contractIdeal
        (Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (graphIdeal D)) =
      graphIdeal D := by
  change
    (Ideal.map
      (N13GoodSexticCoordinateEquiv.toSextic.comp
        N13TwoAdicCoordinateBaseChange.extendCoordinate)
      (graphIdeal D)).comap
        (N13GoodSexticCoordinateEquiv.toSextic.comp
          N13TwoAdicCoordinateBaseChange.extendCoordinate) =
      graphIdeal D
  exact comap_map_comp_of_bijective
    N13TwoAdicCoordinateBaseChange.extendCoordinate
    N13GoodSexticCoordinateEquiv.toSextic
    (by
      change Function.Bijective
        (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
          (K := N13IntegralModelContraction.Q₂))
      exact
        (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
          (K := N13IntegralModelContraction.Q₂)).bijective)
    (graphIdeal D)
    (by
      simpa [graphIdeal] using
        N13TwoAdicCoordinateBaseChange.comap_map_mumfordIdeal D)

/-- Exact contraction already holds for an arbitrary integral semigraph.
Only monicity is used in the coefficient-descent argument. -/
theorem contractIdeal_map_semiGraphIdeal
    (D : SemiMumford₂) :
    N13IntegralModelContraction.contractIdeal
        (Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (semiGraphIdeal D)) =
      semiGraphIdeal D := by
  change
    (Ideal.map
      (N13GoodSexticCoordinateEquiv.toSextic.comp
        N13TwoAdicCoordinateBaseChange.extendCoordinate)
      (semiGraphIdeal D)).comap
        (N13GoodSexticCoordinateEquiv.toSextic.comp
          N13TwoAdicCoordinateBaseChange.extendCoordinate) =
      semiGraphIdeal D
  exact comap_map_comp_of_bijective
    N13TwoAdicCoordinateBaseChange.extendCoordinate
    N13GoodSexticCoordinateEquiv.toSextic
    (by
      change Function.Bijective
        (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
          (K := N13IntegralModelContraction.Q₂))
      exact
        (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
          (K := N13IntegralModelContraction.Q₂)).bijective)
    (semiGraphIdeal D)
    (by
      simpa [semiGraphIdeal] using
        N13TwoAdicCoordinateBaseChange.comap_map_mumfordIdeal_semi D)

/-- The standard sextic graph ideal of smooth integral data. -/
def sexticIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal
    (N13GoodSexticCoordinateEquiv.M
      (K := N13IntegralModelContraction.Q₂))
    (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
    (N13TwoAdicMumfordTransport.sexticSemi D nInf).v

/-- The standard sextic generic graph attached to arbitrary integral
generalized Mumford data. -/
def sexticSemiIdeal
    (D : SemiMumford₂) (nInf : ℤ) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal
    (N13GoodSexticCoordinateEquiv.M
      (K := N13IntegralModelContraction.Q₂))
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v

/-- The canonical contraction of the actual sextic graph is the original
integral graph ideal, not merely an ideal in the same Picard class. -/
theorem contractIdeal_sexticIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    N13IntegralModelContraction.contractIdeal
        (sexticIdeal D nInf) =
      graphIdeal D := by
  unfold sexticIdeal
  rw [←
    N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D nInf]
  simpa [graphIdeal] using contractIdeal_map_graphIdeal D

/-- Canonical contraction of an arbitrary transported integral semigraph
recovers the original integral graph ideal exactly. -/
theorem contractIdeal_sexticSemiIdeal
    (D : SemiMumford₂) (nInf : ℤ) :
    N13IntegralModelContraction.contractIdeal
        (sexticSemiIdeal D nInf) =
      semiGraphIdeal D := by
  unfold sexticSemiIdeal
  rw [←
    N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemiOfSemi
      D nInf]
  simpa [semiGraphIdeal] using
    contractIdeal_map_semiGraphIdeal D

/-- Fractional-ideal form of exact contraction. -/
theorem contractedFractional_sexticIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    N13IntegralFractionalHull.contractedFractional
        (sexticIdeal D nInf) =
      (graphIdeal D :
        FractionalIdeal IntegralRing⁰ FunctionField) := by
  exact congrArg
    (fun I : Ideal IntegralRing ↦
      (I : FractionalIdeal IntegralRing⁰ FunctionField))
    (contractIdeal_sexticIdeal D nInf)

/-- Fractional-ideal form of exact semigraph contraction. -/
theorem contractedFractional_sexticSemiIdeal
    (D : SemiMumford₂) (nInf : ℤ) :
    N13IntegralFractionalHull.contractedFractional
        (sexticSemiIdeal D nInf) =
      (semiGraphIdeal D :
        FractionalIdeal IntegralRing⁰ FunctionField) := by
  exact congrArg
    (fun I : Ideal IntegralRing ↦
      (I : FractionalIdeal IntegralRing⁰ FunctionField))
    (contractIdeal_sexticSemiIdeal D nInf)

end

end MazurProof.N13IntegralGraphContraction


