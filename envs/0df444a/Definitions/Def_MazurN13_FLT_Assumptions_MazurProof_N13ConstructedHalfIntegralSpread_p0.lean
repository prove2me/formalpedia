-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConstructedHalfIntegralSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ConstructedHalfIntegralSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T17:38:31.484659+00:00
-- url     : https://prove2.me/theorems/aff9873b-81a1-4521-9404-f90efa921ea7
-- title:
--   FLT.Assumptions.MazurProof.N13ConstructedHalfIntegralSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ConstructedHalfIntegralSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ConstructedHalfIntegralSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p2
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBaseChange_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialProductLift_p0

set_option autoImplicit false




/-!
# The integral spread of the N13 constructed half

The proof of two-surjectivity selects a concrete invertible fractional-ideal
root over `ℚ`.  Base change sends that exact root to `ℚ₂`.  Multiplication by
its canonical fractional-ideal denominator produces an ordinary ideal, so
the existing contraction/divisorial-hull machinery applies without choosing
a different half.

The resulting hull has generic fibre equal to the selected root up to the
displayed principal denominator.  Its remaining integral invertibility
condition is exactly the existing three-product special trace lift.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13ConstructedHalfIntegralSpread

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open SexticMumford

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev G : Type :=
  N13MumfordFullKummerTwoSurjective.G

abbrev Q₂ : Type :=
  N13InfinityBaseChange.Q₂

abbrev Mℚ : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev M₂ : SexticMumford.Model Q₂ :=
  N13Mumford.model Q₂

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev RationalFractionalIdeal : Type :=
  N13IntegralFractionalHull.RationalFractionalIdeal

/-- Base change on invertible affine fractional ideals from `ℚ` to `ℚ₂`. -/
def invFracBaseChange :
    SexticMumford.InvFrac Mℚ →*
      SexticMumford.InvFrac M₂ :=
  SexticMumford.OrientedBaseChange.invFracMap
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f
      N13InfinityBaseChange.ratToQ₂)

/-- The exact Padé-selected ideal root, after coefficient extension to
`ℚ₂`. -/
def twoAdicIdealRoot (P : G) :
    SexticMumford.InvFrac M₂ :=
  invFracBaseChange
    (N13MumfordFullKummerTwoSurjective.constructedHalfData
      P).finite.idealRoot

/-- The literal polynomial generator retained by the selected Padé
branch. -/
def graphU (P : G) : ℚ[X] :=
  (N13MumfordFullKummerTwoSurjective.constructedHalfData
    P).finite.graphU

/-- The literal graph polynomial retained by the selected Padé branch. -/
def graphV (P : G) : ℚ[X] :=
  (N13MumfordFullKummerTwoSurjective.constructedHalfData
    P).finite.graphV

theorem graphU_ne_zero (P : G) :
    graphU P ≠ 0 :=
  (N13MumfordFullKummerTwoSurjective.constructedHalfData
    P).finite.graphU_ne_zero

/-- Whether the selected fractional root or its inverse is the retained
graph ideal. -/
def inverseOrientation (P : G) : Bool :=
  (N13MumfordFullKummerTwoSurjective.constructedHalfData
    P).finite.inverseOrientation

/-- The coefficient-extended literal graph ideal selected by the Padé
construction. -/
def twoAdicGraphIdeal (P : G) : Ideal RationalRing :=
  SexticMumford.mumfordIdeal M₂
    ((graphU P).map N13InfinityBaseChange.ratToQ₂)
    ((graphV P).map N13InfinityBaseChange.ratToQ₂)

/-- The canonical monic/remainder rational Mumford representative of the
retained Padé graph. -/
def normalizedGraphMumford (P : G) :
    SexticMumford.Mumford Mℚ :=
  N13MumfordFullKummerIdentityFiber.FiniteIdealGraphRootData.normalizedGraphMumford
      (N13MumfordFullKummerTwoSurjective.constructedHalfData
        P).finite.toFiniteIdealGraphRootData

/-- Coefficient extension of the canonical retained graph to `ℚ₂`. -/
def twoAdicNormalizedGraphMumford (P : G) :
    SexticMumford.Mumford M₂ :=
  (normalizedGraphMumford P).mapCoeffs
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f
      N13InfinityBaseChange.ratToQ₂)

/-- The coefficient-extended normalized Mumford pair presents exactly the
same ordinary graph ideal as the original retained Padé polynomials. -/
theorem mumfordIdeal_twoAdicNormalizedGraph_eq
    (P : G) :
    SexticMumford.mumfordIdeal M₂
        (twoAdicNormalizedGraphMumford P).u
        (twoAdicNormalizedGraphMumford P).v =
      twoAdicGraphIdeal P := by
  have h :=
    congrArg
      (Ideal.map
        (SexticMumford.OrientedBaseChange.coordinateMap
          (M := Mℚ) (M' := M₂)
          N13InfinityBaseChange.ratToQ₂
          (N13InfinityBaseChange.map_n13_f
            N13InfinityBaseChange.ratToQ₂)))
      (N13MumfordFullKummerIdentityFiber.FiniteIdealGraphRootData.mumfordIdeal_normalizedGraphMumford
          (N13MumfordFullKummerTwoSurjective.constructedHalfData
            P).finite.toFiniteIdealGraphRootData)
  simpa only [normalizedGraphMumford,
    twoAdicNormalizedGraphMumford,
    SexticMumford.mapCoeffs_u,
    SexticMumford.mapCoeffs_v,
    graphU, graphV, twoAdicGraphIdeal,
    SexticMumford.OrientedBaseChange.map_mumfordIdeal] using h

/-- The selected root still satisfies its exact square identity after
two-adic coefficient extension. -/
theorem twoAdicIdealRoot_square (P : G) :
    invFracBaseChange
        (SexticMumford.mumfordIdealUnit Mℚ
              (N13MumfordFullKummerTwoSurjective.constructedHalfData
                P).representative.toSemi *
          toPrincipalIdeal
            (SexticMumford.CoordinateRing Mℚ)
            (SexticMumford.FunctionField Mℚ)
            (N13MumfordFullKummerTwoSurjective.constructedHalfData
              P).finite.principalCorrection) =
      twoAdicIdealRoot P ^ 2 := by
  rw [(N13MumfordFullKummerTwoSurjective.constructedHalfData
    P).finite.square_eq, map_pow]
  rfl

/-- Base change preserves the exact graph presentation: according to the
retained orientation bit, the selected two-adic root itself or its inverse
is literally the coefficient-extended Padé graph ideal. -/
theorem twoAdicIdealRoot_graph_eq (P : G) :
    (((if inverseOrientation P
        then (twoAdicIdealRoot P)⁻¹
        else twoAdicIdealRoot P) :
      SexticMumford.InvFrac M₂) :
        RationalFractionalIdeal) =
      (twoAdicGraphIdeal P : RationalFractionalIdeal) := by
  have h :=
    congrArg
      (SexticMumford.OrientedBaseChange.fractionalMap
        (M := Mℚ) (M' := M₂)
        N13InfinityBaseChange.ratToQ₂
        N13InfinityBaseChange.ratToQ₂_injective
        (N13InfinityBaseChange.map_n13_f
          N13InfinityBaseChange.ratToQ₂))
      (N13MumfordFullKummerTwoSurjective.constructedHalfData
        P).finite.graph_eq
  by_cases hOrientation :
      (N13MumfordFullKummerTwoSurjective.constructedHalfData
        P).finite.inverseOrientation = true
  · simp only [inverseOrientation, hOrientation, if_pos] at h ⊢
    rw [twoAdicIdealRoot, ← map_inv, invFracBaseChange,
      SexticMumford.OrientedBaseChange.coe_invFracMap]
    simpa only [graphU, graphV, twoAdicGraphIdeal,
      SexticMumford.OrientedBaseChange.fractionalMap_coe_mumfordIdeal]
      using h
  · have hFalse :
        (N13MumfordFullKummerTwoSurjective.constructedHalfData
          P).finite.inverseOrientation = false :=
      Bool.eq_false_of_not_eq_true hOrientation
    simp only [inverseOrientation, hFalse, Bool.false_eq_true,
      if_false] at h ⊢
    simpa only [twoAdicIdealRoot, invFracBaseChange,
      graphU, graphV, twoAdicGraphIdeal,
      Units.coe_map,
      SexticMumford.OrientedBaseChange.coe_invFracMap,
      SexticMumford.OrientedBaseChange.fractionalMap_coe_mumfordIdeal]
      using h

/-- The retained root or inverse is the graph ideal of an actual balanced
Mumford representative over `ℚ₂`, canonically normalized from the Padé
polynomials. -/
theorem twoAdicIdealRoot_normalizedGraph_eq (P : G) :
    (((if inverseOrientation P
        then (twoAdicIdealRoot P)⁻¹
        else twoAdicIdealRoot P) :
      SexticMumford.InvFrac M₂) :
        RationalFractionalIdeal) =
      (SexticMumford.mumfordIdeal M₂
          (twoAdicNormalizedGraphMumford P).u
          (twoAdicNormalizedGraphMumford P).v :
        RationalFractionalIdeal) := by
  rw [twoAdicIdealRoot_graph_eq,
    mumfordIdeal_twoAdicNormalizedGraph_eq]

/-- A degree-zero retained graph gives the trivial selected root after
two-adic coefficient extension. -/
theorem twoAdicIdealRoot_eq_one_of_graphU_natDegree_eq_zero
    (P : G) (hdeg : (graphU P).natDegree = 0) :
    twoAdicIdealRoot P = 1 := by
  have hroot :=
    N13MumfordFullKummerIdentityFiber.FiniteIdealGraphRootData.idealRoot_eq_one_of_graphU_natDegree_eq_zero
        (N13MumfordFullKummerTwoSurjective.constructedHalfData
          P).finite.toFiniteIdealGraphRootData hdeg
  rw [twoAdicIdealRoot, hroot, map_one]

/-- The degree-zero branch has the unit integral spread; it does not need
the general divisorial-hull or special-product-lift construction. -/
def degreeZeroIntegralRootHull :
    N13IntegralFractionalHull.IntegralFractionalIdeal :=
  1

theorem extend_degreeZeroIntegralRootHull
    (P : G) (hdeg : (graphU P).natDegree = 0) :
    N13IntegralFractionalHull.extendFractional
        degreeZeroIntegralRootHull =
      (twoAdicIdealRoot P :
        RationalFractionalIdeal) := by
  rw [twoAdicIdealRoot_eq_one_of_graphU_natDegree_eq_zero
    P hdeg]
  change
    N13IntegralFractionalHull.extendFractional
        (1 :
          N13IntegralFractionalHull.IntegralFractionalIdeal) =
      (1 : RationalFractionalIdeal)
  exact map_one N13IntegralFractionalHull.extendFractional

theorem degreeZeroIntegralRootHull_isUnit :
    IsUnit degreeZeroIntegralRootHull :=
  isUnit_one

/-- The underlying two-adic generic fractional ideal. -/
def rootFractional (P : G) :
    RationalFractionalIdeal :=
  (twoAdicIdealRoot P : RationalFractionalIdeal)

/-- Clear the canonical denominator of the selected generic root.  This is
an ordinary ideal in the two-adic generic affine coordinate ring. -/
def rootIdeal (P : G) : Ideal RationalRing :=
  (rootFractional P).num

/-- Clearing the canonical denominator changes the selected root only by
the displayed principal fractional ideal. -/
theorem span_den_mul_rootFractional (P : G) :
    FractionalIdeal.spanSingleton RationalRing⁰
          (algebraMap RationalRing FunctionField
            ((rootFractional P).den : RationalRing)) *
        rootFractional P =
      (rootIdeal P : RationalFractionalIdeal) := by
  exact
    FractionalIdeal.den_mul_self_eq_num'
      RationalRing⁰ FunctionField (rootFractional P)

theorem rootFractional_isUnit (P : G) :
    IsUnit (rootFractional P) :=
  (twoAdicIdealRoot P).isUnit

private theorem root_den_ne_zero (P : G) :
    algebraMap RationalRing FunctionField
        ((rootFractional P).den : RationalRing) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective RationalRing FunctionField).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp
        (rootFractional P).den.property)

theorem rootIdeal_isUnit (P : G) :
    IsUnit (rootIdeal P : RationalFractionalIdeal) := by
  have hprincipal :
      IsUnit
        (FractionalIdeal.spanSingleton RationalRing⁰
          (algebraMap RationalRing FunctionField
            ((rootFractional P).den : RationalRing))) := by
    apply
      (FractionalIdeal.mul_inv_cancel_iff_isUnit
        FunctionField).mp
    exact
      FractionalIdeal.spanSingleton_mul_inv
        FunctionField (root_den_ne_zero P)
  rw [← span_den_mul_rootFractional P]
  exact hprincipal.mul (rootFractional_isUnit P)

theorem rootIdeal_ne_bot (P : G) :
    rootIdeal P ≠ ⊥ := by
  intro hzero
  have hfrac :
      (rootIdeal P : RationalFractionalIdeal) = 0 := by
    rw [hzero]
    rfl
  exact (rootIdeal_isUnit P).ne_zero hfrac

/-- The canonical integral divisorial spread of the exact constructed
half-root. -/
def integralRootHull (P : G) :
    N13IntegralFractionalHull.IntegralFractionalIdeal :=
  N13IntegralFractionalHull.divisorialHull (rootIdeal P)

/-- Its generic fibre is the denominator-cleared selected root. -/
theorem extend_integralRootHull (P : G) :
    N13IntegralFractionalHull.extendFractional
        (integralRootHull P) =
      (rootIdeal P : RationalFractionalIdeal) :=
  N13IntegralFractionalHull.extendFractional_divisorialHull_eq
    (rootIdeal_ne_bot P) (rootIdeal_isUnit P)

/-- Equivalently, the generic fibre is the actual Padé-selected root
multiplied by its explicit principal denominator. -/
theorem extend_integralRootHull_eq_principal_mul (P : G) :
    N13IntegralFractionalHull.extendFractional
        (integralRootHull P) =
      FractionalIdeal.spanSingleton RationalRing⁰
          (algebraMap RationalRing FunctionField
            ((rootFractional P).den : RationalRing)) *
        rootFractional P := by
  rw [extend_integralRootHull, span_den_mul_rootFractional]

/-- The remaining special-fibre obligation for this exact constructed
half: lift the three explicit special trace products into the contracted
root and its multiplier inverse. -/
abbrev SpecialProductLift (P : G) : Type :=
  N13SpecialProductLift.Data (rootIdeal P)

/-- That single special trace lift makes the integral spread invertible. -/
theorem integralRootHull_isUnit
    (P : G) (D : SpecialProductLift P) :
    IsUnit (integralRootHull P) :=
  D.isUnit_divisorialHull
    (rootIdeal_ne_bot P) (rootIdeal_isUnit P)

end

end MazurProof.N13ConstructedHalfIntegralSpread


