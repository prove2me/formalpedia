-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:29:52.311985+00:00
-- url     : https://prove2.me/theorems/52397fe6-ac8c-4b36-b050-ba89823007d5
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralGraphSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralGraphSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralGraphSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphContraction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphJacobian_p0

set_option autoImplicit false




/-!
# Invertible integral spreads of N13 Mumford graphs

A smooth integral generalized Mumford graph already gives an invertible
fractional ideal on the integral affine model: this is the explicit global
Jacobian dual-frame theorem.  Exact graph contraction then identifies the
canonical contraction of its generic sextic graph with that same integral
ideal.

Consequently the divisorial-hull construction makes no change at all on an
integral graph.  This is the representative-level adapter needed by the
proper-spread construction; it uses neither local factoriality nor a special
fibre classification.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralGraphSpread

noncomputable section

abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev SmoothMumford₂ : Type :=
  N13IntegralGraphContraction.SmoothMumford₂

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- Exact contraction of a smooth integral graph is already an invertible
fractional ideal on the integral affine model. -/
theorem contractedFractional_sexticIdeal_isUnit
    (D : SmoothMumford₂) (nInf : ℤ) :
    IsUnit
      (N13IntegralFractionalHull.contractedFractional
        (N13IntegralGraphContraction.sexticIdeal D nInf)) := by
  rw [N13IntegralGraphContraction.contractedFractional_sexticIdeal]
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford

/-- Double multiplier inverse fixes an invertible integral fractional
ideal. -/
private theorem inv_inv_eq_of_isUnit
    {I : IntegralFractionalIdeal} (hI : IsUnit I) :
    I⁻¹⁻¹ = I := by
  have hmul : I * I⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      FunctionField).mpr hI
  exact
    (FractionalIdeal.right_inverse_eq
      FunctionField I⁻¹ I
        (by simpa [mul_comm] using hmul)).symm

/-- Any canonical contraction that is already an invertible ordinary
integral ideal has invertible divisorial hull. -/
theorem divisorialHull_isUnit_of_contractIdeal_eq_isUnit
    (J : Ideal RationalRing)
    (I : Ideal IntegralRing)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J = I)
    (hunit : IsUnit (I : IntegralFractionalIdeal)) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralFractionalHull.contractedFractional, hcontract,
    inv_inv_eq_of_isUnit hunit]
  exact hunit

/-- Exact recovery as any integral generalized Mumford semigraph already
identifies the divisorial hull with that graph ideal.  The stronger
vertical Bézout field of `SmoothMumford₂` is not needed here because the
global curve Jacobian supplies the dual frame. -/
theorem divisorialHull_eq_semiGraphIdeal_of_contractIdeal_eq
    (J : Ideal RationalRing)
    (D : SemiMumford₂)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J =
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) :
    N13IntegralFractionalHull.divisorialHull J =
      (N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v :
        IntegralFractionalIdeal) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralFractionalHull.contractedFractional,
    hcontract]
  exact inv_inv_eq_of_isUnit
    (N13IntegralGraphJacobian.mumfordIdeal_isUnit D)

/-- Hence a recovered integral semigraph makes the canonical divisorial
spread invertible without any special-fibre frame. -/
theorem divisorialHull_isUnit_of_contractIdeal_eq_semiGraph
    (J : Ideal RationalRing)
    (D : SemiMumford₂)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J =
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) := by
  rw [divisorialHull_eq_semiGraphIdeal_of_contractIdeal_eq
    J D hcontract]
  exact N13IntegralGraphJacobian.mumfordIdeal_isUnit D

/-- Any generic ideal whose canonical contraction is an integral graph has
that graph itself as its divisorial hull. -/
theorem divisorialHull_eq_graphIdeal_of_contractIdeal_eq
    (J : Ideal RationalRing)
    (D : SmoothMumford₂)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J =
        N13IntegralGraphContraction.graphIdeal D) :
    N13IntegralFractionalHull.divisorialHull J =
      (N13IntegralGraphContraction.graphIdeal D :
        IntegralFractionalIdeal) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralFractionalHull.contractedFractional,
    hcontract]
  exact inv_inv_eq_of_isUnit
    (N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford)

/-- Thus exact recovery of an integral graph is already enough to prove
invertibility of the canonical divisorial spread. -/
theorem divisorialHull_isUnit_of_contractIdeal_eq
    (J : Ideal RationalRing)
    (D : SmoothMumford₂)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J =
        N13IntegralGraphContraction.graphIdeal D) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) := by
  rw [divisorialHull_eq_graphIdeal_of_contractIdeal_eq J D hcontract]
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford

/-- The divisorial hull of the canonical contraction of an integral graph
is literally the original integral graph fractional ideal. -/
theorem divisorialHull_sexticIdeal_eq_graphIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    N13IntegralFractionalHull.divisorialHull
        (N13IntegralGraphContraction.sexticIdeal D nInf) =
      (N13IntegralGraphContraction.graphIdeal D :
        IntegralFractionalIdeal) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralGraphContraction.contractedFractional_sexticIdeal]
  exact inv_inv_eq_of_isUnit
    (N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford)

/-- Every smooth integral Mumford graph therefore supplies an actual
invertible integral spread of its generic sextic graph. -/
theorem divisorialHull_sexticIdeal_isUnit
    (D : SmoothMumford₂) (nInf : ℤ) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13IntegralGraphContraction.sexticIdeal D nInf)) := by
  rw [divisorialHull_sexticIdeal_eq_graphIdeal]
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford

/-- The divisorial hull of a transported integral semigraph is literally
its original integral graph fractional ideal. -/
theorem divisorialHull_sexticSemiIdeal_eq_semiGraphIdeal
    (D : SemiMumford₂) (nInf : ℤ) :
    N13IntegralFractionalHull.divisorialHull
        (N13IntegralGraphContraction.sexticSemiIdeal D nInf) =
      (N13IntegralGraphContraction.semiGraphIdeal D :
        IntegralFractionalIdeal) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralGraphContraction.contractedFractional_sexticSemiIdeal]
  exact inv_inv_eq_of_isUnit
    (N13IntegralGraphJacobian.mumfordIdeal_isUnit D)

/-- Thus every integral generalized Mumford semigraph, without an extra
vertical smoothness field, supplies an invertible integral spread. -/
theorem divisorialHull_sexticSemiIdeal_isUnit
    (D : SemiMumford₂) (nInf : ℤ) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13IntegralGraphContraction.sexticSemiIdeal D nInf)) := by
  rw [divisorialHull_sexticSemiIdeal_eq_semiGraphIdeal]
  exact N13IntegralGraphJacobian.mumfordIdeal_isUnit D

end

end MazurProof.N13IntegralGraphSpread


