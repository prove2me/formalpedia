-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalReductionTwo_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalReductionTwo_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:25:48.948991+00:00
-- url     : https://prove2.me/theorems/a916a259-ddf9-4ffa-aefd-6f087cdb4e0f
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianOrderTwo_p0

set_option autoImplicit false




/-!
# Global N13 integers in the first ramified quotient at two

The relative maximal order is monogenic over the Gaussian integers.  Its
power-basis universal property therefore maps the full global maximal order
to the fixed integral Gaussian order used at two:

* the Gaussian generator maps to the local generator `i`;
* the translated cubic generator maps to `theta - 9`.

Composing with the exact quotient map gives a genuine ring homomorphism from
the full ring of integers to `F₈[ε]/(ε²)`.  Thus later logarithmic detectors
act on every global unit, rather than only on a displayed list of elements.
-/

open Polynomial

namespace MazurProof.N13GaussianGlobalReductionTwo

noncomputable section

open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo

abbrev L := N13GaussianCubicField.L

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L

local instance intAlgebraGI : Algebra ℤ GI :=
  Ring.toIntAlgebra GI

abbrev RelativeO := integralClosure GI L
abbrev O := NumberField.RingOfIntegers L
abbrev Order := N13GaussianOrderTwo.Order
abbrev F8 := N13LocalDlogTwo.F8

local instance intAlgebraRelativeO : Algebra ℤ RelativeO :=
  Ring.toIntAlgebra RelativeO

local instance intAlgebraAbsoluteO :
    Algebra ℤ (integralClosure ℤ L) :=
  Ring.toIntAlgebra (integralClosure ℤ L)

def giToOrder : GI →+* Order :=
  Zsqrtd.lift
    ⟨N13GaussianOrderTwo.i, by
      calc
        N13GaussianOrderTwo.i *
            N13GaussianOrderTwo.i =
          (-1 : Order) := by
            simpa only [pow_two] using
              N13GaussianOrderTwo.i_sq
        _ = ((-1 : ℤ) : Order) := by norm_num⟩

@[simp] theorem giToOrder_i :
    giToOrder N13GaussianGlobalArithmetic.i =
      N13GaussianOrderTwo.i := by
  simp [giToOrder, N13GaussianGlobalArithmetic.i]

local instance giAlgebraOrder : Algebra GI Order :=
  giToOrder.toAlgebra

@[simp] theorem algebraMap_gi_i :
    algebraMap GI Order N13GaussianGlobalArithmetic.i =
      N13GaussianOrderTwo.i :=
  giToOrder_i

theorem shiftedTheta_root_h :
    aeval
        (N13GaussianOrderTwo.theta - 9 : Order)
        N13GaussianGlobalArithmetic.h = 0 := by
  rw [N13GaussianGlobalArithmetic.h, aeval_def,
    eval₂_comp]
  have hinner :
      eval₂ (algebraMap GI Order)
          (N13GaussianOrderTwo.theta - 9)
          (X + C 9) =
        N13GaussianOrderTwo.theta := by
    simp only [eval₂_add, eval₂_X, eval₂_C]
    change
      N13GaussianOrderTwo.theta - 9 +
          giToOrder (9 : GI) =
        N13GaussianOrderTwo.theta
    simp [giToOrder]
  rw [hinner]
  simp only [N13GaussianGlobalArithmetic.g,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, eval₂_one, eval₂_ofNat,
    eval₂_neg, map_ofNat, map_one, map_neg, map_sub, map_mul,
    algebraMap_gi_i]
  linear_combination
    N13GaussianOrderTwo.theta_gaussian_cubic

theorem minpoly_relative_gen :
    minpoly GI
        N13GaussianCubicField.relativeIntegralPowerBasis.gen =
      N13GaussianGlobalArithmetic.h := by
  have hgen :
      algebraMap RelativeO L
          N13GaussianCubicField.relativeIntegralPowerBasis.gen =
        N13GaussianCubicField.alpha := by
    change
      ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
          RelativeO) : L) =
        N13GaussianCubicField.alpha
    exact
      N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen
  calc
    minpoly GI
          N13GaussianCubicField.relativeIntegralPowerBasis.gen =
        minpoly GI
          (algebraMap RelativeO L
            N13GaussianCubicField.relativeIntegralPowerBasis.gen) :=
      (minpoly.algHom_eq
        (IsScalarTower.toAlgHom GI RelativeO L)
        (by
          intro x y hxy
          exact Subtype.ext hxy)
        N13GaussianCubicField.relativeIntegralPowerBasis.gen).symm
    _ = minpoly GI N13GaussianCubicField.alpha := by
      rw [hgen]
    _ = N13GaussianGlobalArithmetic.h :=
      N13GaussianCubicField.minpoly_alpha

def relativeToOrderAlgHom : RelativeO →ₐ[GI] Order :=
  N13GaussianCubicField.relativeIntegralPowerBasis.lift
    (N13GaussianOrderTwo.theta - 9)
    (by
      rw [minpoly_relative_gen]
      exact shiftedTheta_root_h)

def relativeToOrder : RelativeO →+* Order :=
  relativeToOrderAlgHom.toRingHom

@[simp] theorem relativeToOrder_gen :
    relativeToOrder
        N13GaussianCubicField.relativeIntegralPowerBasis.gen =
      N13GaussianOrderTwo.theta - 9 := by
  exact PowerBasis.lift_gen
    N13GaussianCubicField.relativeIntegralPowerBasis
    (N13GaussianOrderTwo.theta - 9)
    _

/-- The unshifted sextic root inside the relative maximal order. -/
def relativeTheta : RelativeO :=
  N13GaussianCubicField.relativeIntegralPowerBasis.gen + 9

/-- The Gaussian unit inside the relative maximal order. -/
def relativeI : RelativeO :=
  algebraMap GI RelativeO N13GaussianGlobalArithmetic.i

@[simp] theorem relativeToOrder_theta :
    relativeToOrder relativeTheta =
      N13GaussianOrderTwo.theta := by
  rw [relativeTheta, map_add, relativeToOrder_gen]
  have h9 :
      relativeToOrder (9 : RelativeO) =
        (9 : Order) := by
    exact map_natCast relativeToOrder 9
  rw [h9]
  ring

@[simp] theorem relativeToOrder_i :
    relativeToOrder relativeI =
      N13GaussianOrderTwo.i := by
  exact (relativeToOrderAlgHom.commutes
    N13GaussianGlobalArithmetic.i).trans
      algebraMap_gi_i

/-- Carrier-preserving identification of the relative integral closure
with Mathlib's absolute ring of integers. -/
def relativeToRingOfIntegers :
    RelativeO ≃+* O :=
  N13GaussianNumberField.relativeToAbsoluteAlgEquiv.toRingEquiv.trans
    N13GaussianNumberField.integralClosureToRingOfIntegersRingEquiv

/-- The global maximal order maps to the fixed integral Gaussian order
used by the first ramified reduction. -/
def ringOfIntegersToOrder : O →+* Order :=
  relativeToOrder.comp
    relativeToRingOfIntegers.symm.toRingHom

@[simp] theorem ringOfIntegersToOrder_relative
    (x : RelativeO) :
    ringOfIntegersToOrder (relativeToRingOfIntegers x) =
      relativeToOrder x := by
  simp [ringOfIntegersToOrder, relativeToRingOfIntegers]

/-- Genuine reduction of the full global maximal order to the dual-number
first jet at the ramified prime over two. -/
def globalReduction : O →+* DualNumber F8 :=
  N13GaussianOrderTwo.reduction.comp
    ringOfIntegersToOrder

@[simp] theorem globalReduction_relative
    (x : RelativeO) :
    globalReduction (relativeToRingOfIntegers x) =
      N13GaussianOrderTwo.reduction (relativeToOrder x) := by
  simp [globalReduction]

@[simp] theorem globalReduction_theta :
    globalReduction
        (relativeToRingOfIntegers relativeTheta) =
      N13LocalDlogRegimes.thetaDual := by
  simp

@[simp] theorem globalReduction_i :
    globalReduction
        (relativeToRingOfIntegers relativeI) =
      N13LocalDlogRegimes.gaussianIDual := by
  simp

end

end MazurProof.N13GaussianGlobalReductionTwo


