-- Prove2me | Definitions.Def_HuangN13_GaussianUnitLogCore
-- name    : HuangN13_GaussianUnitLogCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:36:35.299704+00:00
-- url     : https://prove2.me/theorems/e11ccd05-ee20-490b-bda7-41b839181a0e
-- title:
--   Global ramified logarithm on the N13 Gaussian order
-- statement:
--   The global maximal-order reduction to the first ramified dual-number quotient, its induced additive unit logarithm, and the named word for three binary unit exponents. The maps and word retain their original source definitions.
-- source:
--   Xiang Huang, Apache-2.0. FLT@51bbb4f191ad0d3753b87123635c100a638ae580; exact unit4/unit6 declaration ranges and hashes in metadata.json. These are the original map and named-word definitions and their necessary short support proofs.

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianGlobalReductionTwo_shiftedTheta_root_h
import Theorems.Thm_MazurProof_N13GaussianNamedUnitSquareclasses_relativeZeta_sq

set_option autoImplicit false

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
/-- The power basis on the generated Gaussian order, transported to the
proved relative integral closure. -/
def relativeIntegralPowerBasis :
    PowerBasis GI (integralClosure GI L) :=
  (Algebra.adjoin.powerBasis' (R := GI) alpha_integral).map
    (Subalgebra.equivOfEq _ _
      integralClosure_eq_adjoin.symm)
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
@[simp] theorem coe_relativeIntegralPowerBasis_gen :
    ((relativeIntegralPowerBasis.gen :
        integralClosure GI L) : L) = alpha := by
  simp [relativeIntegralPowerBasis]
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianGlobalReductionTwo.fieldL
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
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder
def relativeToOrderAlgHom : RelativeO →ₐ[GI] Order :=
  N13GaussianCubicField.relativeIntegralPowerBasis.lift
    (N13GaussianOrderTwo.theta - 9)
    (by
      rw [minpoly_relative_gen]
      exact shiftedTheta_root_h)
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder
def relativeToOrder : RelativeO →+* Order :=
  relativeToOrderAlgHom.toRingHom
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianGlobalReductionTwo.fieldL
/-- The unshifted sextic root inside the relative maximal order. -/
def relativeTheta : RelativeO :=
  N13GaussianCubicField.relativeIntegralPowerBasis.gen + 9
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
/-- The global maximal order maps to the fixed integral Gaussian order
used by the first ramified reduction. -/
def ringOfIntegersToOrder : O →+* Order :=
  relativeToOrder.comp
    relativeToRingOfIntegers.symm.toRingHom
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
/-- Genuine reduction of the full global maximal order to the dual-number
first jet at the ramified prime over two. -/
def globalReduction : O →+* DualNumber F8 :=
  N13GaussianOrderTwo.reduction.comp
    ringOfIntegersToOrder
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def relativeE1 : RelativeO :=
  1 - relativeTheta ^ 2 +
    (relativeZeta - 1) * relativeTheta
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def relativeE2 : RelativeO :=
  1 + relativeZeta * relativeTheta ^ 2 +
    (1 + 2 * relativeZeta) * relativeTheta
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def relativeE1Inv : RelativeO :=
  1 + relativeZeta + relativeZeta * relativeTheta
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def relativeE2Inv : RelativeO :=
  -relativeZeta * relativeTheta ^ 2 -
    (2 + 2 * relativeZeta) * relativeTheta -
    1 + relativeZeta
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- The translated relative power-basis generator satisfies the displayed
Gaussian cubic already inside the relative maximal order. -/
theorem relativeTheta_gaussian_cubic :
    relativeTheta ^ 3 + 2 * relativeTheta ^ 2 -
        relativeTheta - 1 -
      relativeZeta *
        (2 * relativeTheta * (relativeTheta + 1)) = 0 := by
  have hroot :
      aeval
          N13GaussianCubicField.relativeIntegralPowerBasis.gen
          N13GaussianGlobalArithmetic.h = 0 := by
    rw [← minpoly_relative_gen]
    exact minpoly.aeval GI
      N13GaussianCubicField.relativeIntegralPowerBasis.gen
  rw [N13GaussianGlobalArithmetic.h, aeval_def,
    eval₂_comp] at hroot
  have hinner :
      eval₂ (algebraMap GI RelativeO)
          N13GaussianCubicField.relativeIntegralPowerBasis.gen
          (Polynomial.X + Polynomial.C 9) =
        relativeTheta := by
    simp only [eval₂_add, eval₂_X, eval₂_C]
    change
      N13GaussianCubicField.relativeIntegralPowerBasis.gen +
          algebraMap GI RelativeO (9 : GI) =
        N13GaussianCubicField.relativeIntegralPowerBasis.gen + 9
    congr 1
    exact map_natCast (algebraMap GI RelativeO) 9
  rw [hinner] at hroot
  simp only [N13GaussianGlobalArithmetic.g,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, eval₂_one, eval₂_ofNat,
    eval₂_neg, map_ofNat, map_one, map_neg, map_sub,
    map_mul] at hroot
  change
    relativeTheta ^ 3 +
        (2 - 2 * relativeZeta) * relativeTheta ^ 2 +
        (-1 - 2 * relativeZeta) * relativeTheta - 1 = 0
    at hroot
  linear_combination hroot
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
theorem relativeE1_mul_inv :
    relativeE1 * relativeE1Inv = 1 := by
  simp only [relativeE1, relativeE1Inv]
  rw [← sub_eq_zero]
  calc
    (1 - relativeTheta ^ 2 +
          (relativeZeta - 1) * relativeTheta) *
          (1 + relativeZeta +
            relativeZeta * relativeTheta) - 1 =
      -relativeZeta *
        (relativeTheta ^ 3 + 2 * relativeTheta ^ 2 -
          relativeTheta - 1 -
          relativeZeta *
            (2 * relativeTheta * (relativeTheta + 1))) := by
        ring_nf
        rw [relativeZeta_sq]
        ring
    _ = 0 := by
      rw [relativeTheta_gaussian_cubic, mul_zero]
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
theorem relativeE2_mul_inv :
    relativeE2 * relativeE2Inv = 1 := by
  simp only [relativeE2, relativeE2Inv]
  rw [← sub_eq_zero]
  calc
    (1 + relativeZeta * relativeTheta ^ 2 +
          (1 + 2 * relativeZeta) * relativeTheta) *
          (-relativeZeta * relativeTheta ^ 2 -
            (2 + 2 * relativeZeta) * relativeTheta -
            1 + relativeZeta) - 1 =
      (relativeTheta + 2 - relativeZeta) *
        (relativeTheta ^ 3 + 2 * relativeTheta ^ 2 -
          relativeTheta - 1 -
          relativeZeta *
            (2 * relativeTheta * (relativeTheta + 1))) := by
        ring_nf
        rw [relativeZeta_sq]
        ring
    _ = 0 := by
      rw [relativeTheta_gaussian_cubic, mul_zero]
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
def relativeE1Unit : RelativeOˣ where
  val := relativeE1
  inv := relativeE1Inv
  val_inv := relativeE1_mul_inv
  inv_val := by
    rw [mul_comm]
    exact relativeE1_mul_inv
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
def relativeE2Unit : RelativeOˣ where
  val := relativeE2
  inv := relativeE2Inv
  val_inv := relativeE2_mul_inv
  inv_val := by
    rw [mul_comm]
    exact relativeE2_mul_inv
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def e1Unit : Oˣ :=
  Units.map relativeToRingOfIntegers.toMonoidHom
    relativeE1Unit
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def e2Unit : Oˣ :=
  Units.map relativeToRingOfIntegers.toMonoidHom
    relativeE2Unit
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def globalDlogHom : Oˣ →* Multiplicative F8 :=
  RamifiedDlog.dlogHom.comp
    (Units.map globalReduction.toMonoidHom)
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
def globalDlogAdd : Additive Oˣ →+ F8 :=
  globalDlogHom.toAdditiveLeft
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- The named representative attached to three binary exponents. -/
def namedWord (c : Exp3) : Oˣ :=
  zetaUnit ^ c.1.val *
    e1Unit ^ c.2.1.val *
    e2Unit ^ c.2.2.val
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end


