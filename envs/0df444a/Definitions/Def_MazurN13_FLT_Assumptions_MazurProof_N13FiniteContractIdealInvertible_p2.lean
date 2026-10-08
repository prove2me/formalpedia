-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p2
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p2
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T07:14:21.146589+00:00
-- url     : https://prove2.me/theorems/72a9bb9f-1b4e-4e16-843d-818bb9b1b294
-- title:
--   FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ContractQuotientXYBasis_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoSemiGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13VerticalGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p1

set_option autoImplicit false

open Module
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteContractIdealInvertible
noncomputable section
attribute [local instance] _root_.MazurProof.N13FiniteContractIdealInvertible.instFactPrimeOfNatNat_fLT
attribute [local instance] _root_.MazurProof.N13FiniteContractIdealInvertible.integralRingDomain
attribute [local instance] _root_.MazurProof.N13FiniteContractIdealInvertible.integralRationalAlgebra
attribute [local instance] _root_.MazurProof.N13FiniteContractIdealInvertible.integralFunctionFieldFractionRing
/-- A finite quadratic contraction therefore has an invertible canonical
divisorial hull. -/
theorem divisorialHull_graphIdeal_isUnit_of_finite_quadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D)) := by
  have hI :=
    contractIdeal_isUnit_of_finite_quadratic D hdeg hfinite
  rw [N13IntegralFractionalHull.divisorialHull]
  have hmul :
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) *
          ((N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D) :
            Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹ =
        1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      FunctionField).mpr hI
  have hinvinv :
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹⁻¹ =
        ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) :=
    (FractionalIdeal.right_inverse_eq
      FunctionField
      (((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹)
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)
      (by simpa [mul_comm] using hmul)).symm
  change
    IsUnit
      (((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹⁻¹)
  rw [hinvinv]
  exact hI

end

end MazurProof.N13FiniteContractIdealInvertible


