-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T07:08:57.242613+00:00
-- url     : https://prove2.me/theorems/960fbe84-6620-4ec0-984b-8f772654fad4
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

set_option autoImplicit false




open Module
open Polynomial
open scoped nonZeroDivisors

/-!
# Invertibility of finite quadratic N13 contractions

A finite quadratic contraction admits a literal integral basis `{1,x}` or
`{1,y}`.  The first basis recovers a horizontal integral semigraph; the
second recovers a vertical graph.  The two structural Jacobian frames prove
invertibility in the respective cases.
-/

namespace MazurProof.N13FiniteContractIdealInvertible

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type := N13IntegralGraphJacobian.FunctionField
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
abbrev Model : SexticMumford.Model N13IntegralModelContraction.Q₂ :=
  N13GoodSexticCoordinateEquiv.M

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing


end
end MazurProof.N13FiniteContractIdealInvertible


