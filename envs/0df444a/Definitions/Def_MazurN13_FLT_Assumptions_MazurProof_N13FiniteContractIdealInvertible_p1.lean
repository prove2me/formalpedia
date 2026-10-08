-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p1
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T07:13:25.150995+00:00
-- url     : https://prove2.me/theorems/9631460e-035b-435b-b934-d8b686aed29d
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
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p0

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
theorem contractIdeal_isUnit_of_finite_quadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    IsUnit
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) := by
  rcases
      N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
        D hdeg hfinite with hx | hy
  · obtain ⟨b, hb⟩ := hx
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13TwoFiberNoEscape.pairFamily
            1
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13CanonicalContractionQuotient.integralX) := by
      simpa [N13FiniteFlatBasisLift.oneX,
        N13TwoFiberNoEscape.pairFamily] using hb
    obtain ⟨E, _, hI⟩ :=
      N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
        D b hb'
    rw [hI]
    exact N13IntegralGraphJacobian.mumfordIdeal_isUnit E
  · obtain ⟨b, hb⟩ := hy
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13FiniteFlatBasisLift.oneX
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13ConcreteGraphRecovery.integralY) := by
      simpa [N13ContractQuotientXYBasis.integralY,
        N13ConcreteGraphRecovery.integralY] using hb
    obtain ⟨E, _, hI⟩ :=
      N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
        D b hb'
    rw [hI]
    exact N13VerticalGraphJacobian.verticalIdeal_isUnit E


end
end MazurProof.N13FiniteContractIdealInvertible


