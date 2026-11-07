-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ResidualData
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ResidualData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:50:36.619452+00:00
-- url     : https://prove2.me/theorems/7fc15ef7-8315-4ecb-9cc8-45e2c22a138d
-- title:
--   Residual Data
-- statement:
--   Definitions and structural lemmas for Residual Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/ResidualData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ResidualContract
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Regrouping
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000 in
/-- One common-factor witness together with the exact complementary projection data. -/
def FixedActiveCommonFactorizationData
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∃ (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (eta : Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)),
    ‖phi‖ = 1 ∧ P_D.IsSymmetricProjection ∧ P_D ≠ 0 ∧ ‖eta‖ = 1 ∧ P_D eta = eta ∧
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
        (M.secondCutJointCompression region
          (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex)) =
      (unitaryLTensor
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm).conjOperator
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)) ∧
    (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
      (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))).symm.conjOperator
        (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) =
      TensorProduct.map
        (leftTensorCompression phi
          (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
            (WC.restrictScalars Complex) Pfirst)) P_D
set_option maxHeartbeats 1800000 in
/-- Exact projection and two-sided scalar-compression facts on the active residual block. -/
def FixedActiveRegroupedCompressionData
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  LinearMap.IsSymmetricProjection
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) ∧
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond ≠ 0 ∧
    RegroupedTwoFactorScalarCompressions
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)
end BPTCommutingProjectorModel
end Bounds
end QEC


