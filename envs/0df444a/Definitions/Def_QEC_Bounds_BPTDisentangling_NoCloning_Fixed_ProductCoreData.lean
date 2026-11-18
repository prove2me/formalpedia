-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCoreData
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCoreData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:19:33.519879+00:00
-- url     : https://prove2.me/theorems/8da0eb82-9b75-44b1-94f5-b8c0f3f7bed4
-- title:
--   Product Core Data
-- statement:
--   Definitions and structural lemmas for Product Core Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/ProductCoreData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Residual
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
/-- Exact fixed-data product block before four-factor reconstruction is attached. -/
inductive FixedActiveDataProductCore
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
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop where
  | intro
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (eta : Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region))
    (psi : Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
      (WC.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (hphi : ‖phi‖ = 1)
    (hP_D : P_D.IsSymmetricProjection)
    (hP_D0 : P_D ≠ 0)
    (heta : ‖eta‖ = 1)
    (hPeta : P_D eta = eta)
    (hpsi : ‖psi‖ = 1)
    (hn0 : ‖n0‖ = 1)
    (hc0 : ‖c0‖ = 1)
    (hU : U psi = n0 ⊗ₜ[Complex] c0)
    (hjoint :
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
            (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)))
    (hproduct :
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).conjOperator
          ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm.conjOperator
            (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)) =
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB)
                (WC.restrictScalars Complex))).toLinearMap P_D) :
    FixedActiveDataProductCore M region bcomponent ccomponent WB WC UB UC P_D Qsecond
end BPTCommutingProjectorModel
end Bounds
end QEC


