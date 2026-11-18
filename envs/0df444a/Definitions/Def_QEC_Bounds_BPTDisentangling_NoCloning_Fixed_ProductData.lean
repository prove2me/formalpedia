-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductData
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:22:12.225612+00:00
-- url     : https://prove2.me/theorems/7b68bc33-cc84-417d-bfb3-e8b19b45fc6a
-- title:
--   Product Data
-- statement:
--   Definitions and structural lemmas for Product Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/ProductData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCoreData
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
/-- Exact four-factor reconstruction equation for the selected joint sector. -/
inductive FixedActiveFourFactorReconstruction
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Prop where
  | intro
    (equation :
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector =
        (fourFactorJointBCSectorEmbedding
          (A := M.fourFactorA region) (D := M.fourFactorD region)
          (bcomponent.1.restrictScalars Complex)
          (ccomponent.1.restrictScalars Complex)).comp
          (((LinearMap.adjoint (fourFactorJointBCSectorEmbedding
            (A := M.fourFactorA region) (D := M.fourFactorD region)
            (bcomponent.1.restrictScalars Complex)
            (ccomponent.1.restrictScalars Complex))).comp
            (((M.fourFactorTransport region).conjOperator M.fullCodeProjector).comp
              (fourFactorJointBCSectorEmbedding
                (A := M.fourFactorA region) (D := M.fourFactorD region)
                (bcomponent.1.restrictScalars Complex)
                (ccomponent.1.restrictScalars Complex)))).comp
            (LinearMap.adjoint (fourFactorJointBCSectorEmbedding
              (A := M.fourFactorA region) (D := M.fourFactorD region)
              (bcomponent.1.restrictScalars Complex)
              (ccomponent.1.restrictScalars Complex))))) :
    FixedActiveFourFactorReconstruction M region bcomponent ccomponent
set_option maxHeartbeats 1800000 in
/-- Exact D5 witness package assembled from its independently cacheable proof blocks. -/
inductive FixedActiveDataProductRankOneTensor
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
    (core : M.FixedActiveDataProductCore
      region bcomponent ccomponent WB WC UB UC P_D Qsecond)
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region)
    (reconstruction : M.FixedActiveFourFactorReconstruction
      region bcomponent ccomponent) :
    FixedActiveDataProductRankOneTensor
      M region bcomponent ccomponent WB WC UB UC P_D Qsecond
end BPTCommutingProjectorModel
end Bounds
end QEC


