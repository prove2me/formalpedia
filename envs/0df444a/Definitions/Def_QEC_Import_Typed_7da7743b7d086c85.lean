-- Prove2me | Definitions.Def_QEC_Import_Typed_7da7743b7d086c85
-- name    : QEC_Import_Typed_7da7743b7d086c85
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:52:08.721955+00:00
-- url     : https://prove2.me/theorems/d6b1cfc2-7edb-437a-9c07-4aa175f80537
-- title:
--   Exact source statement: BPTCommuting Projector Model: four Factor Transport comp active Region Embeddings Core
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/Embeddings.lean#L229-L283

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_comp_activeRegionEmbeddingsCore_QECertTypedStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
        (isotypicLiftedMultiplicity.{0} nC))),
(M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)) =
      (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
        (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
        (ccomponent.1.restrictScalars Complex)).comp
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
            (productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap))


