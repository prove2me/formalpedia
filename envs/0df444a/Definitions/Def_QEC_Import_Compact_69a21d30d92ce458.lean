-- Prove2me | Definitions.Def_QEC_Import_Compact_69a21d30d92ce458
-- name    : QEC_Import_Compact_69a21d30d92ce458
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:12:01.923891+00:00
-- url     : https://prove2.me/theorems/606ba8ad-712a-4d3f-b6de-149301c985b3
-- title:
--   Exact source statement: BPTCommuting Projector Model: first Cut compressed overlap block product
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FirstCutBlock.lean#L31-L68

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressed_overlap_block_product_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)),
let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let D := M.fourFactorD region
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem AB W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N D)),
      (unitaryLTensor AB U).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) component) =
          rightTensorExtensionAfterLeft AB W0 N Pleft →
      (unitaryRTensor U D).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component) =
          leftTensorExtensionBeforeRight W0 N D Qright →
      (isotypicSectorBlockTransportLeft AB H W0 N D U).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := AB) (C := D) H)).comp
            ((M.firstCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding (A := AB) (C := D) H))) =
        TensorProduct.map Pleft Qright


