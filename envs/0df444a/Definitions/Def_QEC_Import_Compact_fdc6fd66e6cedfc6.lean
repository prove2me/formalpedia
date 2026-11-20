-- Prove2me | Definitions.Def_QEC_Import_Compact_fdc6fd66e6cedfc6
-- name    : QEC_Import_Compact_fdc6fd66e6cedfc6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:11:51.543919+00:00
-- url     : https://prove2.me/theorems/31b8c218-1241-42d0-a5f8-9fcfd051eee5
-- title:
--   Exact source statement: BPTCommuting Projector Model: second Cut compressed overlap block product
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Compression.lean#L30-L68

import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Compression
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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_block_product_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)),
let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      (isotypicSectorBlockTransportLeft A H W0 N CD U).conjOperator
          ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := CD) H)).comp
            ((M.secondCutCodeLift region).comp
              (tensorTripleSubtypeEmbedding (A := A) (C := CD) H))) =
        TensorProduct.map Pleft Qright


