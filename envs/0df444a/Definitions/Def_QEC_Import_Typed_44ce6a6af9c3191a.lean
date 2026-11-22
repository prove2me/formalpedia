-- Prove2me | Definitions.Def_QEC_Import_Typed_44ce6a6af9c3191a
-- name    : QEC_Import_Typed_44ce6a6af9c3191a
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:56:58.052807+00:00
-- url     : https://prove2.me/theorems/296fa8a3-85a2-4a6e-b597-b9f030508109
-- title:
--   Exact source statement: BPTCommuting Projector Model: second Cut Qright ne zero of nonzero code active block
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L154-L229

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
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
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_ne_zero_of_nonzero_code_active_block_QECertTypedStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region)
    (hleft :
      (unitaryLTensor (M.fourFactorA region) U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
        rightTensorExtensionAfterLeft (M.fourFactorA region)
          (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft)
    (hright :
      (unitaryRTensor U
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} n)
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright),
    Qright ≠ 0


