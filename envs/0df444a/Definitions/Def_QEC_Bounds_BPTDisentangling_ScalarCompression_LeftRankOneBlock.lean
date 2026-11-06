-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:49:58.536483+00:00
-- url     : https://prove2.me/theorems/3bf41840-6d0b-43b3-a06f-80f49745c447
-- title:
--   Left Rank One Block
-- statement:
--   Definitions and structural lemmas for Left Rank One Block, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneBlock.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneWitness
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000 in
/-- The three physical second-cut equations consumed by the rank-one block theorem. -/
def SecondCutActiveBlockConditions
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region ∧
    (unitaryLTensor (M.fourFactorA region) U).conjOperator
        (overlapProjectorOnIsotypicComponent
          (M.fourFactorProjectorABLocal region) component) =
      rightTensorExtensionAfterLeft (M.fourFactorA region)
        (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} n) Pleft ∧
    (unitaryRTensor U
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
        (overlapRightProjectorOnIsotypicComponent
          (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
          component) =
      leftTensorExtensionBeforeRight (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Qright
set_option maxHeartbeats 800000 in
/-- The normalized rank-one product obtained after compressing the active B sector. -/
def SecondCutRankOneBlockProduct
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  let A := M.fourFactorA region
  let H := component.1.restrictScalars Complex
  let W0 := W.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} n
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A H) CD) :=
    (LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  ∃ phi : Semantics.CompositeSystem A W0,
    ‖phi‖ = 1 ∧
    T.conjOperator Rcompressed =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright
end BPTCommutingProjectorModel
end Bounds
end QEC


