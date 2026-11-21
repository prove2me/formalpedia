-- Prove2me | Definitions.Def_QEC_Import_Typed_fad7a53b486a4f25
-- name    : QEC_Import_Typed_fad7a53b486a4f25
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T00:23:30.158309+00:00
-- url     : https://prove2.me/theorems/169e26ca-c88f-439c-afca-cfa86cc6db1c
-- title:
--   Exact source statement: BPTCommuting Projector Model: final Assembly Selected Tensor compression region Local
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/SelectedTensorCompression.lean#L27-L82

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SelectedTensorCompression
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblySelectedTensor_compression_regionLocal_QECertTypedStatement : Prop :=
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
        (isotypicLiftedMultiplicity.{0} nC)))
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem),
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let eComp := (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap
    let H := Semantics.CompositeSystem S N
    let K := Semantics.CompositeSystem X D
    let R := M.regionSubsystem region
    let A0 : Semantics.Operator H :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    ∀ (J : Semantics.CompositeSystem H K →ₗ[Complex] R.factorizedSystem),
      J = TensorProduct.map eSel eComp →
      (LinearMap.adjoint J).comp
          ((R.registerFactorization.conjOperator (R.extendLocalToRegister A)).comp J) =
        TensorProduct.map A0 (1 : Semantics.Operator K)


