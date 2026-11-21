-- Prove2me | Definitions.Def_QEC_Import_Typed_b22afd9577f25d66
-- name    : QEC_Import_Typed_b22afd9577f25d66
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:41:53.962674+00:00
-- url     : https://prove2.me/theorems/2c88e1f6-edc6-4c8f-9a5e-7b65ec520feb
-- title:
--   Exact source statement: BPTCommuting Projector Model: active Complement Embedding adjoint comp self
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L691-L710

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 200000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbedding_adjoint_comp_self_QECertTypedStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))),
    let E := M.activeComplementEmbedding region ccomponent WC UC
    (LinearMap.adjoint E.toLinearMap).comp E.toLinearMap =
      (1 : Semantics.Operator
        (ActiveComplementDomain M region nC WC))


