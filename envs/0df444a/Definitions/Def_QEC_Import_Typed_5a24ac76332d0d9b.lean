-- Prove2me | Definitions.Def_QEC_Import_Typed_5a24ac76332d0d9b
-- name    : QEC_Import_Typed_5a24ac76332d0d9b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:47:48.066095+00:00
-- url     : https://prove2.me/theorems/c04b7097-f6a1-42fe-bd77-c5a41319c56b
-- title:
--   Exact source statement: BPTCommuting Projector Model: active Complement Projector is Symmetric Projection
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L732-L757

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

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.activeComplementProjector_isSymmetricProjection_QECertTypedStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (ActiveComplementDomain M region nC WC))
    (hP : @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementDomain M region nC WC) _ _ _ P),
@LinearMap.IsSymmetricProjection Complex
      (ActiveComplementCodomain M region) _ _ _
      (M.activeComplementProjector region ccomponent WC UC P)


