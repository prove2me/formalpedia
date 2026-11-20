-- Prove2me | Definitions.Def_QEC_Import_Compact_f7cc1b973e83a32c
-- name    : QEC_Import_Compact_f7cc1b973e83a32c
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T13:58:46.351944+00:00
-- url     : https://prove2.me/theorems/c93edbe5-f16e-44f6-b52f-8b5924ddf5de
-- title:
--   Exact source statement: BPTCommuting Projector Model: active Complement Embedding Core apply tmul
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/ComplementEmbeddingCore.lean#L70-L92

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_apply_tmul_QECertStatement : Prop :=
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
    (x : WC.restrictScalars Complex) (n : isotypicLiftedMultiplicity.{0} nC)
    (d : M.fourFactorD region),
    let image := (M.activeComplementEmbeddingCore region ccomponent WC UC (x ⊗ₜ[Complex] (n ⊗ₜ[Complex] d)))
    image = image


