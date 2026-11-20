-- Prove2me | Definitions.Def_QEC_Import_Compact_ba2f0537c0540e55
-- name    : QEC_Import_Compact_ba2f0537c0540e55
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T13:58:55.827255+00:00
-- url     : https://prove2.me/theorems/fc540ab3-8b95-44bb-b7ab-456a11d69c5c
-- title:
--   Exact source statement: BPTCommuting Projector Model: active Selected Embedding Core apply tmul
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/SelectedEmbeddingCore.lean#L53-L76

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.activeSelectedEmbeddingCore_apply_tmul_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nB : Nat} [NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (n : isotypicLiftedMultiplicity.{0} nB),
    let image := (M.activeSelectedEmbeddingCore region bcomponent WB UB ((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n))
    image = image


