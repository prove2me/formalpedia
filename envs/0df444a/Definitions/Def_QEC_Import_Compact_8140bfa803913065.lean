-- Prove2me | Definitions.Def_QEC_Import_Compact_8140bfa803913065
-- name    : QEC_Import_Compact_8140bfa803913065
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:05:24.409768+00:00
-- url     : https://prove2.me/theorems/5bbad631-5ede-45c3-bb7a-abc0b3153cd6
-- title:
--   Exact source statement: BPTCommuting Projector Model: second Cut Code Lift eq active embedding compression of absorption
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L344-L389

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_eq_active_embedding_compression_of_absorption_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region),
let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    M.secondCutCodeLift region =
      J.comp (((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)).comp
        (LinearMap.adjoint J))


