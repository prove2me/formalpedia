-- Prove2me | Definitions.Def_QEC_Import_Compact_0f5a8c0e18c8f014
-- name    : QEC_Import_Compact_0f5a8c0e18c8f014
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:50:49.771414+00:00
-- url     : https://prove2.me/theorems/24b0e26a-d33e-42ea-89fa-83b3eeebdc3b
-- title:
--   Exact source statement: BPTCommuting Projector Model: first Cut compressed Code is Symmetric Projection
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeProjection.lean#L25-L71

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutFactorNonzero
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeProjection
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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressedCode_isSymmetricProjection_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)),
let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
    let H := component.1.restrictScalars Complex
    let D := M.fourFactorD region
    let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
    ((LinearMap.adjoint J).comp ((M.firstCutCodeLift region).comp J)).IsSymmetricProjection


