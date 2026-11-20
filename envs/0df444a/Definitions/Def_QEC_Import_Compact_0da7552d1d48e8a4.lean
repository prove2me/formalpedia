-- Prove2me | Definitions.Def_QEC_Import_Compact_0da7552d1d48e8a4
-- name    : QEC_Import_Compact_0da7552d1d48e8a4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:05:13.441524+00:00
-- url     : https://prove2.me/theorems/339dddfe-37ce-48cd-aa3d-070d0b1dc9da
-- title:
--   Exact source statement: BPTCommuting Projector Model: second Cut compressed scalar for left subtype probe
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Coordinates.lean#L29-L76

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 300000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_scalar_for_left_subtype_probe_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (H : Submodule Complex (M.fourFactorB region))
    (J : Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) →ₗ[Complex]
      Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
    (hJ : J = tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) H)
    (Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)))
    (Esub : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) H)),
∃ scalar : Complex,
      Rcompressed *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Esub *
          Rcompressed =
        scalar • Rcompressed


