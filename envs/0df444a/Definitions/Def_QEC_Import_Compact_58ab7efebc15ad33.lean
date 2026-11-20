-- Prove2me | Definitions.Def_QEC_Import_Compact_58ab7efebc15ad33
-- name    : QEC_Import_Compact_58ab7efebc15ad33
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:55:46.692638+00:00
-- url     : https://prove2.me/theorems/3f14bdc6-b139-4972-aefa-bccde94e972e
-- title:
--   Exact source statement: BPTCommuting Projector Model: joint BCSector Compression Left eq sequential First Cut Compression
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean#L43-L69

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)),
(LinearMap.adjoint
      (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.firstCutCodeLift region).comp
        (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      M.sequentialFirstCutJointCompression region pB pC


