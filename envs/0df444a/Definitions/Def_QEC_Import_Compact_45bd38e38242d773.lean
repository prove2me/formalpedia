-- Prove2me | Definitions.Def_QEC_Import_Compact_45bd38e38242d773
-- name    : QEC_Import_Compact_45bd38e38242d773
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:28.393538+00:00
-- url     : https://prove2.me/theorems/e2be5d9a-5c51-43f4-a555-ce84324bccb4
-- title:
--   Exact source statement: BPTCommuting Projector Model: first Cut Factorized Compression eq sequential
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean#L26-L39

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
set_option autoImplicit false
universe checked_u0
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.firstCutFactorizedCompression_eq_sequential_QECertStatement : Prop :=
∀ {L : QEC.Bounds.BPTQuditLattice} {kappa : Type checked_u0} [inst : Fintype kappa]
  (M : QEC.Bounds.BPTCommutingProjectorModel L kappa) (region : Finset (QEC.Bounds.BPTQuditLattice.Site L))
  (pB : Submodule ℂ (QEC.Bounds.BPTCommutingProjectorModel.fourFactorB M region))
  (pC : Submodule ℂ (QEC.Bounds.BPTCommutingProjectorModel.fourFactorC M region)),
  LinearMap.adjoint
        (QEC.Bounds.BPTCommutingProjectorModel.firstCutSelectedCEmbedding M region pC ∘ₗ
          QEC.Bounds.BPTCommutingProjectorModel.firstCutSelectedBAfterCEmbedding M region pB pC) ∘ₗ
      QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift M region ∘ₗ
        QEC.Bounds.BPTCommutingProjectorModel.firstCutSelectedCEmbedding M region pC ∘ₗ
          QEC.Bounds.BPTCommutingProjectorModel.firstCutSelectedBAfterCEmbedding M region pB pC =
    QEC.Bounds.BPTCommutingProjectorModel.sequentialFirstCutJointCompression M region pB pC


