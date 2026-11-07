-- Prove2me | Definitions.Def_QEC_Import_Compact_5fad1f5e448917cb
-- name    : QEC_Import_Compact_5fad1f5e448917cb
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:55.75123+00:00
-- url     : https://prove2.me/theorems/0c7f7836-634b-468e-a59d-19566247f6ae
-- title:
--   Exact source statement: BPTCommuting Projector Model: second Cut Factorized Compression eq sequential
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean#L181-L194

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
set_option autoImplicit false
universe checked_u0
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCutFactorizedCompression_eq_sequential_QECertStatement : Prop :=
∀ {L : QEC.Bounds.BPTQuditLattice} {kappa : Type checked_u0} [inst : Fintype kappa]
  (M : QEC.Bounds.BPTCommutingProjectorModel L kappa) (region : Finset (QEC.Bounds.BPTQuditLattice.Site L))
  (pB : Submodule ℂ (QEC.Bounds.BPTCommutingProjectorModel.fourFactorB M region))
  (pC : Submodule ℂ (QEC.Bounds.BPTCommutingProjectorModel.fourFactorC M region)),
  LinearMap.adjoint
        (QEC.Bounds.BPTCommutingProjectorModel.secondCutSelectedBEmbedding M region pB ∘ₗ
          QEC.Bounds.BPTCommutingProjectorModel.secondCutSelectedCAfterBEmbedding M region pB pC) ∘ₗ
      QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift M region ∘ₗ
        QEC.Bounds.BPTCommutingProjectorModel.secondCutSelectedBEmbedding M region pB ∘ₗ
          QEC.Bounds.BPTCommutingProjectorModel.secondCutSelectedCAfterBEmbedding M region pB pC =
    QEC.Bounds.BPTCommutingProjectorModel.sequentialSecondCutJointCompression M region pB pC


