-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:43:57.63861+00:00
-- url     : https://prove2.me/theorems/e9139fe1-1147-4822-ba10-df1971ffba76
-- title:
--   Sequential Embedding
-- statement:
--   Definitions and structural lemmas for Sequential Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbedding.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


