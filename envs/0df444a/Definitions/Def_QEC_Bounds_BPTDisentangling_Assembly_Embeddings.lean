-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
-- name    : QEC_Bounds_BPTDisentangling_Assembly_Embeddings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T00:53:45.009213+00:00
-- url     : https://prove2.me/theorems/73613432-81c2-43c6-aef3-fd96d2d71cc0
-- title:
--   Embeddings
-- statement:
--   Definitions and structural lemmas for Embeddings, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/Embeddings.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
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


