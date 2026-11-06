-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
-- name    : QEC_Bounds_BPTDisentangling_Sectors_Embedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:17:01.395233+00:00
-- url     : https://prove2.me/theorems/41faffd3-d151-4c5f-95c5-b7fcf5a6f1c8
-- title:
--   Embedding
-- statement:
--   Definitions and structural lemmas for Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def tensorTripleSubtypeEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) :
    (Semantics.CompositeSystem (Semantics.CompositeSystem A p) C) →ₗ[Complex]
      Semantics.CompositeSystem (Semantics.CompositeSystem A B) C :=
  TensorProduct.map
    (TensorProduct.map (1 : Semantics.Operator A) p.subtype)
    (1 : Semantics.Operator C)
end BPTCommutingProjectorModel
end Bounds
end QEC


