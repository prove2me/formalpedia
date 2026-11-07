-- Prove2me | Definitions.Def_QEC_Import_Compact_452dc9c2926328f6
-- name    : QEC_Import_Compact_452dc9c2926328f6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:09:39.939357+00:00
-- url     : https://prove2.me/theorems/de062c58-7d52-487b-aa80-fdfa951bc26a
-- title:
--   Exact source statement: BPTCommuting Projector Model: active overlap product eq isotypic embedding compression
-- statement:
--   The exact universally quantified proposition of the linked source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L165-L223

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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.active_overlap_product_eq_isotypic_embedding_compression_QECertStatement : Prop :=
∀  {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (hactive :
      (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) *
          overlapLiftLeft (C := C)
            (TensorProduct.map (1 : Semantics.Operator A)
              (leftIsotypicSectorProjector P component)) =
        overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q),
overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q =
      (tensorTripleSubtypeEmbedding (A := A) (C := C)
        (component.1.restrictScalars Complex)).comp
        (((LinearMap.adjoint
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))).comp
          ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
            (tensorTripleSubtypeEmbedding (A := A) (C := C)
              (component.1.restrictScalars Complex)))).comp
          (LinearMap.adjoint
            (tensorTripleSubtypeEmbedding (A := A) (C := C)
              (component.1.restrictScalars Complex))))


