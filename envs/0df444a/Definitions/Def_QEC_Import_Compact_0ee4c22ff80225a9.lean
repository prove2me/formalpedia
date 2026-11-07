-- Prove2me | Definitions.Def_QEC_Import_Compact_0ee4c22ff80225a9
-- name    : QEC_Import_Compact_0ee4c22ff80225a9
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:21.228325+00:00
-- url     : https://prove2.me/theorems/b08bb24d-cf9c-46fb-85af-2d7f7f6c50e1
-- title:
--   Exact source statement: BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp overlap Lift Left comp tensor Triple Subtype Embedding
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L396-L424

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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding_QECertStatement : Prop :=
∀  {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B),
(LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        ((overlapLiftLeft (C := C) P).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))) =
      overlapLiftLeft (C := C)
        (overlapProjectorOnIsotypicComponent P component)


