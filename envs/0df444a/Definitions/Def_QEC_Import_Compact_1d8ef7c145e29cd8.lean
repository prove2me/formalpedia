-- Prove2me | Definitions.Def_QEC_Import_Compact_1d8ef7c145e29cd8
-- name    : QEC_Import_Compact_1d8ef7c145e29cd8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:24.837191+00:00
-- url     : https://prove2.me/theorems/02facc22-e985-4415-b467-874498b7b8ba
-- title:
--   Exact source statement: BPTCommuting Projector Model: adjoint tensor Triple Subtype Embedding comp overlap Lift Right comp tensor Triple Subtype Embedding
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L459-L516

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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding_QECertStatement : Prop :=
∀  {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B),
(LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        ((overlapLiftRight (A := A) Q).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex))) =
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component)


