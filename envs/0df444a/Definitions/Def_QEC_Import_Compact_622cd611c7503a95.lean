-- Prove2me | Definitions.Def_QEC_Import_Compact_622cd611c7503a95
-- name    : QEC_Import_Compact_622cd611c7503a95
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:10:01.527782+00:00
-- url     : https://prove2.me/theorems/e437ed23-2311-4cbd-a754-db047f8070ee
-- title:
--   Exact source statement: BPTCommuting Projector Model: isotypic compression overlap product eq sector block product
-- statement:
--   The exact universally quantified proposition of the linked source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L524-L665

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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.isotypic_compression_overlap_product_eq_sector_block_product_QECertStatement : Prop :=
∀  {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B),
(LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        (((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex)))) =
      overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
        overlapLiftRight (A := A)
          (overlapRightProjectorOnIsotypicComponent P Q component)


