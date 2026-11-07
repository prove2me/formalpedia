-- Prove2me | Definitions.Def_QEC_Import_Compact_d76dd315620d14a8
-- name    : QEC_Import_Compact_d76dd315620d14a8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:15.637206+00:00
-- url     : https://prove2.me/theorems/555e3108-4027-400a-adc5-9a9ba3fb8517
-- title:
--   Exact source statement: BPTCommuting Projector Model: tensor Triple Subtype Embedding comp adjoint eq left Isotypic Sector Lift
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L141-L157

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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift_QECertStatement : Prop :=
∀  {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B),
(tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex)).comp
        (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
          (component.1.restrictScalars Complex))) =
      overlapLiftLeft (C := C)
        (TensorProduct.map (1 : Semantics.Operator A)
          (leftIsotypicSectorProjector P component))


