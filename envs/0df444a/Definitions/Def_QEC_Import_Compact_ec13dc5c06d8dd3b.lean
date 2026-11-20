-- Prove2me | Definitions.Def_QEC_Import_Compact_ec13dc5c06d8dd3b
-- name    : QEC_Import_Compact_ec13dc5c06d8dd3b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:49:37.383346+00:00
-- url     : https://prove2.me/theorems/9e29bdaa-95e0-420f-b32f-6aeaf4380f63
-- title:
--   Exact source statement: BPTCommuting Projector Model: first Cut all external Local scalar compression of external Boundary recoverable
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4272-L4334

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.firstCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (E : Semantics.Operator (M.fourFactorC region)),
∃ scalar : Complex,
      M.firstCutCodeLift region *
          overlapLiftLeft (C := M.fourFactorD region)
            (TensorProduct.map
              (1 : Semantics.Operator
                (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) E) *
          M.firstCutCodeLift region = scalar • M.firstCutCodeLift region


