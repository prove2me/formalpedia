-- Prove2me | Definitions.Def_QEC_Import_Compact_9b62ca70080600a3
-- name    : QEC_Import_Compact_9b62ca70080600a3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:05:16.700188+00:00
-- url     : https://prove2.me/theorems/8b0544b4-3a39-409b-b13e-af4cf7f763e7
-- title:
--   Exact source statement: BPTCommuting Projector Model: first Cut exists unique active left Isotypic Sector of nonzero code
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4451-L4551

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
set_option maxHeartbeats 800000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)),
∃ component : isotypicComponents
        (leftInteractionAlgebra (M.firstCutProjectorMC region))
        (M.fourFactorC region),
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          M.firstCutCodeLift region ∧
        ∀ other : isotypicComponents
            (leftInteractionAlgebra (M.firstCutProjectorMC region))
            (M.fourFactorC region),
          other ≠ component →
          M.firstCutCodeLift region * M.firstCutSectorLift region other = 0


