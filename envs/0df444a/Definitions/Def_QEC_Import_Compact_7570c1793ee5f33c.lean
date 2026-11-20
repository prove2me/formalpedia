-- Prove2me | Definitions.Def_QEC_Import_Compact_7570c1793ee5f33c
-- name    : QEC_Import_Compact_7570c1793ee5f33c
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:49:35.756193+00:00
-- url     : https://prove2.me/theorems/300138ca-5a29-444d-a100-2ccebb6bb345
-- title:
--   Exact source statement: BPTCommuting Projector Model: first Cut Code Lift sector dichotomy
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4224-L4262

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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_dichotomy_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)),
M.firstCutCodeLift region * M.firstCutSectorLift region component = 0 ∨
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
        M.firstCutCodeLift region


