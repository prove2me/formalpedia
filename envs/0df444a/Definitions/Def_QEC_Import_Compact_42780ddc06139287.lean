-- Prove2me | Definitions.Def_QEC_Import_Compact_42780ddc06139287
-- name    : QEC_Import_Compact_42780ddc06139287
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:49:45.785607+00:00
-- url     : https://prove2.me/theorems/7baf71c4-bd9f-4008-a42d-289c06bf9b5e
-- title:
--   Exact source statement: BPTCommuting Projector Model: joint active sector code support of active cuts
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L932-L1030

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.joint_active_sector_code_support_of_active_cuts_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region),
(M.fourFactorTransport region).conjOperator M.fullCodeProjector *
        (M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
              (leftIsotypicSectorProjector
                (M.fourFactorProjectorABLocal region) bcomponent))) *
        (M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
            ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
              (leftIsotypicSectorProjector
                (M.firstCutProjectorMC region) ccomponent))) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector


