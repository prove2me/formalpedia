-- Prove2me | Definitions.Def_QEC_Import_Compact_a7c59a129dc32b69
-- name    : QEC_Import_Compact_a7c59a129dc32b69
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:14.386691+00:00
-- url     : https://prove2.me/theorems/84b694fa-e4d3-489e-9c87-6606b39fd092
-- title:
--   Exact source statement: BPTCommuting Projector Model: boundary To Four Factor Reorder to Linear Equiv apply tmul
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1458-L1468

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
universe checked_u0
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul_QECertStatement : Prop :=
∀ {L : QEC.Bounds.BPTQuditLattice} {kappa : Type checked_u0} [inst : Fintype kappa]
  (M : QEC.Bounds.BPTCommutingProjectorModel L kappa) (region : Finset (QEC.Bounds.BPTQuditLattice.Site L))
  (a : QEC.Bounds.BPTCommutingProjectorModel.fourFactorA M region)
  (b : QEC.Bounds.BPTCommutingProjectorModel.fourFactorB M region)
  (c : QEC.Bounds.BPTCommutingProjectorModel.fourFactorC M region)
  (d : QEC.Bounds.BPTCommutingProjectorModel.fourFactorD M region),
  (QEC.Semantics.UnitaryTransport.toLinearEquiv
        (QEC.Semantics.UnitaryTransport.symm
          (QEC.Bounds.BPTCommutingProjectorModel.fourFactorMiddleReassociate M region)))
      ((QEC.Semantics.UnitaryTransport.toLinearEquiv
          (QEC.Bounds.BPTCommutingProjectorModel.boundaryToMiddleReorder
            (QEC.Bounds.BPTCommutingProjectorModel.fourFactorA M region)
            (QEC.Bounds.BPTCommutingProjectorModel.fourFactorB M region)
            (QEC.Bounds.BPTCommutingProjectorModel.fourFactorC M region)
            (QEC.Bounds.BPTCommutingProjectorModel.fourFactorD M region)))
        (b ⊗ₜ[ℂ] c ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] d))) =
    a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))


