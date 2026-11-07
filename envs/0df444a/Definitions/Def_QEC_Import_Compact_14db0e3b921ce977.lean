-- Prove2me | Definitions.Def_QEC_Import_Compact_14db0e3b921ce977
-- name    : QEC_Import_Compact_14db0e3b921ce977
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:50.721785+00:00
-- url     : https://prove2.me/theorems/9ea65418-59e9-44c6-8169-b265ab185510
-- title:
--   Exact source statement: BPTCommuting Projector Model: regroup actual active sector scalar compressions
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Regrouping.lean#L50-L113

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.regroup_actual_active_sector_scalar_compressions_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hrawInternal :
      M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond)
    (hrawExternal :
      M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond),
RegroupedTwoFactorScalarCompressions
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)


