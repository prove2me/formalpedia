-- Prove2me | Definitions.Def_QEC_Import_Compact_4cdbe99c34b948a0
-- name    : QEC_Import_Compact_4cdbe99c34b948a0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:10:32.923564+00:00
-- url     : https://prove2.me/theorems/959a3991-f928-4a5c-887b-8fa142a20fa9
-- title:
--   Exact source statement: BPTCommuting Projector Model: all internal Residual scalar compressions on actual active sector
-- statement:
--   The exact universally quantified proposition of the linked source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/InternalAssembly.lean#L28-L58

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalAssembly
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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.all_internalResidual_scalar_compressions_on_actual_active_sector_QECertStatement : Prop :=
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
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hphysical :
      ∀ X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB),
        ∃ scalar : Complex,
          M.PhysicalInternalResidualProbeCompression region Qsecond X scalar),
M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond


