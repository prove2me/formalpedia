-- Prove2me | Definitions.Def_QEC_Import_Compact_b94046e01f65d82c
-- name    : QEC_Import_Compact_b94046e01f65d82c
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:10:40.868099+00:00
-- url     : https://prove2.me/theorems/d8bc74e0-1591-467c-8145-dab99db6f867
-- title:
--   Exact source statement: BPTCommuting Projector Model: all external Residual scalar compressions on actual active sector
-- statement:
--   The exact universally quantified proposition of the linked source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/ExternalAssembly.lean#L28-L57

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalAssembly
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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.all_externalResidual_scalar_compressions_on_actual_active_sector_QECertStatement : Prop :=
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
      ∀ Y : Semantics.Operator (WC.restrictScalars Complex),
        M.ExternalResidualPhysicalWitness region ccomponent WC UC Qsecond Y),
M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond


