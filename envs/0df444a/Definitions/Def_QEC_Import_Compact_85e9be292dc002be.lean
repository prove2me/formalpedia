-- Prove2me | Definitions.Def_QEC_Import_Compact_85e9be292dc002be
-- name    : QEC_Import_Compact_85e9be292dc002be
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:46.403432+00:00
-- url     : https://prove2.me/theorems/89683d72-0339-4887-ace1-ea15da7ac82c
-- title:
--   Exact source statement: BPTCommuting Projector Model: external Residual scalar compression on actual active sector
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/ExternalTransport.lean#L27-L195

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
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
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.externalResidual_scalar_compression_on_actual_active_sector_QECertStatement : Prop :=
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
    (Y : Semantics.Operator (WC.restrictScalars Complex))
    (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) (scalar : Complex)
    (hPullback : M.ExternalResidualProbePullback
      region ccomponent WC UC Y E Ephysical)
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hscalar : M.PhysicalExternalResidualProbeCompression
      region Qsecond Ephysical scalar),
M.ActualExternalResidualProbeCompression
      region ccomponent WC UC Qsecond Y scalar


