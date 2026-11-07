-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalPhysical
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalPhysical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:09:45.827227+00:00
-- url     : https://prove2.me/theorems/be9fd91e-b88e-4f33-b8cc-9a60c6081378
-- title:
--   External Physical
-- statement:
--   Definitions and structural lemmas for External Physical, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/ExternalPhysical.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalData
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def ExternalResidualPhysicalWitness
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
    (Y : Semantics.Operator (WC.restrictScalars Complex)) : Prop :=
  ∃ (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) (scalar : Complex),
    M.ExternalResidualProbePullback region ccomponent WC UC Y E Ephysical ∧
    M.PhysicalExternalResidualProbeCompression region Qsecond Ephysical scalar
set_option maxHeartbeats 4000000
end BPTCommutingProjectorModel
end Bounds
end QEC


