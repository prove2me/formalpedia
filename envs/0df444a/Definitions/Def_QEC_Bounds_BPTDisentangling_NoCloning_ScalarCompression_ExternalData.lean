-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalData
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:02:45.552921+00:00
-- url     : https://prove2.me/theorems/46fbf25b-1d3d-45a4-a21d-6431d35db713
-- title:
--   External Data
-- statement:
--   Definitions and structural lemmas for External Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/ExternalData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def ExternalResidualProbePullback
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Y : Semantics.Operator (WC.restrictScalars Complex))
    (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) : Prop :=
  E = UC.symm.conjOperator
      (TensorProduct.map Y
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))) ∧
  Ephysical = (ccomponent.1.restrictScalars Complex).subtype.comp
    (E.comp (LinearMap.adjoint (ccomponent.1.restrictScalars Complex).subtype))
def PhysicalExternalResidualProbeCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB : Nat} [NeZero nB]
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (Ephysical : Semantics.Operator (M.fourFactorC region))
    (scalar : Complex) : Prop :=
  Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Ephysical (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond
end BPTCommutingProjectorModel
end Bounds
end QEC


