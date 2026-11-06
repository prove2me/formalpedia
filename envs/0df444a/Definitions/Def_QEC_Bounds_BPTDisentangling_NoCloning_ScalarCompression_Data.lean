-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Data
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:52:25.947206+00:00
-- url     : https://prove2.me/theorems/48ed73b1-b84e-4e02-9a16-dbaf9c2319c8
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Data.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def PhysicalInternalResidualProbeCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB : Nat} [NeZero nB]
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
    (scalar : Complex) : Prop :=
  Qsecond *
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
          (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond
def ActualInternalResidualProbeCompression
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
    (X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
    (scalar : Complex) : Prop :=
  M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
def ActualInternalResidualScalarCompression
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∀ X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB),
    ∃ scalar : Complex,
      M.ActualInternalResidualProbeCompression region ccomponent WC UC Qsecond X scalar
def ActualExternalResidualProbeCompression
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
    (Y : Semantics.Operator (WC.restrictScalars Complex)) (scalar : Complex) : Prop :=
  M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
def ActualExternalResidualScalarCompression
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∀ Y : Semantics.Operator (WC.restrictScalars Complex),
    ∃ scalar : Complex,
      M.ActualExternalResidualProbeCompression region ccomponent WC UC Qsecond Y scalar
def ActualActiveSectorScalarCompressions
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  (LinearMap.IsSymmetricProjection
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) ∧
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond ≠ 0) ∧
  M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond ∧
  M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond
end BPTCommutingProjectorModel
end Bounds
end QEC


