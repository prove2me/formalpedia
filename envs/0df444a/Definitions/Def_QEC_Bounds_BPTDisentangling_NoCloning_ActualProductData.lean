-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActualProductData
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ActualProductData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:24:45.420048+00:00
-- url     : https://prove2.me/theorems/03d34ccf-d10c-4016-a7aa-75ecfee04ee6
-- title:
--   Actual Product Data
-- statement:
--   Definitions and structural lemmas for Actual Product Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActualProductData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductData
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000 in
/-- Actual sector coordinates together with the exact fixed-data D5 evidence. -/
inductive ActualFixedActiveDataProductRankOneTensor
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Prop where
  | intro
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (nC : Nat) [hnC : NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (nB : Nat) [hnB : NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (evidence : M.FixedActiveDataProductRankOneTensor
      region bcomponent ccomponent WB WC UB UC P_D Qsecond) :
    ActualFixedActiveDataProductRankOneTensor M region
end BPTCommutingProjectorModel
end Bounds
end QEC


