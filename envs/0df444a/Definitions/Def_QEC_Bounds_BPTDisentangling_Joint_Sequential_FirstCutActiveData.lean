-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActiveData
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActiveData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:00:18.151785+00:00
-- url     : https://prove2.me/theorems/245b0d2b-4555-4e0c-aeba-0029993fd74b
-- title:
--   First Cut Active Data
-- statement:
--   Definitions and structural lemmas for First Cut Active Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutActiveData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000 in
/-- The concrete first-cut sequential active block with the residual `D` factor unchanged. -/
def FirstCutActualSequentialActiveBlock
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))) : Prop :=
  (M.firstCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
      (M.sequentialFirstCutJointCompression region
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex)) =
    (tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))).conjOperator
      (TensorProduct.map
        (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
          (WC.restrictScalars Complex) Pfirst) P_D)
end BPTCommutingProjectorModel
end Bounds
end QEC


