-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:51:59.030204+00:00
-- url     : https://prove2.me/theorems/21857f44-ce1c-4eed-bf05-d6ec65b2cfe7
-- title:
--   Block Data
-- statement:
--   Definitions and structural lemmas for Block Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/BlockData.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factors
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
/-- The source-level conclusion of the concrete B-first sequential block. -/
def SecondCutActualSequentialActiveBlock
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
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∃ phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex),
    ‖phi‖ = 1 ∧
    let A := M.fourFactorA region
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} nB
    let NC := isotypicLiftedMultiplicity.{0} nC
    let D := M.fourFactorD region
    (M.secondCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC).conjOperator
        (M.sequentialSecondCutJointCompression region pB pC) =
      (unitaryLTensor (Semantics.CompositeSystem A (WB.restrictScalars Complex))
        (tensorAssociatorUnitary N (WC.restrictScalars Complex)
          (Semantics.CompositeSystem NC D)).symm).conjOperator
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond))
end BPTCommutingProjectorModel
end Bounds
end QEC


