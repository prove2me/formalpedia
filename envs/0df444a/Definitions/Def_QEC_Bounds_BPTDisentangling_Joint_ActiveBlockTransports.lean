-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
-- name    : QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:24:28.06333+00:00
-- url     : https://prove2.me/theorems/3b5be1fa-1945-4162-9702-29f1cd9bd52c
-- title:
--   Active Block Transports
-- statement:
--   Definitions and structural lemmas for Active Block Transports, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveBlockTransports.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutCore
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
/--
The fixed-witness transport from the simultaneous active `B,C` sector in
second-cut coordinates to the common `A B' B'' C' C''D` coordinates.
-/
noncomputable def secondCutJointActiveBlockTransport
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
        (isotypicLiftedMultiplicity.{0} nC))) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region)
          (bcomponent.1.restrictScalars Complex))
        (Semantics.CompositeSystem (ccomponent.1.restrictScalars Complex)
          (M.fourFactorD region)))
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex))
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))) :=
  composeUnitaryTransport
    (isotypicSectorBlockTransportLeft (M.fourFactorA region)
      (bcomponent.1.restrictScalars Complex) (WB.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nB)
      (Semantics.CompositeSystem (ccomponent.1.restrictScalars Complex)
        (M.fourFactorD region)) UB)
    (composeUnitaryTransport
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorA region)
        (WB.restrictScalars Complex))
        (unitaryLTensor (isotypicLiftedMultiplicity.{0} nB)
          (composeUnitaryTransport (unitaryRTensor UC (M.fourFactorD region))
            (tensorAssociatorUnitary (WC.restrictScalars Complex)
              (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region)))))
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorA region)
        (WB.restrictScalars Complex))
        (tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex)
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm))
set_option maxHeartbeats 800000 in
/--
The companion fixed-witness transport from the simultaneous active sector in
first-cut coordinates to the same common coordinates.
-/
noncomputable def firstCutJointActiveBlockTransport
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
        (isotypicLiftedMultiplicity.{0} nC))) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region)
            (bcomponent.1.restrictScalars Complex))
          (ccomponent.1.restrictScalars Complex))
        (M.fourFactorD region))
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex))
          (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region)))) :=
  composeUnitaryTransport
    (isotypicSectorBlockTransportLeft
      (Semantics.CompositeSystem (M.fourFactorA region)
        (bcomponent.1.restrictScalars Complex))
      (ccomponent.1.restrictScalars Complex) (WC.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) UC)
    (composeUnitaryTransport
      (unitaryRTensor
        (isotypicSectorBlockTransportLeft (M.fourFactorA region)
          (bcomponent.1.restrictScalars Complex) (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex) UB)
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)))
      (tensorAssociatorUnitary
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))))
end BPTCommutingProjectorModel
end Bounds
end QEC


