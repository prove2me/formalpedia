-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryStatement
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IsometryStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:07:30.766496+00:00
-- url     : https://prove2.me/theorems/c1181531-4847-42ff-9e06-1b882dc68561
-- title:
--   Isometry Statement
-- statement:
--   Definitions and structural lemmas for Isometry Statement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryStatement.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 120000 in
def FinalAssemblyOutputEmbeddingIsometry
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
        (isotypicLiftedMultiplicity.{0} nC))) : Prop :=
  let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  (LinearMap.adjoint Eout).comp Eout =
    (1 : Semantics.Operator
      (M.FinalAssemblyCompressionDomain region nB nC WB WC))
end BPTCommutingProjectorModel
end Bounds
end QEC


