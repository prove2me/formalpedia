-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorActiveStatement
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorActiveStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:18:08.923913+00:00
-- url     : https://prove2.me/theorems/91795bd0-7ab9-4245-b599-433b90ed6d30
-- title:
--   Compression Exterior Active Statement
-- statement:
--   Definitions and structural lemmas for Compression Exterior Active Statement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorActiveStatement.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The four-factor operator produced after compressing the exterior action. -/
noncomputable def finalAssemblyCompressionActiveResult
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (Z : Semantics.Operator (M.fourFactorD region)) :
    Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC) :=
  TensorProduct.map (1 : Semantics.Operator
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)))
    (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
      (TensorProduct.map
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC)) Z))
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def FinalAssemblyCompressionActiveAt
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem)
    (Z : Semantics.Operator (M.fourFactorD region)) : Prop :=
  let J := M.finalAssemblyCompressionActiveEmbedding
    region bcomponent ccomponent WB WC UB UC
  (LinearMap.adjoint J).comp
      ((((M.regionSubsystem region).registerFactorization.conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P)).comp
        J)) =
      M.finalAssemblyCompressionActiveResult region nB nC WB WC Z
set_option maxHeartbeats 300000 in
def FinalAssemblyCompressionActiveStatement
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) : Prop :=
  ∃ Z : Semantics.Operator (M.fourFactorD region),
    M.FinalAssemblyCompressionActiveAt
      region bcomponent ccomponent WB WC UB UC P Z
end BPTCommutingProjectorModel
end Bounds
end QEC


