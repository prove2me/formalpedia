-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:02:04.887533+00:00
-- url     : https://prove2.me/theorems/c2dd2c73-7305-458b-a5e7-5a6a9b903fbe
-- title:
--   Compression Exterior Coordinates
-- statement:
--   Definitions and structural lemmas for Compression Exterior Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorCoordinates.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
abbrev FinalAssemblyCompressionDomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Type :=
  Semantics.CompositeSystem
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB))
    (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def finalAssemblyCompressionActiveEmbedding
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
        (isotypicLiftedMultiplicity.{0} nC))) :=
  (show
    M.FinalAssemblyCompressionDomain region nB nC WB WC →ₗ[Complex]
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.regionSubsystem region).complementSystem) from
    TensorProduct.map
      (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
      (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def finalAssemblyCompressionCoordinateEmbedding
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
        (isotypicLiftedMultiplicity.{0} nC))) :=
  (M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
    (M.finalAssemblyCompressionActiveEmbedding region bcomponent ccomponent WB WC UB UC)
end BPTCommutingProjectorModel
end Bounds
end QEC


