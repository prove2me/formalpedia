-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
-- name    : QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:58:12.194248+00:00
-- url     : https://prove2.me/theorems/8d5d42ae-39bd-4948-823b-7e75c101cb04
-- title:
--   Selected Embedding Core
-- statement:
--   Definitions and structural lemmas for Selected Embedding Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/SelectedEmbeddingCore.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def activeSelectedEmbeddingCore
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nB : Nat} [NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB))) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)) →ₗᵢ[Complex]
      (M.regionSubsystem region).selectedSystem := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  let eB : (Semantics.CompositeSystem (WB.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nB)) →ₗᵢ[Complex] M.fourFactorB region :=
    (bcomponent.1.restrictScalars Complex).subtypeₗᵢ.comp
      UB.symm.toLinearIsometryEquiv.toLinearIsometry
  exact
    (A.selectedFactorization AB hAAB).symm.toLinearIsometryEquiv.toLinearIsometry.comp
      ((TensorProduct.mapIsometry (LinearIsometry.id) eB).comp
        (tensorAssociatorUnitary (M.fourFactorA region) (WB.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nB)).toLinearIsometryEquiv.toLinearIsometry)
end BPTCommutingProjectorModel
end Bounds
end QEC


