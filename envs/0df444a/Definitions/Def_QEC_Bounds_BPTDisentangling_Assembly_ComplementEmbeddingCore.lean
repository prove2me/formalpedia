-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
-- name    : QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:58:08.129756+00:00
-- url     : https://prove2.me/theorems/09dbed26-86ae-4018-bd3f-736d4d8304b8
-- title:
--   Complement Embedding Core
-- statement:
--   Definitions and structural lemmas for Complement Embedding Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/ComplementEmbeddingCore.lean

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
set_option maxHeartbeats 450000 in
set_option synthInstance.maxHeartbeats 50000 in
/-- The concrete coordinate realization of the active complement embedding. -/
noncomputable def activeComplementCoordinateEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))) →ₗᵢ[Complex]
      (M.regionSubsystem region).complementSystem := by
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let eC : (Semantics.CompositeSystem (WC.restrictScalars Complex)
      (isotypicLiftedMultiplicity.{0} nC)) →ₗᵢ[Complex] M.fourFactorC region :=
    (ccomponent.1.restrictScalars Complex).subtypeₗᵢ.comp
      UC.symm.toLinearIsometryEquiv.toLinearIsometry
  exact
    (AB.complementFactorization ABC hABABC).symm.toLinearIsometryEquiv.toLinearIsometry.comp
      ((TensorProduct.mapIsometry eC (LinearIsometry.id)).comp
        (tensorAssociatorUnitary (WC.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region)).symm.toLinearIsometryEquiv.toLinearIsometry)
noncomputable def activeComplementEmbeddingCore
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :=
  M.activeComplementCoordinateEmbedding region ccomponent WC UC
end BPTCommutingProjectorModel
end Bounds
end QEC


