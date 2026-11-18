-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
-- name    : QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T04:08:46.44833+00:00
-- url     : https://prove2.me/theorems/e5120c66-3133-4120-88ec-5efbf355b7b9
-- title:
--   Assembly Helpers
-- statement:
--   Definitions and structural lemmas for Assembly Helpers, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def activeSelectedEmbedding
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
      (M.regionSubsystem region).selectedSystem :=
  M.activeSelectedEmbeddingCore region bcomponent WB UB
noncomputable def activeComplementEmbedding
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
      (M.regionSubsystem region).complementSystem :=
  M.activeComplementEmbeddingCore region ccomponent WC UC
set_option maxHeartbeats 1600000 in
/-- The selected/complement embedding expressed in the original region coordinates. -/
noncomputable def finalAssemblyInputEmbedding
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
  (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
    ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
      (TensorProduct.map
        (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
        (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap))
set_option maxHeartbeats 1600000 in
/-- The same embedding expressed through the active block and final product regrouping. -/
noncomputable def finalAssemblyOutputEmbedding
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
  (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
    (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
    (ccomponent.1.restrictScalars Complex)).comp
    ((M.secondCutJointActiveBlockTransport
      region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
      ((tensorAssociatorUnitary
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
          (WC.restrictScalars Complex))
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
        (productBlockRegrouping (A := M.fourFactorA region)
          (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
          (X := WC.restrictScalars Complex)
          (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
            (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap))
noncomputable def rankOneTensorOperator
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (v : H) (P : Semantics.Operator K) :
    Semantics.Operator (Semantics.CompositeSystem H K) :=
  TensorProduct.map (InnerProductSpace.rankOne Complex v v).toLinearMap P
abbrev ActiveComplementDomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nC : Nat)
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Type :=
  Semantics.CompositeSystem (WC.restrictScalars Complex)
    (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region))
abbrev ActiveComplementCodomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem region).complementSystem
abbrev FinalActiveProductDomain
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) : Type :=
  Semantics.CompositeSystem
    (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
set_option maxHeartbeats 1600000 in
/-- The final common-coordinate rank-one product before regrouping. -/
noncomputable def finalActiveProductOperator
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region))) :
    Semantics.Operator (FinalActiveProductDomain M region nB nC WB WC) :=
  TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    (TensorProduct.map
      (InnerProductSpace.rankOne Complex
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap P_D)
noncomputable def activeComplementEmbeddingLinearMap
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
    ActiveComplementDomain M region nC WC →ₗ[Complex]
      ActiveComplementCodomain M region := by
  let eComp := M.activeComplementEmbedding region ccomponent WC UC
  exact
    { toFun := fun x => eComp x
      map_add' := fun x y => eComp.map_add x y
      map_smul' := fun c x => by
        change eComp.toLinearMap (c • x) = c • eComp.toLinearMap x
        exact eComp.toLinearMap.map_smul c x }
noncomputable def activeComplementProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (ActiveComplementDomain M region nC WC)) :
    Semantics.Operator (ActiveComplementCodomain M region) :=
  let E := M.activeComplementEmbedding region ccomponent WC UC
  E.toLinearMap.comp (P.comp (LinearMap.adjoint E.toLinearMap))
end BPTCommutingProjectorModel
end Bounds
end QEC


