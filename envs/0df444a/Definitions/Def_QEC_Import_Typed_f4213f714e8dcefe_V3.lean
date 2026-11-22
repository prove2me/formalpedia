-- Prove2me | Definitions.Def_QEC_Import_Typed_f4213f714e8dcefe_V3
-- name    : QEC_Import_Typed_f4213f714e8dcefe_V3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T03:19:19.265797+00:00
-- url     : https://prove2.me/theorems/51a92734-d706-41b7-b3e4-7da7f79edd89
-- title:
--   Exact source statement: BPTCommuting Projector Model: final Assembly Reassociated Embedding compression region Local
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RegionCompression.lean#L27-L101

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorRightOne
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompression
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds Classical
open scoped BigOperators ComplexOrder TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
universe typed_u
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3Core
    {H SN X D : Type typed_u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup SN] [InnerProductSpace Complex SN] [Semantics.FiniteQuantumSystem SN]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (E : Semantics.CompositeSystem SN (Semantics.CompositeSystem X D) →ₗ[Complex] H)
    (G : Semantics.Operator H) (A0 : Semantics.Operator SN) : Prop :=
    ∀ (O : Semantics.UnitaryTransport
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem SN X) D)
        (Semantics.CompositeSystem SN
          (Semantics.CompositeSystem X D))),
      O = tensorAssociatorUnitary SN X D →
      ∀ (Enew : Semantics.CompositeSystem
          (Semantics.CompositeSystem SN X) D →ₗ[Complex]
        H),
        Enew = E.comp O.toLinearEquiv.toLinearMap →
        (LinearMap.adjoint Enew).comp
            (G.comp Enew) =
          TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
            (1 : Semantics.Operator D)

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3Body
{L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
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
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem) : Prop :=
    let F := M.fourFactorTransport region
    let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
    let N := isotypicLiftedMultiplicity.{0} nB
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
    let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
      (LinearMap.adjoint eSel).comp (A.comp eSel)
    QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3Core E (F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)) A0

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3 : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
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
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem),
  QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3Body (nB := nB) (nC := nC) M region bcomponent ccomponent WB WC UB UC A


