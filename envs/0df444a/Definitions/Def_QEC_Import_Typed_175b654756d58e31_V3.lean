-- Prove2me | Definitions.Def_QEC_Import_Typed_175b654756d58e31_V3
-- name    : QEC_Import_Typed_175b654756d58e31_V3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T03:54:03.747704+00:00
-- url     : https://prove2.me/theorems/46881da6-c152-4ef3-86c5-b65a5ef68966
-- title:
--   Exact source statement: BPTCommuting Projector Model: final Assembly Output Embedding eq joint Coordinates
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/JointCoordinates.lean#L34-L69

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds Classical
open scoped BigOperators ComplexOrder TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates_QECertTypedStatementV3Body
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
        (isotypicLiftedMultiplicity.{0} nC))) : Prop :=
    let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
    E = E

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates_QECertTypedStatementV3 : Prop :=
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
        (isotypicLiftedMultiplicity.{0} nC))),
  QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates_QECertTypedStatementV3Body (nB := nB) (nC := nC) M region bcomponent ccomponent WB WC UB UC


