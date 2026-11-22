-- Prove2me | Definitions.Def_QEC_Import_Typed_8e968132ef42b4f0
-- name    : QEC_Import_Typed_8e968132ef42b4f0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T01:52:01.862255+00:00
-- url     : https://prove2.me/theorems/fb093e85-9cff-444f-a6f4-fd3d772ac041
-- title:
--   Exact source statement: BPTCommuting Projector Model: final Assembly Associator symm conj left Map right one
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorRightOne.lean#L24-L56

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorRightOne
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds
open scoped TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_leftMap_right_one_QECertTypedStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)),
    let H := Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    ∀ (A0 : Semantics.Operator H),
      (tensorAssociatorUnitary H X D).symm.conjOperator
          (TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D))) =
        TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D)


