-- Prove2me | Definitions.Def_QEC_Import_Typed_2435cb85c2937e18
-- name    : QEC_Import_Typed_2435cb85c2937e18
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T01:03:52.681784+00:00
-- url     : https://prove2.me/theorems/4221f868-a367-48a1-b5f4-a635764e13e5
-- title:
--   Exact source statement: BPTCommuting Projector Model: final Assembly Associator symm conj tensor Map
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorSpecialization.lean#L24-L45

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds
open scoped TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_tensorMap_QECertTypedStatement : Prop :=
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
          (TensorProduct.map A0
            (TensorProduct.map (1 : Semantics.Operator X) (1 : Semantics.Operator D))) =
        TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D)


