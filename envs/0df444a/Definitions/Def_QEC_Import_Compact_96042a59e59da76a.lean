-- Prove2me | Definitions.Def_QEC_Import_Compact_96042a59e59da76a
-- name    : QEC_Import_Compact_96042a59e59da76a
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:34.855267+00:00
-- url     : https://prove2.me/theorems/388e8b98-c129-4db3-858d-9007710d422e
-- title:
--   Exact source statement: Second Cut Rank One Block Product: witness norm
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneProductWitnessNorm.lean#L20-L36

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitness
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.SecondCutRankOneBlockProduct.witness_norm_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] {M : BPTCommutingProjectorModel L kappa} {region : Finset L.Site}
    {component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {n : Nat} [NeZero n]
    {W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n))}
    {Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))}
    (h : SecondCutRankOneBlockProduct (n := n) M region component W U Qright),
‖SecondCutRankOneBlockProduct.witness (n := n) h‖ = 1


