-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitness
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:52:33.462084+00:00
-- url     : https://prove2.me/theorems/4d098ed4-56cd-4fa7-9cce-bddd84ce2811
-- title:
--   Left Rank One Product Witness
-- statement:
--   Definitions and structural lemmas for Left Rank One Product Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneProductWitness.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def SecondCutRankOneBlockProduct.witness
    {M : BPTCommutingProjectorModel L kappa} {region : Finset L.Site}
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
    (h : SecondCutRankOneBlockProduct (n := n) M region component W U Qright) :
    Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex) :=
  Classical.choose h
end BPTCommutingProjectorModel
end Bounds
end QEC


