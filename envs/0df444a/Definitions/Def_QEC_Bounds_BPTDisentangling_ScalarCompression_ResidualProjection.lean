-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:07:35.4367+00:00
-- url     : https://prove2.me/theorems/741d8a08-2039-40fd-9a78-1fc22428a71b
-- title:
--   Residual Projection
-- statement:
--   Definitions and structural lemmas for Residual Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def secondCutResidualTheta
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (Qright : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D))) :
    Semantics.Operator (Semantics.CompositeSystem N C) :=
  rightTensorCompression eta
    ((tensorAssociatorUnitary N C D).symm.conjOperator Qright)
end BPTCommutingProjectorModel
end Bounds
end QEC


