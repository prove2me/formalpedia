-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Dimension
-- name    : QEC_Coding_HypergraphProduct_Dimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:27:58.419846+00:00
-- url     : https://prove2.me/theorems/d790773a-b729-4e91-b621-d2a7d44b5fb4
-- title:
--   Dimension
-- statement:
--   Definitions and structural lemmas for Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
open TensorProduct
def jointTensorMap
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M]
    [AddCommGroup M'] [Module F M']
    [AddCommGroup N] [Module F N]
    [AddCommGroup N'] [Module F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N') :
    M ⊗[F] N →ₗ[F] (M' ⊗[F] N) × (M ⊗[F] N') :=
  (f.rTensor N).prod (g.lTensor M)
end QEC.Coding.HypergraphProduct


