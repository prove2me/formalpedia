-- Prove2me | Definitions.Def_HatAffineOffsets_TypeI
-- name    : HatAffineOffsets_TypeI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:08:33.884852+00:00
-- url     : https://prove2.me/theorems/0cc2aade-872d-5787-9711-35476b3dacac
-- title:
--   Type I
-- statement:
--   Definitions and structural lemmas for Type I, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineOffsets/TypeI.lean

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
namespace HatAffineOffsets
universe u v w
open Finset
noncomputable local instance _p2m_local_instance_8d02a9c2cf_10 (p : Prop) : Decidable p :=
  Classical.propDecidable p
def OffsetCoverable
    {K : Type u} {I : Type v} {J : Type w}
    (F : (J -> K) -> I -> K) (x : I -> K) : Prop :=
  exists g : J -> K,
    HatAffineGeneral.Covers g (HatAffineGeneral.BadSet F x)
def typeIRoot
    {K : Type u} {I : Type v} [Field K]
    (alpha b x : I -> K) (i : I) : K :=
  (x i - b i) / alpha i
def offsetNormalizationEquiv
    {K : Type u} {I : Type v} [Field K]
    (alpha b : I -> K) (halpha : forall i, alpha i ≠ 0) :
    (I -> K) ≃ (I -> K) where
  toFun x i := (x i - b i) / alpha i
  invFun d i := alpha i * d i + b i
  left_inv x := by
    funext i
    field_simp [halpha i]
    <;> ring
  right_inv d := by
    funext i
    field_simp [halpha i]
    <;> ring
end HatAffineOffsets


