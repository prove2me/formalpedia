-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
-- name    : QEC_Coding_HypergraphProduct_Dimension_Formula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:35:17.216117+00:00
-- url     : https://prove2.me/theorems/f1b4f350-5224-490c-8a12-532997194a5e
-- title:
--   Formula
-- statement:
--   Definitions and structural lemmas for Formula, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def kerCompLinearEquiv
    {F : Type v} {V W X : Type u}
    [Semiring F]
    [AddCommMonoid V] [Module F V]
    [AddCommMonoid W] [Module F W]
    [AddCommMonoid X] [Module F X]
    (e : V ≃ₗ[F] W) (f : W →ₗ[F] X) :
    LinearMap.ker (f.comp e.toLinearMap) ≃ₗ[F] LinearMap.ker f where
  toFun x := ⟨e x.1, by
    change f (e x.1) = 0
    exact x.2⟩
  invFun y := ⟨e.symm y.1, by
    change f (e (e.symm y.1)) = 0
    rw [e.apply_symm_apply]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact e.map_smul a x.1
end QEC.Coding.HypergraphProduct


