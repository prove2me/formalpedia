-- Prove2me | Definitions.Def_OddOrder_Mathlib_SemidirectProduct
-- name    : OddOrder_Mathlib_SemidirectProduct
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:23.072459+00:00
-- url     : https://prove2.me/theorems/53bd53f4-6845-4016-8b2e-fa3d37b31704
-- title:
--   Generic helpers for `SemidirectProduct`
-- statement:
--   Supplements to Mathlib's `SemidirectProduct`. The main result is that a semidirect product of two $p$-groups is a $p$-group (`IsPGroup.semidirectProduct`), the core of the argument in Isaacs Lemma 4.32 ($P$ a $p$-group acting on a $p$-group $G$ gives $[G,P]<G$ and $C_G(P)>1$) that $\Gamma=G\rtimes P$ is a $p$-group hence nilpotent.
--
--   Declarations: `SemidirectProduct.finite` (a `Finite` instance via `equivProd`) and `SemidirectProduct.commutator_inl_inr` (the commutator $[\mathrm{inl}\,n,\mathrm{inr}\,g]=\mathrm{inl}(n\cdot\varphi_g(n)^{-1})$).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Mathlib/SemidirectProduct.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/SemidirectProduct.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent

/-- **半直積の Finite instance**. `SemidirectProduct.equivProd` 経由. -/
instance SemidirectProduct.finite {N G : Type*} [Group N] [Group G] [Finite N] [Finite G]
    {φ : G →* MulAut N} : Finite (N ⋊[φ] G) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

/-- **`inl.range ⊔ inr.range = ⊤`**: 半直積は `inl` と `inr` の像で生成される.

`inl_left_mul_inr_right` (∀ x, `inl x.left * inr x.right = x`) から従う.
Γ 内 commutator `⁅inl.range, inr.range⁆` に Isaacs Lem 4.1 (`⁅H, K⁆ ⊴ ⟨H, K⟩`) を
適用する際の前提. -/
theorem SemidirectProduct.inl_range_sup_inr_range_eq_top
    {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} :
    (SemidirectProduct.inl : N →* N ⋊[φ] G).range ⊔
      (SemidirectProduct.inr : G →* N ⋊[φ] G).range = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact Subgroup.mul_mem_sup ⟨x.left, rfl⟩ ⟨x.right, rfl⟩

open scoped commutatorElement in
/-- **`⁅inl n, inr g⁆ = inl (n * (φ g) n⁻¹)`**: Γ = N ⋊[φ] G 内の commutator は
`inl` の中で計算できる. これが `actionCommutator φ` の Γ 内 commutator 表示の核. -/
theorem SemidirectProduct.commutator_inl_inr
    {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} (n : N) (g : G) :
    ⁅(SemidirectProduct.inl n : N ⋊[φ] G), (SemidirectProduct.inr g : N ⋊[φ] G)⁆ =
      SemidirectProduct.inl (n * (φ g) n⁻¹) := by
  rw [commutatorElement_def]
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
                SemidirectProduct.inv_left, SemidirectProduct.inv_right, mul_assoc]


