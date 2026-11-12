-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_CrossedHomomorphism
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_CrossedHomomorphism
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:20.751411+00:00
-- url     : https://prove2.me/theorems/ed28a161-39bb-464c-8f2f-bb146d2ce020
-- title:
--   Isaacs Ch. 3, Lemma 3.6: crossed homomorphisms
-- statement:
--   Formalizes the four basic facts of Isaacs, *Finite Group Theory*, §3B, Lemma 3.6 (pp. 76–78) on crossed homomorphisms (1-cocycles). Since Mathlib's `groupCohomology.oneCocycles` only handles commutative coefficients, crossed homomorphisms with non-abelian coefficients are defined here. A left-action convention is used, $\varphi(xy)=\varphi(x)\cdot x\cdot\varphi(y)$, which mirrors the book's right-action convention; the book's right cosets become left cosets.
--
--   Main definitions: `CrossedHom` (a crossed homomorphism from $G$ acting by automorphisms on $N$) and its kernel `ker` (Lemma 3.6(b): the set where $\varphi=1$ is a subgroup).
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/CrossedHomomorphism.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/CrossedHomomorphism.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.Index

namespace OddOrder.Isaacs.Ch03

section

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]

/-- **Isaacs p. 77 (crossed homomorphism)**: `G` が `N` に automorphism で作用する
(`MulDistribMulAction G N`) とき, `φ : G → N` が **crossed homomorphism** とは
`φ(xy) = φ(x) * x • φ(y)` を満たすこと (左作用 convention; 書籍の右作用版
`φ(xy) = φ(x)^y φ(y)` の mirror). 作用が自明なら通常の準同型に一致する. -/
structure CrossedHom (G N : Type*) [Group G] [Group N] [MulDistribMulAction G N] where
  /-- 台となる写像. -/
  toFun : G → N
  /-- Crossed homomorphism 条件 (左 1-cocycle 等式). -/
  map_mul_smul' : ∀ x y : G, toFun (x * y) = toFun x * x • toFun y

namespace CrossedHom

instance : FunLike (CrossedHom G N) G N where
  coe := CrossedHom.toFun
  coe_injective := fun φ ψ h => by cases φ; cases ψ; congr

@[ext]
lemma ext {φ ψ : CrossedHom G N} (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext _ _ h

@[simp]
lemma coe_mk (f : G → N) (h : ∀ x y : G, f (x * y) = f x * x • f y) : ⇑(mk f h) = f := rfl

/-- Crossed homomorphism 条件 (coercion 形). -/
lemma map_mul_smul (φ : CrossedHom G N) (x y : G) : φ (x * y) = φ x * x • φ y :=
  φ.map_mul_smul' x y

/-- **Isaacs Lemma 3.6(a)**: `φ(1) = 1`. -/
@[simp]
lemma map_one (φ : CrossedHom G N) : φ 1 = 1 := by
  have h := φ.map_mul_smul 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_mul.mp h

/-- Inverse 公式 `φ(x⁻¹) = x⁻¹ • φ(x)⁻¹` (書籍 Lemma 3.6 証明中の
`φ(k⁻¹)` の計算の一般形). -/
lemma map_inv (φ : CrossedHom G N) (x : G) : φ x⁻¹ = x⁻¹ • (φ x)⁻¹ := by
  have h := φ.map_mul_smul x x⁻¹
  rw [mul_inv_cancel, φ.map_one] at h
  have h2 : x • φ x⁻¹ = (φ x)⁻¹ := eq_inv_of_mul_eq_one_right h.symm
  rw [← h2, inv_smul_smul]

/-- **Isaacs Lemma 3.6(b)**: crossed homomorphism の kernel
`{x | φ(x) = 1}` は部分群. -/
def ker (φ : CrossedHom G N) : Subgroup G where
  carrier := {x | φ x = 1}
  one_mem' := φ.map_one
  mul_mem' := fun {x y} hx hy => by
    have hx' : φ x = 1 := hx
    have hy' : φ y = 1 := hy
    change φ (x * y) = 1
    rw [φ.map_mul_smul, hx', hy', smul_one, mul_one]
  inv_mem' := fun {x} hx => by
    have hx' : φ x = 1 := hx
    change φ x⁻¹ = 1
    rw [φ.map_inv, hx', inv_one, smul_one]

@[simp]
lemma mem_ker (φ : CrossedHom G N) {x : G} : x ∈ φ.ker ↔ φ x = 1 := Iff.rfl

end CrossedHom

end

end OddOrder.Isaacs.Ch03


