-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_WreathProduct
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_WreathProduct
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:24.318636+00:00
-- url     : https://prove2.me/theorems/ebb26cba-9bd1-4c4e-a666-41e4b5a4e134
-- title:
--   Isaacs §3A: the general wreath product over a $G$-set
-- statement:
--   Formalizes the general wreath product of Isaacs, *Finite Group Theory*, §3A (pp. 73–76). For a group $D$ and a group $Q$ acting on a set $\Omega$, the wreath product $D\wr_\Omega Q$ is the group on $(\Omega\to D)\times Q$ with $\langle a_1,a_2\rangle\langle b_1,b_2\rangle=\langle a_1\cdot(b_1\circ(a_2^{-1}\cdot)),a_2b_2\rangle$, a semidirect product of the base group with the coordinate-permutation action. Mathlib only has the regular wreath product ($\Omega=Q$), so the book's general form is implemented as a generalization of it, and `wreathEquivRegular` records the isomorphism with Mathlib's regular case.
--
--   The main definition is `WreathProduct` (with its group structure, identity laws, etc.).
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/WreathProduct.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/WreathProduct.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.Data.ZMod.Basic

namespace OddOrder.Isaacs.Ch03

variable (D Q Ω : Type*) [Group D] [Group Q] [MulAction Q Ω]

/-- **Isaacs §3A (general wreath product)**: `Q`-集合 `Ω` 上の wreath product.
台は `(Ω → D) × Q`, 積は `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (b₁ ∘ (a₂⁻¹ • ·)), a₂ * b₂⟩`.
mathlib `RegularWreathProduct` の `Ω = Q` (左正則作用) を一般の作用に置換した形. -/
@[ext]
structure WreathProduct where
  /-- The base component `Ω → D`. -/
  left : Ω → D
  /-- The permuting component in `Q`. -/
  right : Q

@[inherit_doc] notation:65 D " ≀[" Ω "] " Q => WreathProduct D Q Ω

namespace WreathProduct

variable {D Q Ω}

instance : Mul (D ≀[Ω] Q) where
  mul a b := ⟨a.1 * fun ω => b.1 (a.2⁻¹ • ω), a.2 * b.2⟩

@[simp]
theorem mul_left (a b : D ≀[Ω] Q) : (a * b).left = a.1 * fun ω => b.1 (a.2⁻¹ • ω) := rfl

@[simp]
theorem mul_right (a b : D ≀[Ω] Q) : (a * b).right = a.right * b.right := rfl

instance : One (D ≀[Ω] Q) where one := ⟨1, 1⟩

omit [MulAction Q Ω] in
@[simp] theorem one_left : (1 : D ≀[Ω] Q).left = 1 := rfl

omit [MulAction Q Ω] in
@[simp] theorem one_right : (1 : D ≀[Ω] Q).right = 1 := rfl

instance : Inv (D ≀[Ω] Q) where
  inv x := ⟨fun ω => x.1⁻¹ (x.2 • ω), x.2⁻¹⟩

@[simp]
theorem inv_left (a : D ≀[Ω] Q) : a⁻¹.left = fun ω => a.left⁻¹ (a.right • ω) := rfl

@[simp]
theorem inv_right (a : D ≀[Ω] Q) : a⁻¹.right = a.right⁻¹ := rfl

instance : Group (D ≀[Ω] Q) where
  mul_assoc a b c := by ext <;> simp [mul_assoc, mul_smul]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

instance : Inhabited (D ≀[Ω] Q) := ⟨1⟩

/-- The canonical projection `D ≀[Ω] Q →* Q`. -/
def rightHom : (D ≀[Ω] Q) →* Q where
  toFun := WreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightHom_apply (a : D ≀[Ω] Q) : rightHom a = a.right := rfl

/-- The canonical injection `Q →* D ≀[Ω] Q` onto the permuting component. -/
def inr : Q →* D ≀[Ω] Q where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem left_inr (q : Q) : (inr q : D ≀[Ω] Q).left = 1 := rfl

@[simp] theorem right_inr (q : Q) : (inr q : D ≀[Ω] Q).right = q := rfl

/-- The canonical injection of the base group `(Ω → D) →* D ≀[Ω] Q`. -/
def inl : (Ω → D) →* D ≀[Ω] Q where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem left_inl (f : Ω → D) : (inl f : D ≀[Ω] Q).left = f := rfl

@[simp] theorem right_inl (f : Ω → D) : (inl f : D ≀[Ω] Q).right = 1 := rfl

@[simp]
theorem rightHom_comp_inr : (rightHom : (D ≀[Ω] Q) →* Q).comp inr = MonoidHom.id _ := by
  ext; simp

/-- The base subgroup `(Ω → D) × 1` is the kernel of `rightHom`, hence normal. -/
theorem range_inl_eq_ker_rightHom :
    (inl : (Ω → D) →* D ≀[Ω] Q).range = (rightHom : (D ≀[Ω] Q) →* Q).ker := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    simp [MonoidHom.mem_ker, rightHom]
  · intro hx
    rw [MonoidHom.mem_ker, rightHom_apply] at hx
    exact ⟨x.left, by ext <;> simp [hx]⟩

/-- base group は正規 (`= ker rightHom`)。 -/
instance range_inl_normal : ((inl : (Ω → D) →* D ≀[Ω] Q).range).Normal := by
  rw [range_inl_eq_ker_rightHom]
  infer_instance

/-- The underlying equiv with the product type. -/
def equivProd : (D ≀[Ω] Q) ≃ (Ω → D) × Q where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.1, x.2⟩

instance [Finite D] [Finite Q] [Finite Ω] : Finite (D ≀[Ω] Q) :=
  Finite.of_equiv _ (equivProd (D := D) (Q := Q) (Ω := Ω)).symm

/-- `x` は base 成分と top 成分の積に分解する: `inl x.left * inr x.right = x`
(`SemidirectProduct.inl_left_mul_inr_right` の wreath 版)。 -/
@[simp] theorem inl_left_mul_inr_right (x : D ≀[Ω] Q) : inl x.left * inr x.right = x := by
  refine WreathProduct.ext ?_ ?_
  · funext ω
    simp only [mul_left, left_inl, right_inl, left_inr, Pi.mul_apply, Pi.one_apply, mul_one]
  · simp only [mul_right, right_inl, right_inr, one_mul]

end WreathProduct

end OddOrder.Isaacs.Ch03


