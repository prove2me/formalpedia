-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerMulGroup
-- name    : OddOrder_Isaacs_Ch04_Commutators_Main_BaerMulGroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:18:33.661327+00:00
-- url     : https://prove2.me/theorems/c740b686-cc41-49fa-9649-40ce644d9e65
-- title:
--   Isaacs §4D: the Baer trick, construction layer (Lemma 4.37)
-- statement:
--   Formalizes the construction layer of the Baer trick of Isaacs, *Finite Group Theory*, Lemma 4.37 (pp. 141–144): square roots in odd-order groups, Baer addition, and the wrapper type carrying the resulting abelian group structure when $G$ has class at most $2$ and odd order, along with a transport API (`MulAut.toBaerMul`, `MonoidHom.toBaerMulLift`, `BaerMul.isPGroup_iff`, ...).
--
--   Main definitions: `sqrtOdd` ($x^{(|G|+1)/2}$, a square root in an odd-order group), `baerAdd` ($x+'y=x\,y\,\sqrt{[y,x]}$ for class at most $2$), and `BaerMul` (the type wrapper, with `toG`/`ofG` coercions and the multiplication instance given by `baerAdd`).
--
--   The bundle also proves 25 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/BaerMulGroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/BaerMulGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **Square root in groups with odd `Nat.card`**: `sqrtOdd x := x^((|G|+1)/2)`.
For `Odd (Nat.card G)`, `(sqrtOdd x)² = x` (`pow_card_eq_one'` で `x^(|G|+1) = x`). -/
noncomputable def sqrtOdd {G : Type*} [Group G] (x : G) : G :=
  x ^ ((Nat.card G + 1) / 2)

/-- **核補題**: `Odd (Nat.card G) ⇒ (sqrtOdd x)² = x`. -/
lemma sqrtOdd_sq {G : Type*} [Group G] (hOdd : Odd (Nat.card G)) (x : G) :
    (sqrtOdd x) ^ 2 = x := by
  unfold sqrtOdd
  rw [← pow_mul]
  have h_eq : (Nat.card G + 1) / 2 * 2 = Nat.card G + 1 := by
    obtain ⟨k, hk⟩ := hOdd; rw [hk]; omega
  rw [h_eq, pow_succ, pow_card_eq_one', one_mul]

@[simp] lemma sqrtOdd_one {G : Type*} [Group G] : sqrtOdd (1 : G) = 1 := by
  simp [sqrtOdd]

lemma sqrtOdd_inv {G : Type*} [Group G] (x : G) : sqrtOdd x⁻¹ = (sqrtOdd x)⁻¹ := by
  unfold sqrtOdd; rw [← inv_pow]

lemma sqrtOdd_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    sqrtOdd (x * y) = sqrtOdd x * sqrtOdd y := by
  unfold sqrtOdd; rw [Commute.mul_pow h]

lemma sqrtOdd_mem_subgroup {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    sqrtOdd x ∈ H := H.pow_mem hx _

/-- **Baer addition** for class ≤ 2 odd order groups: `x +' y := x * y * sqrtOdd ⁅y, x⁆`. -/
noncomputable def baerAdd {G : Type*} [Group G] (x y : G) : G := x * y * sqrtOdd ⁅y, x⁆

lemma baerAdd_def {G : Type*} [Group G] (x y : G) :
    baerAdd x y = x * y * sqrtOdd ⁅y, x⁆ := rfl

/-- **Lem 4.37 part (a) precursor**: If `x` and `y` commute, then `x +' y = x * y`
(since `⁅y, x⁆ = 1` and `sqrtOdd 1 = 1`). -/
lemma baerAdd_eq_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    baerAdd x y = x * y := by
  rw [baerAdd_def, (commutatorElement_eq_one_iff_commute (g₁ := y) (g₂ := x)).mpr h.symm,
      sqrtOdd_one, mul_one]

/-- Identity: `1 +' x = x`. -/
@[simp] lemma baerAdd_one_left {G : Type*} [Group G] (x : G) : baerAdd 1 x = x := by
  rw [baerAdd_def, one_mul, commutatorElement_one_right, sqrtOdd_one, mul_one]

/-- Identity: `x +' 1 = x`. -/
@[simp] lemma baerAdd_one_right {G : Type*} [Group G] (x : G) : baerAdd x 1 = x := by
  rw [baerAdd_def, mul_one, commutatorElement_one_left, sqrtOdd_one, mul_one]

/-- Inverse: `x +' x⁻¹ = 1`. -/
@[simp] lemma baerAdd_inv_right {G : Type*} [Group G] (x : G) : baerAdd x x⁻¹ = 1 := by
  have h1 : ⁅x⁻¹, x⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_left
  rw [baerAdd_def, mul_inv_cancel, h1, sqrtOdd_one, mul_one]

/-- Inverse: `x⁻¹ +' x = 1`. -/
@[simp] lemma baerAdd_inv_left {G : Type*} [Group G] (x : G) : baerAdd x⁻¹ x = 1 := by
  have h1 : ⁅x, x⁻¹⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_right
  rw [baerAdd_def, inv_mul_cancel, h1, sqrtOdd_one, mul_one]

/-- **Lem 4.37 commutativity**: `x +' y = y +' x` for class ≤ 2.

Derivation: `y +' x = y * x * sqrtOdd ⁅x, y⁆ = x * y * ⁅y, x⁆ * sqrtOdd ⁅x, y⁆`
(using `mul_comm_commutator_of_class_le_two`). Now `⁅x, y⁆⁻¹ = ⁅y, x⁆`, so
`sqrtOdd ⁅x, y⁆ = (sqrtOdd ⁅y, x⁆)⁻¹`. Combined:
`y +' x = x * y * ⁅y, x⁆ * (sqrtOdd ⁅y, x⁆)⁻¹ = x * y * sqrtOdd ⁅y, x⁆ = x +' y`
(using `(sqrtOdd ⁅y, x⁆)² = ⁅y, x⁆`). -/
lemma baerAdd_comm {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (hOdd : Odd (Nat.card G)) (x y : G) :
    baerAdd x y = baerAdd y x := by
  rw [baerAdd_def, baerAdd_def]
  -- Set S := sqrtOdd ⁅y, x⁆. Show x * y * S = y * x * sqrtOdd ⁅x, y⁆.
  set S : G := sqrtOdd ⁅y, x⁆ with hS_def
  have h_yx : y * x = x * y * ⁅y, x⁆ := mul_comm_commutator_of_class_le_two hC x y
  have h_inv : (sqrtOdd ⁅x, y⁆ : G) = S⁻¹ := by
    rw [hS_def, ← sqrtOdd_inv]
    congr 1
    exact (commutatorElement_inv y x).symm
  have h_sq : S * S = ⁅y, x⁆ := by
    have := sqrtOdd_sq hOdd (⁅y, x⁆ : G); rw [sq] at this; exact this
  -- Goal: x * y * S = y * x * sqrtOdd ⁅x, y⁆
  rw [h_inv, h_yx]
  -- Goal: x * y * S = x * y * ⁅y, x⁆ * S⁻¹
  rw [← h_sq]
  -- Goal: x * y * S = x * y * (S * S) * S⁻¹
  group

/-- `sqrtOdd` of a central element is central. -/
lemma sqrtOdd_central_of_central {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) : sqrtOdd z ∈ Subgroup.center G :=
  sqrtOdd_mem_subgroup hz

/-- Right-hom version of commutator in class ≤ 2: `⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆`.
Derived from left-hom + `commutatorElement_inv`. -/
lemma commutatorElement_mul_right_of_class_le_two {G : Type*} [Group G]
    (hC : _root_.commutator G ≤ Subgroup.center G) (z a b : G) :
    ⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆ := by
  -- ⁅z, a*b⁆ = ⁅a*b, z⁆⁻¹ = (⁅a, z⁆ * ⁅b, z⁆)⁻¹ = ⁅b, z⁆⁻¹ * ⁅a, z⁆⁻¹ = ⁅z, b⁆ * ⁅z, a⁆
  -- In class 2, ⁅z, a⁆ and ⁅z, b⁆ are central, so commute.
  have h_swap : (⁅z, a⁆ : G) * ⁅z, b⁆ = ⁅z, b⁆ * ⁅z, a⁆ := by
    have h_ca : ⁅z, a⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top z a)
    exact (Subgroup.mem_center_iff.mp h_ca _).symm
  have h_inv_ab : (⁅a * b, z⁆ : G)⁻¹ = ⁅z, a * b⁆ := commutatorElement_inv (a * b) z
  have h_left : (⁅a * b, z⁆ : G) = ⁅a, z⁆ * ⁅b, z⁆ :=
    commutatorElement_mul_left_of_class_le_two hC a b z
  rw [← h_inv_ab, h_left, mul_inv_rev, commutatorElement_inv, commutatorElement_inv, h_swap]

/-- **Lem 4.37 associativity**: `x +' (y +' z) = (x +' y) +' z` for class ≤ 2 + odd order.

**証明**: 両辺は `x * y * z * sqrtOdd ⁅z, y⁆ * sqrtOdd ⁅y, x⁆ * sqrtOdd ⁅z, x⁆` に等しい
(中心 commutators の積 は順序自由).

LHS = `x * (yz·S_{zy}) * S_{(yz·S_{zy}, x)}`:
- `⁅yz·S_{zy}, x⁆ = ⁅y, x⁆ * ⁅z, x⁆` (left hom + `⁅S_{zy}, x⁆ = 1`)
- `S_{⁅y,x⁆·⁅z,x⁆} = S_{y,x} * S_{z,x}` (sqrtOdd of central commuting product)

RHS = `(xy·S_{yx}) * z * S_{(z, xy·S_{yx})}`:
- `⁅z, xy·S_{yx}⁆ = ⁅z, x⁆ * ⁅z, y⁆` (right hom + `⁅z, S_{yx}⁆ = 1`)
- `z` moves past central `S_{yx}` ⇒ `xyz·S_{yx}·S_{⁅z,x⁆·⁅z,y⁆}`
- `S_{⁅z,x⁆·⁅z,y⁆} = S_{z,x} * S_{z,y}`. -/
lemma baerAdd_assoc {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (x y z : G) :
    baerAdd x (baerAdd y z) = baerAdd (baerAdd x y) z := by
  -- Notation: S_{ab} = sqrtOdd ⁅a, b⁆
  set Syz : G := sqrtOdd ⁅z, y⁆
  set Sxy : G := sqrtOdd ⁅y, x⁆
  set Sxz : G := sqrtOdd ⁅z, x⁆
  -- Centrality of all sqrtOdd-of-commutator elements
  have h_Sc_zy : Syz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z y))
  have h_Sc_yx : Sxy ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top y x))
  have h_Sc_zx : Sxz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z x))
  -- Helper: central element commutes with anything (Commute)
  have h_comm_central : ∀ {c : G}, c ∈ Subgroup.center G → ∀ a, Commute c a := fun hc a =>
    (Subgroup.mem_center_iff.mp hc a).symm
  have h_Comm_Syz : ∀ a, Commute Syz a := fun a => h_comm_central h_Sc_zy a
  have h_Comm_Sxy : ∀ a, Commute Sxy a := fun a => h_comm_central h_Sc_yx a
  -- LHS commutator computation: ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆
  have h_LHS_arg : ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    have h_yz_x : ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ :=
      commutatorElement_mul_left_of_class_le_two hC y z x
    have h_Syz_x : ⁅Syz, x⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := Syz) (g₂ := x)).mpr (h_Comm_Syz x)
    rw [commutatorElement_mul_left_of_class_le_two hC, h_yz_x, h_Syz_x, mul_one]
  -- RHS commutator computation: ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆
  have h_RHS_arg : ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
    have h_z_xy : ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ :=
      commutatorElement_mul_right_of_class_le_two hC z x y
    have h_z_Sxy : ⁅z, Sxy⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := z) (g₂ := Sxy)).mpr (h_Comm_Sxy z).symm
    rw [commutatorElement_mul_right_of_class_le_two hC z (x * y) Sxy, h_z_xy, h_z_Sxy, mul_one]
  -- Distribute sqrtOdd over products of central commutators
  -- sqrtOdd (⁅y, x⁆ * ⁅z, x⁆) = Sxy * Sxz (centrals commute)
  have h_C_xy : (⁅y, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  have h_C_zx : (⁅z, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z x)
  have h_split_LHS : sqrtOdd (⁅y, x⁆ * ⁅z, x⁆ : G) = Sxy * Sxz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_xy) ⁅z, x⁆)
  -- sqrtOdd (⁅z, x⁆ * ⁅z, y⁆) = Sxz * Syz
  have h_C_zy : (⁅z, y⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z y)
  have h_split_RHS : sqrtOdd (⁅z, x⁆ * ⁅z, y⁆ : G) = Sxz * Syz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_zx) ⁅z, y⁆)
  -- Compute LHS and RHS
  -- LHS = x * (y * z * Syz) * sqrtOdd ⁅y * z * Syz, x⁆
  --     = x * y * z * Syz * sqrtOdd (⁅y, x⁆ * ⁅z, x⁆)
  --     = x * y * z * Syz * Sxy * Sxz
  -- RHS = (x * y * Sxy) * z * sqrtOdd ⁅z, x * y * Sxy⁆
  --     = x * y * Sxy * z * sqrtOdd (⁅z, x⁆ * ⁅z, y⁆)
  --     = x * y * Sxy * z * Sxz * Syz
  --     = x * y * z * Sxy * Sxz * Syz  (Sxy commutes with z)
  -- LHS = RHS iff Syz * Sxy * Sxz = Sxy * Sxz * Syz, which holds because all centrals commute.
  rw [baerAdd_def, baerAdd_def, baerAdd_def, baerAdd_def, h_LHS_arg, h_RHS_arg,
      h_split_LHS, h_split_RHS]
  -- Goal: x * (y * z * Syz) * (Sxy * Sxz) = (x * y * Sxy) * z * (Sxz * Syz)
  -- Both sides normalize to `x * y * z * Sxy * Sxz * Syz` via commutativity
  -- of central elements (Syz, Sxy, Sxz).
  have h_Sxy_z := h_Comm_Sxy z
  have h_LHS_norm :
      x * (y * z * Syz) * (Sxy * Sxz) = x * y * z * Sxy * Sxz * Syz := by
    have hC : Commute Syz (Sxy * Sxz) := (h_Comm_Syz Sxy).mul_right (h_Comm_Syz Sxz)
    have h_rearrange :
        x * (y * z * Syz) * (Sxy * Sxz) = (x * y * z) * (Syz * (Sxy * Sxz)) := by group
    rw [h_rearrange, hC.eq]; group
  have h_RHS_norm :
      (x * y * Sxy) * z * (Sxz * Syz) = x * y * z * Sxy * Sxz * Syz := by
    have h_rearrange :
        (x * y * Sxy) * z * (Sxz * Syz) = x * y * (Sxy * z) * (Sxz * Syz) := by group
    rw [h_rearrange, h_Sxy_z.eq]; group
  rw [h_LHS_norm, h_RHS_norm]

/-- **Lem 4.37 part (c)**: Every group homomorphism (between equal-card groups) preserves
`baerAdd`: `f (baerAdd x y) = baerAdd (f x) (f y)`. -/
lemma baerAdd_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h_card : Nat.card G = Nat.card H) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) := by
  rw [baerAdd_def, baerAdd_def, map_mul, map_mul]
  congr 1
  -- f (sqrtOdd ⁅y, x⁆) = sqrtOdd (f ⁅y, x⁆) = sqrtOdd ⁅f y, f x⁆
  rw [sqrtOdd, sqrtOdd, h_card, map_pow, map_commutatorElement]

/-- **Lem 4.37 part (c) for MulEquiv** (Aut preservation): For `f : G ≃* G`,
`f (baerAdd x y) = baerAdd (f x) (f y)`. つまり multiplicative automorphism は
baerAdd を保存. -/
lemma baerAdd_mulEquiv_eq {G : Type*} [Group G] (f : G ≃* G) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) :=
  baerAdd_map_eq f.toMonoidHom rfl x y

/-- **Lem 4.37(b) inductive step** (仮定不要): `baerAdd (x^n) x = x^(n+1)`.

`x` と `x^n` は常に commute するので, `baerAdd x^n x = x^n * x * sqrtOdd ⁅x, x^n⁆ = x^n · x · 1 = x^{n+1}`.
これが `BaerMul G` の `npow_succ` フィールドに対応する. -/
lemma baerAdd_pow_self_eq_pow_succ {G : Type*} [Group G] (x : G) (n : ℕ) :
    baerAdd (x ^ n) x = x ^ (n + 1) := by
  have h_comm : Commute (x ^ n) x := Commute.pow_self x n
  rw [baerAdd_eq_mul_of_commute h_comm, ← pow_succ]

/-- **Baer trick type wrapper**: `BaerMul G := G` (定義的に同型).

`G` が奇数位数 + class ≤ 2 のときに `BaerMul G` 上に `baerAdd` を乗法とする `CommGroup` 構造を
与える (Lem 4.37). これにより mathlib の CommGroup 用 API (Cor 4.35 等) を `BaerMul G` に
直接適用できる.

Naming: 乗法的 wrapper として扱う ("multiplicative view of (G, +')"). -/
def BaerMul (G : Type*) : Type _ := G

namespace BaerMul

variable {G : Type*}

/-- Coercion `BaerMul G ≃ G` (identity at runtime). -/
def toG : BaerMul G ≃ G := Equiv.refl _

/-- Coercion `G ≃ BaerMul G` (identity at runtime). -/
def ofG : G ≃ BaerMul G := Equiv.refl _

@[simp] theorem toG_ofG (x : G) : toG (ofG x) = x := rfl

@[simp] theorem ofG_toG (x : BaerMul G) : ofG (toG x) = x := rfl

end BaerMul

/-- `Mul (BaerMul G) = baerAdd`. -/
noncomputable instance BaerMul.instMul {G : Type*} [Group G] : Mul (BaerMul G) where
  mul x y := BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))

/-- `1 : BaerMul G = ofG 1`. -/
instance BaerMul.instOne {G : Type*} [One G] : One (BaerMul G) where
  one := BaerMul.ofG 1

/-- `(·)⁻¹ : BaerMul G → BaerMul G` is the same as G's inverse (Lem 4.37 で `baerAdd x⁻¹ x = 1`). -/
instance BaerMul.instInv {G : Type*} [Inv G] : Inv (BaerMul G) where
  inv x := BaerMul.ofG (BaerMul.toG x)⁻¹

/-- **CommGroup instance for `BaerMul G`**: `G` が `Odd (Nat.card G)` + `commutator G ≤ Z(G)`
を満たすとき, `(BaerMul G, baerAdd, 1, ·⁻¹)` は可換群.

実装方針: 基本 `Mul / One / Inv` instance を別途与えて, ここでは **axiom フィールドのみ提供**.
`npow / zpow` フィールドはデフォルト (`npowRec` / `zpowRec`) を使用. `npowRec` は `*`
(我々の baerAdd) を `n` 回反復するので, BaerMul の pow = `baerAdd`-iterate.
G の `x^n` との一致は Lem 4.37(b) (`baerAdd_pow_self_eq_pow_succ`) 経由で別途証明. -/
noncomputable instance BaerMul.instCommGroup {G : Type*} [Group G]
    [hOdd : Fact (Odd (Nat.card G))]
    [hC : Fact (_root_.commutator G ≤ Subgroup.center G)] : CommGroup (BaerMul G) where
  mul_assoc x y z := by
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG
        y))))
        (BaerMul.toG z)) =
      BaerMul.ofG (baerAdd (BaerMul.toG x)
        (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG z)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG
      (baerAdd_assoc hC.out (BaerMul.toG x) (BaerMul.toG y) (BaerMul.toG z)).symm
  one_mul x := by
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG 1)) (BaerMul.toG x)) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_left]
    rfl
  mul_one x := by
    change BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG (BaerMul.ofG 1))) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_right]
    rfl
  mul_comm x y := by
    change BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y)) =
      BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG x))
    exact congr_arg BaerMul.ofG (baerAdd_comm hC.out hOdd.out _ _)
  inv_mul_cancel x := by
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (BaerMul.toG x)⁻¹)) (BaerMul.toG x)) =
      BaerMul.ofG 1
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_inv_left]

instance BaerMul.instFinite {G : Type*} [Finite G] : Finite (BaerMul G) :=
  inferInstanceAs (Finite G)

@[simp] lemma BaerMul.nat_card_eq {G : Type*} : Nat.card (BaerMul G) = Nat.card G := rfl

/-- **Lem 4.37(c) wrapped**: G の multiplicative automorphism は `BaerMul G` 上でも
multiplicative automorphism (= baerAdd 保存). 関数本体は同じ (恒等経由). -/
noncomputable def MulAut.toBaerMul {G : Type*} [Group G] (f : G ≃* G) :
    BaerMul G ≃* BaerMul G where
  toFun x := BaerMul.ofG (f (BaerMul.toG x))
  invFun x := BaerMul.ofG (f.symm (BaerMul.toG x))
  left_inv x := by
    change BaerMul.ofG (f.symm (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.symm_apply_apply]
    rfl
  right_inv x := by
    change BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (f.symm (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.apply_symm_apply]
    rfl
  map_mul' x y := by
    change BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))))) =
        BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))
          (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG y)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG (baerAdd_mulEquiv_eq f (BaerMul.toG x) (BaerMul.toG y))

/-- `MulAut.toBaerMul` は群準同型 (composition / 1 を保存). 下の `MonoidHom.toBaerMulLift`
を構成するために使う. -/
noncomputable def MulAut.toBaerMulHom {G : Type*} [Group G] :
    MulAut G →* MulAut (BaerMul G) where
  toFun f := MulAut.toBaerMul f
  map_one' := by
    ext x
    change BaerMul.ofG ((1 : MulAut G) (BaerMul.toG x)) = x
    change BaerMul.ofG (BaerMul.toG x) = x
    exact BaerMul.ofG_toG x
  map_mul' f g := by
    ext x
    change BaerMul.ofG ((f * g) (BaerMul.toG x)) =
        BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (g (BaerMul.toG x)))))
    simp only [BaerMul.toG_ofG]
    rfl

/-- φ : A →* MulAut G を BaerMul G への作用 φ' : A →* MulAut (BaerMul G) に lift する.
関数本体は同じ (Lem 4.37(c)). -/
noncomputable def MonoidHom.toBaerMulLift {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) : A →* MulAut (BaerMul G) :=
  MulAut.toBaerMulHom.comp φ

@[simp] lemma MonoidHom.toBaerMulLift_apply {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (a : A) (g : BaerMul G) :
    (MonoidHom.toBaerMulLift φ a) g = BaerMul.ofG ((φ a) (BaerMul.toG g)) := rfl

/-- **Lem 4.37(b) full form**: `BaerMul G` の自然冪 (baerAdd-iterate) = `G` の自然冪.
`npow_succ` の帰納で示す. -/
lemma BaerMul.npow_eq_pow {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = BaerMul.ofG ((BaerMul.toG x) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ, ih]
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG ((BaerMul.toG x) ^ k))) (BaerMul.toG x)) =
        BaerMul.ofG ((BaerMul.toG x) ^ (k + 1))
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_pow_self_eq_pow_succ]

/-- `BaerMul G` での `x^n = 1` ↔ `G` での `x^n = 1`. Cor 4.35 適用時の `g^p = 1` 翻訳に使用. -/
lemma BaerMul.pow_eq_one_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = 1 ↔ (BaerMul.toG x) ^ n = 1 := by
  rw [BaerMul.npow_eq_pow]
  change BaerMul.ofG ((BaerMul.toG x) ^ n) = BaerMul.ofG 1 ↔ (BaerMul.toG x) ^ n = 1
  exact BaerMul.ofG.apply_eq_iff_eq

/-- `IsPGroup p (BaerMul G) ↔ IsPGroup p G`. BaerMul の構造を経由しても p-群性は不変. -/
lemma BaerMul.isPGroup_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)] (p : ℕ) :
    IsPGroup p (BaerMul G) ↔ IsPGroup p G := by
  unfold IsPGroup
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, hn⟩ := h (BaerMul.ofG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff] at hn
    simpa [BaerMul.toG_ofG] using hn
  · obtain ⟨n, hn⟩ := h (BaerMul.toG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff]
    exact hn

end

end OddOrder.Isaacs.Ch04


