-- Prove2me | Definitions.Def_OddOrder_Mathlib_Subgroup
-- name    : OddOrder_Mathlib_Subgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:21.919239+00:00
-- url     : https://prove2.me/theorems/d61eaa10-819a-488d-87c4-86bd0ca0cf29
-- title:
--   Auxiliary `Subgroup` lemmas absent from Mathlib
-- statement:
--   General-purpose `Subgroup` lemmas missing from Mathlib, supporting mainly the Chermak–Delgado development but placed in the shared Mathlib-extension namespace as upstream candidates. Results include the classical $|HK|\cdot|H\cap K|=|H|\cdot|K|$, $H\le C_G(C_G(H))$ without commutativity assumptions, idempotency $C_G(C_G(C_G(H)))=C_G(H)$, $C_G(H\sqcup K)=C_G(H)\sqcap C_G(K)$, and that a finite quotient by a nontrivial subgroup has strictly smaller cardinality.
--
--   Definitions: `ptStabOfMulAut` (pointwise stabilizer in the acting group of a subgroup under a `MulAut` action), `fixedPointsOfMulAut` (the fixed-point subgroup of a `MulAut` action) and `powMonoidHom_range_characteristic` (the $p$-th power subgroup of a commutative group is characteristic).
--
--   The bundle also proves 23 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Mathlib/Subgroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/Subgroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Span.Basic

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Classical identity**: `|HK| · |H ∩ K| = |H| · |K|` for subgroups `H, K` of a
group `G`, where `HK ⊆ G` is the set product (not generally a subgroup).
無限群でも両辺はゼロで成立する.

mathlib v4.29.1 不在 ── 関連 `index_inf_le`, `relIndex_inf_mul_relIndex` は部分対応のみ.

**証明戦略**: `H × K → HK` の準同型 (の corestriction) は H ⊓ K 加群作用で fiber が
`|H ∩ K|` と分かる. mathlib 流には:
1. `card_mul_eq_card_subgroup_mul_card_quotient` で `|HK| = |K| · |(↑H).image mk|`.
2. `H ⧸ K.subgroupOf H ≃ (↑H).image mk` (本証明内で構成).
3. Lagrange `|H| = |H ⧸ K.subgroupOf H| · |K.subgroupOf H|`.
4. `K.subgroupOf H = (H ⊓ K).subgroupOf H`, `subgroupOfEquivOfLe` で `≃ H ⊓ K`. -/
theorem card_HK_mul_card_inf_eq_card_mul_card (H K : Subgroup G) :
    Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  classical
  -- Step 1: `|HK| = |K| · |(↑H).image mk|` (mathlib 既存)
  rw [card_mul_eq_card_subgroup_mul_card_quotient K (↑H : Set G)]
  -- Step 2: 補助 — corestricted projection `f : H → img` は全射
  set img := (↑H : Set G).image (QuotientGroup.mk : G → G ⧸ K) with himg
  let f : H → ↥img := fun h => ⟨QuotientGroup.mk h.val, h.val, h.property, rfl⟩
  have hf_surj : Function.Surjective f := by
    rintro ⟨_, h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  -- Step 3: Setoid.ker f は QuotientGroup.leftRel (K.subgroupOf H) と関係が一致
  have hsetoid_rel :
      ∀ h₁ h₂ : H,
        (QuotientGroup.leftRel (K.subgroupOf H)) h₁ h₂ ↔ (Setoid.ker f) h₁ h₂ := by
    intro h₁ h₂
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf, Setoid.ker_def]
    constructor
    · intro hrel
      apply Subtype.ext
      change QuotientGroup.mk h₁.val = QuotientGroup.mk h₂.val
      rw [QuotientGroup.eq]
      exact hrel
    · intro hrel
      have : QuotientGroup.mk h₁.val = (QuotientGroup.mk h₂.val : G ⧸ K) :=
        congrArg Subtype.val hrel
      rwa [QuotientGroup.eq] at this
  -- Step 4: H ⧸ K.subgroupOf H ≃ ↥img (合成)
  have hquot_img_card : Nat.card (H ⧸ K.subgroupOf H) = Nat.card ↥img :=
    (Nat.card_congr (Quotient.congrRight hsetoid_rel)).trans
      (Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf_surj))
  -- Step 5: Lagrange in H
  have hH_split : Nat.card H = Nat.card (H ⧸ K.subgroupOf H) * Nat.card ↥(K.subgroupOf H) :=
    (K.subgroupOf H).card_eq_card_quotient_mul_card_subgroup
  -- Step 6: `K.subgroupOf H = (H ⊓ K).subgroupOf H`, `subgroupOfEquivOfLe` で
  -- `|K.subgroupOf H| = |H ⊓ K|`
  have hKHinf : K.subgroupOf H = (H ⊓ K).subgroupOf H := by
    ext x
    simp only [mem_subgroupOf, mem_inf, and_iff_right x.property]
  have hker_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [hKHinf]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : H ⊓ K ≤ H)).toEquiv
  -- Step 7: 合算
  rw [hquot_img_card, hker_card] at hH_split
  -- hH_split : Nat.card H = Nat.card ↥img * Nat.card ↥(H ⊓ K)
  -- Goal: Nat.card K * Nat.card ↥img * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K
  rw [mul_assoc, ← hH_split, Nat.mul_comm]

/-- `H ≤ C_G(C_G(H))` for any subgroup `H` ── classical Galois connection (`le_centralizer_iff`).

mathlib v4.29.1 不在: 既存 `Subgroup.le_centralizer` は `IsMulCommutative H` 仮定が必要だが,
本補題は仮定なし. `Subgroup.closure_le_centralizer_centralizer` を `H = closure ↑H` に適用. -/
theorem le_centralizer_centralizer (H : Subgroup G) :
    H ≤ centralizer (centralizer (H : Set G) : Set G) := by
  conv_lhs => rw [← H.closure_eq]
  exact closure_le_centralizer_centralizer _

/-- `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`.

mathlib v4.29.1 では `Subalgebra` 版 (`Algebra/Subalgebra/Centralizer.lean:19`) のみで,
`Subgroup` 版は不在. `Set.centralizer_union` + `Subgroup.centralizer_closure` から従う. -/
theorem centralizer_sup (H K : Subgroup G) :
    centralizer ((H ⊔ K : Subgroup G) : Set G)
      = centralizer (H : Set G) ⊓ centralizer (K : Set G) := by
  have hHK : (H ⊔ K : Subgroup G) = closure ((H : Set G) ∪ (K : Set G)) := by
    rw [closure_union, closure_eq, closure_eq]
  rw [hHK, centralizer_closure]
  ext g
  simp only [mem_centralizer_iff, Set.mem_union, mem_inf, or_imp, forall_and]

/-- **`MulAut` 作用の部分群 `J` の各点固定化群** (作用する側 `A` の中で取る): `φ a` が `J` を
元ごとに固定するような `a ∈ A` 全体.  `fixedPointsOfMulAut` (固定される側 `G` の中で取る) の双対.

下流: Peterfalvi (9.7)(a) — ブロック `H_i` の各点固定化群が `C_U(H_i)`, その指数が書籍の `a`
(issue 0152). -/
def ptStabOfMulAut {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) (J : Subgroup G) :
    Subgroup A where
  carrier := {a | ∀ x ∈ J, (φ a) x = x}
  one_mem' := fun x _ => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb x hx => by
    rw [map_mul]
    change (φ a) ((φ b) x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    rw [map_inv]
    change (φ a).symm x = x
    exact (MulEquiv.symm_apply_eq _).mpr (ha x hx).symm

@[simp]
theorem mem_ptStabOfMulAut {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {J : Subgroup G} {a : A} :
    a ∈ ptStabOfMulAut φ J ↔ ∀ x ∈ J, (φ a) x = x := Iff.rfl

/-- **`MulAut` 作用の固定点部分群**: `φ : A →* MulAut G` の下で `∀ a, (φ a) g = g` を
満たす要素全体. mathlib `MulAction.fixedPoints` は Set だが, MulAut 作用の場合は
group 構造を持つので Subgroup として bundle.

下流: Isaacs Lem 4.32 後半 (P p-group on G p-group ⇒ fixedPoints > 1) で使用. -/
def fixedPointsOfMulAut {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    Subgroup G where
  carrier := {g | ∀ a : A, (φ a) g = g}
  one_mem' := fun a => map_one (φ a)
  mul_mem' := fun {x y} hx hy a => by rw [map_mul, hx, hy]
  inv_mem' := fun {x} hx a => by rw [map_inv, hx]

@[simp]
theorem mem_fixedPointsOfMulAut {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {g : G} :
    g ∈ fixedPointsOfMulAut φ ↔ ∀ a : A, (φ a) g = g := Iff.rfl

/-- 自明作用 (`1 : A →* MulAut G`) の固定点は `⊤` (全要素が固定). -/
@[simp]
theorem fixedPointsOfMulAut_one_eq_top {A G : Type*} [Group A] [Group G] :
    fixedPointsOfMulAut (1 : A →* MulAut G) = ⊤ := by
  ext g
  simp only [mem_fixedPointsOfMulAut, Subgroup.mem_top, iff_true]
  intro a
  rfl

/-- **`Subgroup.centralizer` の bijective hom 像**: bijective `f : G →* G'` で
`(centralizer s).map f = centralizer (f '' s)`. mathlib v4.29.1 では `≤` 方向のみ
(`map_centralizer_le_centralizer_image`). -/
theorem map_centralizer_eq_of_bijective {G G' : Type*} [Group G] [Group G']
    (s : Set G) (f : G →* G') (hf : Function.Bijective f) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image s f)
  intro y hy
  obtain ⟨g, rfl⟩ := hf.surjective y
  refine ⟨g, ?_, rfl⟩
  change g ∈ Subgroup.centralizer s
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hfx : f x ∈ f '' s := ⟨x, hx, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp hy (f x) hfx
  rw [← map_mul, ← map_mul] at this
  exact hf.injective this

/-- **`p`-th power subgroup is characteristic** in CommGroup: for any `n : ℕ`, the range
of `powMonoidHom n` (= `{x^n : x : M}` as subgroup of M) is characteristic in M.

mathlib v4.29.1 不在の generic lemma. Lucchini K=⊥ (M abelian case で `φ(M) ⊴ G` を
`characteristic in normal` 経由で得る) で使用. -/
instance powMonoidHom_range_characteristic
    {M : Type*} [CommGroup M] (n : ℕ) :
    ((powMonoidHom (α := M) n).range).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hφx
    obtain ⟨y, hy⟩ := hφx
    refine ⟨φ.symm y, ?_⟩
    have : φ ((φ.symm y) ^ n) = φ x := by
      rw [map_pow, MulEquiv.apply_symm_apply]
      exact hy
    exact φ.injective this
  · intro hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨φ y, ?_⟩
    change (φ y) ^ n = φ x
    rw [← map_pow]
    exact congrArg φ hy

/-- **`Nat.card (↥K ⧸ N.subgroupOf K) = Nat.card (K.map qmk_N)`** via first iso.
`f := (QuotientGroup.mk' N).comp K.subtype` has `ker = N.subgroupOf K`, `range = K.map qmk_N`.
`quotientKerEquivRange` gives the equiv, take Nat.card_congr. -/
theorem nat_card_quotient_subgroupOf_eq_card_map {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (K : Subgroup G) :
    Nat.card ((↥K) ⧸ (N.subgroupOf K)) = Nat.card (K.map (QuotientGroup.mk' N)) := by
  let f0 : ↥K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hker : f0.ker = N.subgroupOf K := by
    ext ⟨x, hx⟩
    simp only [f0, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f0.range = K.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, hxy⟩
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, hxy⟩
  have hEq : Nat.card ((↥K) ⧸ f0.ker) = Nat.card ↥(f0.range) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f0).toEquiv
  -- Substitute the equal subgroups.
  conv_lhs => rw [show N.subgroupOf K = f0.ker from hker.symm]
  conv_rhs => rw [show K.map (QuotientGroup.mk' N) = f0.range from hrange.symm]
  exact hEq

/-- Mapping `B ≤ A ≤ H` through `H.subtype` commutes with viewing `B` as a subgroup
of `A`. -/
theorem subgroupOf_map_subtype_eq_map_subgroupOf {H : Subgroup G} {A B : Subgroup H}
    (hBA : B ≤ A) :
    (B.subgroupOf A).map
        (Subgroup.equivMapOfInjective A H.subtype H.subtype_injective).toMonoidHom =
      (B.map H.subtype).subgroupOf (A.map H.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hyB, rfl⟩
    rw [mem_subgroupOf]
    exact ⟨(y : H), hyB, rfl⟩
  · intro hx
    rw [mem_subgroupOf] at hx
    rcases hx with ⟨y, hyB, hyx⟩
    refine ⟨⟨y, hBA hyB⟩, hyB, ?_⟩
    apply Subtype.ext
    exact hyx

/-- Normality of `B.subgroupOf A` is preserved when `B ≤ A ≤ H` is mapped through
`H.subtype`. -/
theorem normal_subgroupOf_map_subtype {H : Subgroup G} {A B : Subgroup H}
    (hBA : B ≤ A) [((B.subgroupOf A) : Subgroup A).Normal] :
    ((B.map H.subtype).subgroupOf (A.map H.subtype)).Normal := by
  let eA : A ≃* A.map H.subtype :=
    Subgroup.equivMapOfInjective A H.subtype H.subtype_injective
  have hmap :
      (B.subgroupOf A).map eA.toMonoidHom =
        (B.map H.subtype).subgroupOf (A.map H.subtype) := by
    simpa [eA] using subgroupOf_map_subtype_eq_map_subgroupOf (H := H) hBA
  rw [← hmap]
  exact (inferInstance : ((B.subgroupOf A) : Subgroup A).Normal).map
    eA.toMonoidHom eA.surjective

/-- Mapping `B ≤ A ≤ H` through `H.subtype` preserves the cardinality of the
quotient layer `A/B`. -/
theorem nat_card_quotient_subgroupOf_map_subtype_eq {H : Subgroup G}
    {A B : Subgroup H} (hBA : B ≤ A)
    [((B.subgroupOf A) : Subgroup A).Normal] :
    Nat.card
        ((A.map H.subtype) ⧸ ((B.map H.subtype).subgroupOf (A.map H.subtype))) =
      Nat.card (A ⧸ B.subgroupOf A) := by
  let eA : A ≃* A.map H.subtype :=
    Subgroup.equivMapOfInjective A H.subtype H.subtype_injective
  have hmap :
      (B.subgroupOf A).map eA.toMonoidHom =
        (B.map H.subtype).subgroupOf (A.map H.subtype) := by
    simpa [eA] using subgroupOf_map_subtype_eq_map_subgroupOf (H := H) hBA
  have : ((B.map H.subtype).subgroupOf (A.map H.subtype)).Normal :=
    normal_subgroupOf_map_subtype (H := H) hBA
  exact (Nat.card_congr
    (QuotientGroup.congr (B.subgroupOf A)
      ((B.map H.subtype).subgroupOf (A.map H.subtype)) eA hmap).toEquiv).symm

/-- Quotienting a subgroup by the ambient bottom subgroup preserves cardinality. -/
theorem nat_card_quotient_bot_subgroupOf_eq {H : Subgroup G} :
    Nat.card (H ⧸ ((⊥ : Subgroup G).subgroupOf H)) = Nat.card H := by
  rw [bot_subgroupOf]
  exact Nat.card_congr QuotientGroup.quotientBot.toEquiv

/-- A subgroup `V` complementing the normal `N` in `G` (`N ⊓ V = ⊥`, `N ⊔ V = ⊤`) has
`|N| * |V| = |G|`. -/
theorem card_mul_card_of_complement_normal {G : Type*} [Group G] [Finite G] {N V : Subgroup G}
    [N.Normal] (hinf : N ⊓ V = ⊥) (hsup : N ⊔ V = ⊤) :
    Nat.card N * Nat.card V = Nat.card G :=
  (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
    (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])).card_mul_card

/-- A finite quotient by a nontrivial subgroup has strictly smaller cardinality.

This is the induction/minimal-counterexample termination bridge used repeatedly when passing
from `G` to `G/K`. Normality is intentionally not required for the cardinal statement. -/
theorem card_quotient_lt_of_ne_bot {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hK : K ≠ ⊥) :
    Nat.card (G ⧸ K) < Nat.card G := by
  have h_eq : Nat.card (G ⧸ K) * Nat.card K = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup K).symm
  have hK_gt : 1 < Nat.card K := (Subgroup.one_lt_card_iff_ne_bot K).mpr hK
  have hQ_pos : 0 < Nat.card (G ⧸ K) := Nat.card_pos
  calc
    Nat.card (G ⧸ K) = Nat.card (G ⧸ K) * 1 := (mul_one _).symm
    _ < Nat.card (G ⧸ K) * Nat.card K :=
      (Nat.mul_lt_mul_left hQ_pos).mpr hK_gt
    _ = Nat.card G := h_eq

/-- **`H` is normal when complement of normal `N` with elementwise commute**:
`N ⊴ G`, `H` complement of `N`, `∀ n ∈ N h ∈ H, n*h = h*n` ⇒ `H ⊴ G`.

直積構造 `G ≃ N × H` を導出する古典的事実. Hall-Higman 3.21 case π' で
`H' ⊴ K` 導出に使用. -/
theorem normal_complement_of_commute {G : Type*} [Group G]
    {N H : Subgroup G} [N.Normal] (hCompl : N.IsComplement' H)
    (hCommute : ∀ n ∈ N, ∀ h ∈ H, n * h = h * n) :
    H.Normal := by
  refine ⟨fun h hh g => ?_⟩
  have hsurj : Function.Surjective (fun x : N × H => (x.1 : G) * x.2) := hCompl.surjective
  obtain ⟨⟨⟨n, hn⟩, ⟨h', hh'⟩⟩, hg⟩ := hsurj g
  simp only at hg
  rw [← hg]
  have hy_in_H : h' * h * h'⁻¹ ∈ H := H.mul_mem (H.mul_mem hh' hh) (H.inv_mem hh')
  have heq : (n * h') * h * (n * h')⁻¹ = h' * h * h'⁻¹ := by
    calc (n * h') * h * (n * h')⁻¹
        = n * (h' * h * h'⁻¹) * n⁻¹ := by group
      _ = (h' * h * h'⁻¹) * n * n⁻¹ := by
          rw [hCommute n hn (h' * h * h'⁻¹) hy_in_H]
      _ = h' * h * h'⁻¹ := by group
  rw [heq]
  exact hy_in_H

/-- **comap of subgroup of `C.map qmk` is ≤ C** when `B ≤ C` (`B = ker qmk`).
`K_GB ≤ C.map qmk ⇒ K_GB.comap qmk ≤ B ⊔ C = C`. -/
theorem comap_le_of_le_map_quotient {G : Type*} [Group G]
    {B C : Subgroup G} [B.Normal] (hBC : B ≤ C)
    {K_GB : Subgroup (G ⧸ B)} (hK : K_GB ≤ C.map (QuotientGroup.mk' B)) :
    K_GB.comap (QuotientGroup.mk' B) ≤ C := by
  calc K_GB.comap (QuotientGroup.mk' B)
      ≤ (C.map (QuotientGroup.mk' B)).comap (QuotientGroup.mk' B) :=
        Subgroup.comap_mono hK
    _ = B ⊔ C := QuotientGroup.comap_map_mk' B C
    _ = C := by rw [sup_comm]; exact sup_of_le_left hBC

/-- **`G ⧸ N` nontrivial iff `N ≠ ⊤`** (有限 G で): mathlib `Subgroup.index_eq_one`
+ `Finite.one_lt_card_iff_nontrivial` を結合.

用途: Hall-Higman 3.21 で C/B nontrivial を `B < C` から導出. -/
theorem nontrivial_quotient_of_ne_top {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (h : N ≠ ⊤) : Nontrivial (G ⧸ N) := by
  rw [← Finite.one_lt_card_iff_nontrivial]
  change 1 < N.index
  exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    ⟨Subgroup.index_ne_zero_of_finite, mt Subgroup.index_eq_one.mp h⟩

/-- **Dedekind / modular law for subgroups** (with normality of one summand).
`E, A, M ≤ G`, `E ⊴ G`, `E ≤ M` ⇒ `M ⊓ (E ⊔ A) = E ⊔ (M ⊓ A)`.

mathlib v4.29.1 では `IsModularLattice (Subgroup G)` instance は `[CommGroup G]` 限定で,
非可換群版は不在 (実際は片方正規で modular).

**用途**: Lucchini Thm 2.20 (K=⊥ case) で `M ⊆ AE ⇒ M = E(A ∩ M)` を導出. -/
theorem inf_sup_eq_sup_inf_of_normal_of_le
    {E A M : Subgroup G} [E.Normal] (hEM : E ≤ M) :
    M ⊓ (E ⊔ A) = E ⊔ (M ⊓ A) := by
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ M := hx.1
    have hxEA : x ∈ E ⊔ A := hx.2
    obtain ⟨e, he, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxEA
    -- x = e * a, a = e⁻¹ * x ∈ M.
    have ha_in_M : a ∈ M := by
      have : e⁻¹ * (e * a) ∈ M := M.mul_mem (M.inv_mem (hEM he)) hxM
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem_sup he ⟨ha_in_M, ha⟩
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨hEM hx, Subgroup.mem_sup_left hx⟩
    · intro x ⟨hxM, hxA⟩
      exact ⟨hxM, Subgroup.mem_sup_right hxA⟩

/-- **Dedekind 直接形** (`M ⊆ E ⊔ A` 仮定下): `E, A, M ≤ G`, `E ⊴ G`, `E ≤ M ≤ E ⊔ A`
⇒ `M = E ⊔ (M ⊓ A)`.

Lucchini Thm 2.20 (K=⊥ case) で **直接** 使う形: `M ⊆ AE ⇒ M = E·(A ∩ M) = E ⊔ B`
where `B = A ⊓ M`. `inf_sup_eq_sup_inf_of_normal_of_le` + `inf_eq_left.mpr hMle` で
合成. -/
theorem eq_sup_inf_of_le_sup_of_normal_of_le
    {E A M : Subgroup G} [E.Normal] (hEM : E ≤ M) (hMle : M ≤ E ⊔ A) :
    M = E ⊔ (M ⊓ A) := by
  rw [← inf_sup_eq_sup_inf_of_normal_of_le hEM]
  exact (inf_eq_left.mpr hMle).symm

/-- **Dedekind / modular law, normalizer form**: if `W ≤ L`, `A ⊓ L = ⊥`, and `A` normalizes `W`,
then `(W ⊔ A) ⊓ L = W`.  Unlike `inf_sup_eq_sup_inf_of_normal_of_le`, this needs only that `A`
*normalizes* `W` (so `W` is normal in `W ⊔ A`), not global normality — fitting the BG step 3(ii)
situation `(Q₁ ⊔ D) ⊓ Q = Q₁` (`Q₁ ≤ Q`, `D ⊓ Q = ⊥`, `D ≤ N_G(Q₁)`).  The noncommutative case is
handled via the product representation `W·A` of `W ⊔ A`. -/
theorem inf_sup_eq_of_le_normalizer_of_inf_eq_bot
    {W A L : Subgroup G} (hW_le : W ≤ L) (hA_inf : A ⊓ L = ⊥)
    (hAnorm : A ≤ Subgroup.normalizer (W : Set G)) :
    (W ⊔ A) ⊓ L = W := by
  apply le_antisymm
  · intro x ⟨hxWA, hxL⟩
    have : (W.subgroupOf (A ⊔ W)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hAnorm
    have hx_AW : x ∈ A ⊔ W := by rw [sup_comm]; exact hxWA
    have hmem : (⟨x, hx_AW⟩ : ↥(A ⊔ W)) ∈ (W.subgroupOf (A ⊔ W)) ⊔ (A.subgroupOf (A ⊔ W)) := by
      rw [← Subgroup.subgroupOf_sup (le_sup_right) (le_sup_left), sup_comm W A,
        Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨⟨w, hw_AW⟩, hw, ⟨a, ha_AW⟩, ha, heq⟩ := hmem
    have hxeq : x = w * a := congrArg (Subtype.val) heq |>.symm
    have ha_L : a ∈ L := by
      have : w⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hW_le hw)) hxL
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have ha_one : a = 1 := by
      have : a ∈ A ⊓ L := ⟨ha, ha_L⟩
      rw [hA_inf, Subgroup.mem_bot] at this; exact this
    rw [hxeq, ha_one, mul_one]; exact hw
  · exact le_inf le_sup_left hW_le

/-- **A subgroup coprime to the index of a normal subgroup lies inside it.**  If `H ⊴ G` and the
order of `S ≤ G` is coprime to `[G : H]`, then `S ≤ H`.  (Applied to a normal Hall `H`: any
subgroup of order coprime to `[G : H]` — e.g. any `π(H)`-subgroup — is contained in `H`.)

The image `S ↦ SH/H ≤ G/H` has order dividing both `|S|` and `[G : H] = |G/H|`, hence trivial by
coprimality, so `S ≤ ker(G → G/H) = H`. -/
theorem le_of_coprime_card_index_of_normal {G : Type*} [Group G] [Finite G]
    {H S : Subgroup G} [H.Normal] (hcop : Nat.Coprime (Nat.card S) H.index) :
    S ≤ H := by
  have h1 : Nat.card (S.map (QuotientGroup.mk' H)) ∣ Nat.card S :=
    S.card_map_dvd (QuotientGroup.mk' H)
  have h2 : Nat.card (S.map (QuotientGroup.mk' H)) ∣ H.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hbot : S.map (QuotientGroup.mk' H) = ⊥ :=
    Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2))
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

/-- **Membership in the ambient image of a center**: `z ∈ Z(P).map P.subtype` iff `z ∈ P` and `z`
commutes with every element of `P`. -/
theorem mem_center_map_subtype_iff {G : Type*} [Group G] {P : Subgroup G} {z : G} :
    z ∈ (Subgroup.center ↥P).map P.subtype ↔ z ∈ P ∧ ∀ w ∈ P, w * z = z * w := by
  constructor
  · rintro ⟨z', hz', rfl⟩
    exact ⟨z'.2, fun w hw =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz') ⟨w, hw⟩)⟩
  · rintro ⟨hzP, hcomm⟩
    exact ⟨⟨z, hzP⟩, Subgroup.mem_center_iff.mpr fun w => Subtype.ext (hcomm w w.2), rfl⟩

/-- **An element normalizing `P` normalizes the ambient image of its center**
`Z(P) = (Subgroup.center ↥P).map P.subtype`: conjugation by `g` preserves both membership in `P`
and commutation with every element of `P`. -/
theorem mem_normalizer_center_map_of_mem_normalizer {G : Type*} [Group G] {P : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro z
  simp only [SetLike.mem_coe] at hg ⊢
  rw [mem_center_map_subtype_iff, mem_center_map_subtype_iff]
  constructor
  · rintro ⟨hzP, hcomm⟩
    refine ⟨(hg z).mp hzP, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ P := by
      refine (hg (g⁻¹ * w * g)).mpr ?_
      have heq : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
      rwa [heq]
    calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm _ hw']
      _ = g * z * g⁻¹ * w := by group
  · rintro ⟨hzP', hcomm⟩
    refine ⟨(hg z).mpr hzP', fun w hw => ?_⟩
    have hw' : g * w * g⁻¹ ∈ P := (hg w).mp hw
    calc w * z = g⁻¹ * ((g * w * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * w * g⁻¹)) * g := by rw [hcomm _ hw']
      _ = z * w := by group

end Subgroup


