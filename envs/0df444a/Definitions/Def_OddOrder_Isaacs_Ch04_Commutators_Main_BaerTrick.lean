-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
-- name    : OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:21:37.402044+00:00
-- url     : https://prove2.me/theorems/973b1134-5dfe-4727-bcbc-7029c2761046
-- title:
--   Isaacs §4D (second part): the Baer trick and applications
-- statement:
--   The second half of the formalization of the Baer trick (Lemma 4.37) and its applications in Isaacs, *Finite Group Theory*, §4D (pp. 141–146). The only definitions are the factor inclusions of a direct product: `prodLeftHom` ($P\to P\times Q$) and `prodRightHom` ($Q\to P\times Q$).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/BaerTrick.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/BaerTrick.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerMulGroup

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **系 of Lem 4.28**: `A` が `actionCommutator φ` (= `[G, A]`) 上で trivial 作用するとき,
coprime + (A or G solvable) 仮定下では `actionCommutator φ = ⊥` (= A trivial on whole G).

**証明**: Lem 4.28 で G = C_G(A) · [G, A]. 各 g = c * x で `c ∈ C_G(A)` ⇒ `(φ a) c = c`,
`x ∈ [G, A]` + 仮定 ⇒ `(φ a) x = x`. 故に `(φ a) g = (φ a)(c·x) = c·x = g`.

Thm 4.36 induction の `[G, A] < G` ケースで使用 (IH ⇒ A trivial on [G, A] ⇒ A trivial on G). -/
theorem actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    (h_triv : ∀ a : A, ∀ h ∈ actionCommutator φ, (φ a) h = h) :
    actionCommutator φ = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_top : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
    rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_right] at h_top
  obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
  -- h_eq : c * x = g, hc_fix : c ∈ fixedPoints, hx_ac : x ∈ actionCommutator
  rw [← h_eq, map_mul, hc_fix a, h_triv a x hx_ac]

/-- **Isaacs Thm 4.36 (class ≤ 2 case)** ⭐: A acts on p-群 G of class ≤ 2 (p > 2),
A is p'-group, A fixes every order-p element of G ⇒ A trivial on G.

Baer trick で `BaerMul G` を可換群として扱い, Cor 4.35 を適用. これが Thm 4.36 の核.

`hp_odd : p ≠ 2` から `Odd p` → `Odd (p^k)` → `Odd (Nat.card G)`. `hC : class ≤ 2` を
`Fact` 化して `BaerMul.instCommGroup` を呼び出し可能に. -/
theorem actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (hC : _root_.commutator G ≤ Subgroup.center G)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Set up Fact (Odd (Nat.card G))
  have hOdd_p : Odd p := hp.out.odd_of_ne_two hp_odd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
  have hOdd_card : Odd (Nat.card G) := by rw [hk]; exact hOdd_p.pow
  have : Fact (Odd (Nat.card G)) := ⟨hOdd_card⟩
  have : Fact (_root_.commutator G ≤ Subgroup.center G) := ⟨hC⟩
  -- φ' : A →* MulAut (BaerMul G)
  set φ' : A →* MulAut (BaerMul G) := MonoidHom.toBaerMulLift φ with hφ'
  -- IsPGroup p (BaerMul G)
  have hG' : IsPGroup p (BaerMul G) := (BaerMul.isPGroup_iff p).mpr hG
  -- h_fix translated to BaerMul G
  have h_fix' : ∀ g : BaerMul G, g ^ p = 1 → ∀ a : A, (φ' a) g = g := by
    intro g hg a
    have hg_G : (BaerMul.toG g) ^ p = 1 := (BaerMul.pow_eq_one_iff g p).mp hg
    have h_fixed : (φ a) (BaerMul.toG g) = BaerMul.toG g := h_fix _ hg_G a
    change BaerMul.ofG ((φ a) (BaerMul.toG g)) = g
    rw [h_fixed]
    exact BaerMul.ofG_toG g
  -- Apply Cor 4.35 to BaerMul G
  have h_bot_baer : actionCommutator φ' = ⊥ :=
    actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p φ' hG' hA_p' h_fix'
  -- Translate back to G via iff
  rw [actionCommutator_eq_bot_iff_acts_trivially] at h_bot_baer
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_act := h_bot_baer a (BaerMul.ofG g)
  -- h_act : (φ' a) (ofG g) = ofG g
  -- Unfold φ': (φ' a) (ofG g) = ofG ((φ a) (toG (ofG g))) = ofG ((φ a) g)
  -- So: ofG ((φ a) g) = ofG g, hence (φ a) g = g by injectivity
  have h_eq : BaerMul.ofG ((φ a) g) = BaerMul.ofG g := by
    have hkey : (φ' a) (BaerMul.ofG g) = BaerMul.ofG ((φ a) g) := by
      change BaerMul.ofG ((φ a) (BaerMul.toG (BaerMul.ofG g))) = BaerMul.ofG ((φ a) g)
      rw [BaerMul.toG_ofG]
    rw [← hkey]
    exact h_act
  exact BaerMul.ofG.injective h_eq

/-- **強帰納法版** (`Nat.card G ≤ n` パラメータ化). Thm 4.36 本体の補助. -/
private theorem isaacs_thm_4_36_aux {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hA_p' : ¬ p ∣ Nat.card A) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : A →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g),
    Nat.card G ≤ n → actionCommutator φ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    -- Case: |G| ≤ m, apply IH
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    have h_card_G : Nat.card G = m + 1 := le_antisymm h_le h_ge
    -- Subcase: G trivial
    by_cases hG_triv : Nontrivial G
    swap
    · have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_triv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro a g
      exact Subsingleton.elim _ _
    -- G nontrivial setup
    have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
      rw [hk]
      exact (Nat.Coprime.pow_right k (Nat.coprime_comm.mp
        (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
    have hG_nilp : Group.IsNilpotent G := hG.isNilpotent
    have hG_solv : Group.IsSolvable G := IsNilpotent.to_isSolvable
    have hSolv : Group.IsSolvable A ∨ Group.IsSolvable G := Or.inr hG_solv
    -- 補助: H ≠ ⊤ + Finite G ⇒ Nat.card ↥H < Nat.card G
    have card_lt_of_ne_top : ∀ {H : Subgroup G}, H ≠ ⊤ → Nat.card ↥H < Nat.card G := by
      intro H h_ne
      have h_dvd : Nat.card ↥H ∣ Nat.card G :=
        ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
      have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
        h_ne (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le' h_ne'
    -- Case分け: [G, A] < ⊤ vs ⊤
    by_cases h_AC_top : actionCommutator φ = ⊤
    swap
    · -- [G, A] < ⊤: IH を actionCommutator に適用
      set H : Subgroup G := actionCommutator φ
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let φ_H : A →* MulAut ↥H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have h_H_card_lt : Nat.card ↥H < Nat.card G := card_lt_of_ne_top h_AC_top
      have hH_pgrp : IsPGroup p ↥H := hG.to_subgroup H
      have h_fix_H : ∀ h : ↥H, h ^ p = 1 → ∀ a : A, (φ_H a) h = h := by
        intro h hh_pow a
        apply Subtype.ext
        change (φ a) h.val = h.val
        apply h_fix
        have := congr_arg (Subtype.val : ↥H → G) hh_pow
        simpa using this
      have h_IH_H := IH φ_H hH_pgrp h_fix_H
        (Nat.le_of_lt_succ (h_H_card_lt.trans_le h_le))
      have h_triv : ∀ a : A, ∀ x ∈ H, (φ a) x = x := by
        intro a x hx
        rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_H
        have := h_IH_H a ⟨x, hx⟩
        exact congr_arg Subtype.val this
      exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime hCop hSolv h_triv
    -- [G, A] = ⊤: G' < ⊤, IH を G' に適用, Three-subgroups で class ≤ 2
    -- G' = commutator G
    set G' : Subgroup G := commutator G with hG'_def
    have hG'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ 1
    have h_G'_lt_top : G' < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial G
    have h_G'_card_lt : Nat.card ↥G' < Nat.card G := card_lt_of_ne_top h_G'_lt_top.ne
    let φ_G' : A →* MulAut ↥G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hG'_inv
    have hG'_pgrp : IsPGroup p ↥G' := hG.to_subgroup G'
    have h_fix_G' : ∀ g' : ↥G', g' ^ p = 1 → ∀ a : A, (φ_G' a) g' = g' := by
      intro g' hg'_pow a
      apply Subtype.ext
      change (φ a) g'.val = g'.val
      apply h_fix
      have := congr_arg (Subtype.val : ↥G' → G) hg'_pow
      simpa using this
    have h_IH_G' := IH φ_G' hG'_pgrp h_fix_G'
      (Nat.le_of_lt_succ (h_G'_card_lt.trans_le h_le))
    have h_triv_G' : ∀ a : A, ∀ g' ∈ G', (φ a) g' = g' := by
      intro a g' hg'
      rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_G'
      have := h_IH_G' a ⟨g', hg'⟩
      exact congr_arg Subtype.val this
    -- Three-subgroups in Γ で G' ⊆ Z(G) を導く
    have h_class_le_2 : commutator G ≤ Subgroup.center G := by
      -- Γ = G ⋊[φ] A. XG = inl(G), YA = inr(A), XG' = inl(G').
      set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
      set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
      set XG' : Subgroup (G ⋊[φ] A) := G'.map (SemidirectProduct.inl : G →* G ⋊[φ] A)
      -- Step 1: ⁅XG', YA⁆ = ⊥ (h_triv_G' + generator computation)
      have h_G'_YA : ⁅XG', YA⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
        rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
        have h_fix' : (φ a) k = k := h_triv_G' a k hk
        rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix', mul_inv_cancel]
        exact map_one _
      -- Step 2: ⁅XG, XG'⁆ ≤ XG' (G' normal in G ⇒ inl の像でも保たれる)
      have h_GG'_le : ⁅XG, XG'⁆ ≤ XG' := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨g, rfl⟩ _ ⟨k, hk, rfl⟩
        -- Goal: ⁅inl g, inl k⁆ ∈ XG' (= inl(G'))
        rw [show (⁅(SemidirectProduct.inl g : G ⋊[φ] A), SemidirectProduct.inl k⁆ :
            G ⋊[φ] A) = SemidirectProduct.inl ⁅g, k⁆ from by
          simp [commutatorElement_def, ← map_mul, ← map_inv]]
        refine ⟨⁅g, k⁆, ?_, rfl⟩
        -- Since G' is normal, both `g * k * g⁻¹` and `k⁻¹` lie in G'.
        have hG'_normal : G'.Normal := inferInstance
        have h_gkg : g * k * g⁻¹ ∈ G' := hG'_normal.conj_mem k hk g
        have h_inv : k⁻¹ ∈ G' := G'.inv_mem hk
        rw [commutatorElement_def]
        exact G'.mul_mem h_gkg h_inv
      -- h12: ⁅⁅XG, XG'⁆, YA⁆ ⊆ ⁅XG', YA⁆ = ⊥
      have h12 : ⁅⁅XG, XG'⁆, YA⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅XG, XG'⁆, YA⁆ ≤ ⁅XG', YA⁆ := Subgroup.commutator_mono h_GG'_le le_rfl
          _ = ⊥ := h_G'_YA
      -- h23: ⁅⁅XG', YA⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥
      have h23 : ⁅⁅XG', YA⁆, XG⁆ = ⊥ := by
        rw [h_G'_YA]
        exact Subgroup.commutator_bot_left XG
      -- Three-subgroups: ⁅⁅YA, XG⁆, XG'⁆ = ⊥
      have h_three : ⁅⁅YA, XG⁆, XG'⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h12 h23
      -- ⁅YA, XG⁆ = ⁅XG, YA⁆ = XG (since actionCommutator = ⊤)
      have h_XGYA_eq_XG : ⁅XG, YA⁆ = XG := by
        rw [← actionCommutator_map_inl φ, h_AC_top]
        exact (MonoidHom.range_eq_map _).symm
      have h_YAXG_eq_XG : ⁅YA, XG⁆ = XG := by
        rw [Subgroup.commutator_comm]; exact h_XGYA_eq_XG
      -- So ⁅XG, XG'⁆ = ⊥ in Γ
      have h_XG_XG'_bot : ⁅XG, XG'⁆ = ⊥ := h_YAXG_eq_XG ▸ h_three
      -- Translate back to G: ⁅⊤, G'⁆ = ⊥ ⇒ G' ⊆ Z(G)
      -- inl(⁅⊤, G'⁆) = ⁅inl(⊤), inl(G')⁆ = ⁅XG, XG'⁆ = ⊥, so ⁅⊤, G'⁆ = ⊥ by inl injective
      have h_top_G'_bot : ⁅(⊤ : Subgroup G), G'⁆ = ⊥ := by
        apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φ] A))
          SemidirectProduct.inl_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.map_bot]
        exact h_XG_XG'_bot
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h_top_G'_bot
      -- h_top_G'_bot : ⊤ ≤ G'.centralizer
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have := h_top_G'_bot (Subgroup.mem_top y)
      exact (this x hx).symm
    -- Apply class ≤ 2 case
    exact actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
      hp_odd h_class_le_2 φ hG hA_p' h_fix

/-- **Isaacs Theorem 4.36** ⭐ (= BG Thm 1.11, **FT クリティカル**):
`p > 2`, `G` p-群, `A` p'-群 が `G` に作用. `A` が `G` の全 order-p 要素を fix するならば,
`A` は `G` 上 trivial に作用する (`actionCommutator φ = ⊥`).

**証明** (Isaacs p.142): 強帰納法 on `|G|`.
- 自明 G: 即座.
- `[G, A] < G`: IH を `actionCommutator` に適用 ⇒ A trivial on [G, A] ⇒ Lem 4.28 系で結論.
- `[G, A] = G`: `G' < G` (G nontrivial nilpotent solvable). IH を G' に適用 ⇒ A trivial on G'.
  Three-subgroups in Γ = G ⋊ A ([G', A] = 1, [G, G'] ⊆ G' から) ⇒ `[G, G'] = 1` ⇒ G' ⊆ Z(G)
  ⇒ class ≤ 2. Baer trick + Cor 4.35 (class ≤ 2 case) で結論.

下流: BG §1 Thm 1.11 (BG Cor 1.12 等), Ch.5 Cor 5.30 経由 normal p-complement (5.26). -/
theorem isaacs_thm_4_36 {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ :=
  isaacs_thm_4_36_aux hp_odd hA_p' (Nat.card G) φ hG h_fix le_rfl

/-- **Isaacs Lemma 4.32 (後半)** ⭐: `P` p-群 が `G` 非自明 p-群 に作用 ⇒
`C_G(P)` (= fixed point subgroup) は非自明.

**proof**: `MulAction P G` を `φ` 経由で setup. `card_modEq_card_fixedPoints` で
`|G| ≡ |fixedPoints| mod p`. G 非自明 p-群より `p ∣ |G|`. 1 は trivial fixed point.
`exists_fixed_point_of_prime_dvd_card_of_fixed_point` で `1` と異なる fixed point 存在. -/
theorem fixedPoints_ne_bot_of_pgroup_action_pgroup
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hP : IsPGroup p P)
    (φ : P →* MulAut G) :
    Subgroup.fixedPointsOfMulAut φ ≠ ⊥ := by
  let : MulAction P G := MulAction.compHom G φ
  -- 1 ∈ fixedPoints (φ p is a group hom, so (φ p) 1 = 1)
  have h1_fix : (1 : G) ∈ MulAction.fixedPoints P G := fun p => by
    change (φ p) 1 = 1
    exact map_one (φ p)
  -- p ∣ |G| since G is a nontrivial p-group
  obtain ⟨n, hn_pos, hn_card⟩ := hG.nontrivial_iff_card.mp inferInstance
  have hp_dvd : p ∣ Nat.card G := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- ∃ b ∈ fixedPoints, b ≠ 1
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := G) hp_dvd h1_fix
  -- b ∈ Subgroup.fixedPointsOfMulAut φ via the same definition
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨b, ?_⟩, ?_⟩
  · exact fun p => hb_fix p
  · intro h
    apply hb_ne
    exact (Subtype.ext_iff.mp h).symm

/-- The left factor inclusion `P →* P × Q`. -/
def prodLeftHom (P Q : Type*) [Group P] [Group Q] : P →* P × Q where
  toFun p := (p, 1)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodLeftHom_apply {P Q : Type*} [Group P] [Group Q] (p : P) :
    prodLeftHom P Q p = (p, 1) :=
  by simp [prodLeftHom]

/-- The right factor inclusion `Q →* P × Q`. -/
def prodRightHom (P Q : Type*) [Group P] [Group Q] : Q →* P × Q where
  toFun q := (1, q)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodRightHom_apply {P Q : Type*} [Group P] [Group Q] (q : Q) :
    prodRightHom P Q q = (1, q) :=
  by simp [prodRightHom]

end

end OddOrder.Isaacs.Ch04


