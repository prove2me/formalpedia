-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_Representations
-- name    : OddOrder_BG_Ch1_Preliminary_S02_Representations
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:40:57.153364+00:00
-- url     : https://prove2.me/theorems/df674373-c168-41e6-ba37-d7328b11ce84
-- title:
--   Bender–Glauberman §2: representations (tail)
-- statement:
--   The tail of the Bender–Glauberman §2 formalization (representations), split off from a longer module. Its docstring gives no further description, and the bundle contains no definitions of its own.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S02_Representations.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S02_Representations.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_FixedSubmodules
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_TwoDimInduction

namespace OddOrder.BG.Ch1.S02

open scoped Pointwise

open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_apply_tmul
  baseChangeRepresentation_faithful)

/-- BG Thm 2.6(b) with the proper-subgroup induction outputs supplied
explicitly.

This is the theorem-facing endpoint for the remaining `G* ≠ 1` and
`G*` non-`p`-group branch.  The hypotheses `hab_ind` and `hsyl_ind` are exactly
the strong-induction outputs for proper normal subgroups of the determinant
kernel, phrased on the restricted faithful representation. -/
private theorem odd_two_dim_sylow_abelian_of_determinantKernel_induction_outputs
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hab_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 →
        (∀ q : ℕ, q.Prime → q ∣ Nat.card N → ¬ CharP F q) →
        Std.Commutative (· * · : N → N → N))
    (hsyl_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 → p ∣ Nat.card N → (P : Sylow p N) →
        Std.Commutative (· * · : P → P → P) ∧
          commutator N ≤ (P : Subgroup N))
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
      ρ hdet_bot P
  by_cases hdet_p : IsPGroup p (determinantKernelSubgroup ρ)
  · exact sylow_commutative_and_commutator_le_of_nontrivial_determinantKernel_pGroup
      ρ hfaithful hdim hdet_p hdet_bot P
  exact
    sylow_commutative_and_commutator_le_of_algebraicClosure_original_induction
      ρ hfaithful hodd hdim
      (determinantKernel_hind_of_odd_two_dim_induction_outputs
        ρ hfaithful hodd hdim hab_ind hsyl_ind) P

/-- Finite subgroup cardinality strictly drops for a proper subgroup. -/
private lemma subgroup_card_lt_of_lt_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H < ⊤) :
    Nat.card H < Nat.card G := by
  have h_dvd : Nat.card H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le : Nat.card H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne : Nat.card H ≠ Nat.card G := fun heq =>
    hH.ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le h_ne

/-- Strong-induction form of BG Thm 2.6(a).

The determinant-kernel branch uses the characteristic-away core spine.  Proper
normal subgroups of `G*` are handled by the induction hypothesis and then
converted into a nontrivial prime core. -/
private theorem odd_two_dim_abelian_strong_induction
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G],
      Nat.card G = n → Odd (Nat.card G) → Module.finrank F V = 2 →
      (ρ : Representation F G V) → Function.Injective ρ →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) →
      Std.Commutative (· * · : G → G → G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard hodd hdim ρ hfaithful hchar
    by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
    · exact commutative_of_determinantKernel_eq_bot ρ hdet_bot
    · refine
        commutative_of_determinantKernel_core_spine_algebraicClosure_charAway
          ρ hfaithful hodd hdim hchar hdet_bot ?_
      intro N hNnormal hN_ne_bot hN_ne_top
      let Gstar : Subgroup G := determinantKernelSubgroup ρ
      let ρN : Representation F N V := ρ.comp (Gstar.subtype.comp N.subtype)
      have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne_bot
      have hfaithfulN : Function.Injective ρN := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact hfaithful (by simpa [ρN, Gstar] using hxy)
      have hN_dvd_Gstar : Nat.card N ∣ Nat.card Gstar :=
        Subgroup.card_subgroup_dvd_card N
      have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card Gstar
      have hoddN : Odd (Nat.card N) :=
        hodd.of_dvd_nat (hN_dvd_Gstar.trans hGstar_dvd_G)
      have hcharN :
          ∀ q : ℕ, q.Prime → q ∣ Nat.card N → ¬ CharP F q := by
        intro q hq_prime hq_dvd
        exact hchar q hq_prime (hq_dvd.trans (hN_dvd_Gstar.trans hGstar_dvd_G))
      have hN_card_lt_Gstar : Nat.card N < Nat.card Gstar := by
        have hN_lt_top : N < ⊤ := lt_top_iff_ne_top.mpr hN_ne_top
        exact subgroup_card_lt_of_lt_top hN_lt_top
      have hGstar_card_le_G : Nat.card Gstar ≤ Nat.card G :=
        Subgroup.card_le_card_group Gstar
      have hN_card_lt_G : Nat.card N < Nat.card G :=
        lt_of_lt_of_le hN_card_lt_Gstar hGstar_card_le_G
      have hNcomm : Std.Commutative (· * · : N → N → N) :=
        ih (Nat.card N) (by simpa [hcard] using hN_card_lt_G)
          (G := N) rfl hoddN hdim ρN hfaithfulN hcharN
      exact exists_prime_opCore_ne_bot_of_commutative hNcomm

/-- **BG Theorem 2.6 (a)**: 奇数位数の有限群 `G` が体 `F` 上 2 次元の
faithful 表現を持ち, char `F` が `|G|` を割らないなら, `G` は abelian. -/
theorem odd_two_dim_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) :
    Std.Commutative (· * · : G → G → G) :=
  odd_two_dim_abelian_strong_induction
    (F := F) (V := V) (Nat.card G) (G := G) rfl hodd hdim ρ hfaithful hchar

/-- Strong-induction form of BG Thm 2.6(b), using Thm 2.6(a) for the
characteristic-away branch on proper subgroups.

This is not the final theorem (a) proof; it isolates the remaining dependency of
the q=p theorem on the abelian branch and supplies the proper-subgroup Sylow
branch recursively. -/
private theorem odd_two_dim_sylow_abelian_strong_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)],
      Nat.card G = n → Odd (Nat.card G) → Module.finrank F V = 2 →
      (ρ : Representation F G V) → Function.Injective ρ →
      p ∣ Nat.card G → (P : Sylow p G) →
      Std.Commutative (· * · : P → P → P) ∧
        commutator G ≤ (P : Subgroup G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hcard hodd hdim ρ hfaithful hp_dvd P
    refine
      odd_two_dim_sylow_abelian_of_determinantKernel_induction_outputs
        (p := p) (F := F) (G := G) hodd hdim ρ hfaithful ?_ ?_ P
    · intro N _hNnormal _hN_ne_bot _hN_ne_top hoddN σ hfaithfulN hdimN hcharN
      exact odd_two_dim_abelian hoddN hdimN σ hfaithfulN hcharN
    · intro N _hNnormal _hN_ne_bot hN_ne_top hoddN σ hfaithfulN hdimN hpN PN
      let Gstar : Subgroup G := determinantKernelSubgroup ρ
      have hN_card_lt_Gstar : Nat.card N < Nat.card Gstar := by
        have hN_lt_top : N < ⊤ := lt_top_iff_ne_top.mpr hN_ne_top
        exact subgroup_card_lt_of_lt_top hN_lt_top
      have hGstar_card_le_G : Nat.card Gstar ≤ Nat.card G :=
        Subgroup.card_le_card_group Gstar
      have hN_card_lt_G : Nat.card N < Nat.card G :=
        lt_of_lt_of_le hN_card_lt_Gstar hGstar_card_le_G
      exact ih (Nat.card N) (by simpa [hcard] using hN_card_lt_G)
        (G := N) rfl hoddN hdimN σ hfaithfulN hpN PN

/-- **BG Theorem 2.6 (b)**: 奇数位数の有限群 `G` が体 `F` 上 2 次元の
faithful 表現を持ち, char `F = p` が `|G|` を割るなら, `G` の `p`-Sylow
は abelian かつ `G'` を含む.

stub: 詳細 proof は §2F section docstring の "證明梗概" + Case q = p
(BG L785-787) 参照. -/
theorem odd_two_dim_sylow_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    (hchar : CharP F p) (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  have : CharP F p := hchar
  exact
    odd_two_dim_sylow_abelian_strong_induction
      (p := p) (F := F) (V := V) (Nat.card G)
      (G := G) rfl hodd hdim ρ hfaithful hp_dvd P

end OddOrder.BG.Ch1.S02


