-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7D1_BurnsideSetup
-- name    : OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7D1_BurnsideSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:19.192021+00:00
-- url     : https://prove2.me/theorems/62b5b29f-c98b-477a-b277-4f2896a9bdc6
-- title:
--   Isaacs FGT Ch. 7: Burnside's $p^aq^b$ theorem, setup (S7D part 1)
-- statement:
--   Isaacs, *Finite Group Theory*, Chapter 7, pp. 219-222: the setup for Burnside's $p^aq^b$ theorem (Theorem 7.8), including its statement, scaffolding, the Steps 2-9 decomposition and the faithful-action bridge.
--
--   The bundle's definition is `conjActionOfNormalizes`, the conjugation action of a subgroup $A\le N_G(N)$ on $N$.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7D1_BurnsideSetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7D1_BurnsideSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A Sylow `p`-subgroup is nontrivial whenever `p ∣ |G|`. -/
theorem Sylow.ne_bot_of_dvd_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_dvd : p ∣ Nat.card G) (P : Sylow p G) :
    (P : Subgroup G) ≠ ⊥ := by
  intro hP_bot
  have hp_prime : p.Prime := Fact.out
  have h_card : Nat.card (P : Subgroup G) = 1 := by rw [hP_bot]; exact Subgroup.card_bot
  have h_eq := P.card_eq_multiplicity
  rw [h_card] at h_eq
  have h_pos : 0 < (Nat.card G).factorization p :=
    hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd
  have h1 : (1 : ℕ) = p ^ 0 := by simp
  rw [h1] at h_eq
  have h_mult_zero : (Nat.card G).factorization p = 0 :=
    (Nat.pow_right_injective hp_prime.two_le h_eq).symm
  omega

/-- **§7D auxiliary observation** (Isaacs L3965) — if `M` is a maximal subgroup
of a simple group `G` and `K ≤ M` is a nontrivial subgroup normalized by every
element of `M`, then `M = N_G(K)`.

Proof: `M ⊆ N_G(K)` by hypothesis.  `N_G(K) ≠ ⊤` since otherwise `K ⊴ G`
which (by simplicity) forces `K = ⊥` (contradicting nontriviality) or `K = ⊤`
(contradicting `K ≤ M < G`).  By maximality, `N_G(K) = M`. -/
theorem maximal_eq_normalizer_of_M_normalizes
    {G : Type*} [Group G] [IsSimpleGroup G]
    {M K : Subgroup G} (hM_max : IsCoatom M)
    (hK_ne_bot : K ≠ ⊥) (hKM_le : K ≤ M)
    (hM_normalizes : M ≤ Subgroup.normalizer K) :
    Subgroup.normalizer K = M := by
  rcases hM_max.le_iff.mp hM_normalizes with h | h
  · -- N_G(K) = ⊤ ⇒ K is normal in G ⇒ K ∈ {⊥, ⊤} by simplicity.
    exfalso
    have hK_norm_G : K.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg_in_N : g ∈ Subgroup.normalizer K := h ▸ Subgroup.mem_top g
      rw [Subgroup.mem_normalizer_iff] at hg_in_N
      exact (hg_in_N x).mp hx
    rcases hK_norm_G.eq_bot_or_eq_top with hK_bot | hK_top
    · exact hK_ne_bot hK_bot
    · -- K = ⊤ contradicts K ≤ M and M < ⊤ (since M is a coatom).
      have : K ≤ M := hKM_le
      rw [hK_top] at this
      exact hM_max.ne_top (le_antisymm le_top this)
  · -- h : N_G(K) = M is exactly the goal.
    exact h

/-- The conjugation action of a subgroup `A ≤ N_G(N)` on the subgroup `N`,
obtained by composing mathlib's conjugation `MulDistribMulAction` of `N_G(N)`
on `N` with the inclusion `A ↪ N_G(N)`.  Under this action
`a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`. -/
@[reducible]
noncomputable def conjActionOfNormalizes {G : Type*} [Group G] (A N : Subgroup G)
    (hAN : A ≤ Subgroup.normalizer N) : MulDistribMulAction ↥A ↥N :=
  MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer N)) ↥N
    (Subgroup.inclusion hAN)

/-- **§7D Step 1 helper** — a characteristic subgroup `W` of `K` (as a subgroup
of `↥K`) has its `H`-image `W.map K.subtype` normalized by `N_H(K)`.

For `g ∈ N_H(K)`, conjugation by `g` restricts to an automorphism of `↥K`; since
`W` is characteristic, that automorphism preserves `W`, so `g` preserves
`W.map K.subtype`.  Used to deduce `M = N_H(K_p)` from `M = N_H(K)` (`K_p`
characteristic in `K`). -/
theorem normalizer_le_normalizer_map_of_characteristic
    {H : Type*} [Group H] {K : Subgroup H} {W : Subgroup ↥K} [W.Characteristic] :
    Subgroup.normalizer (K : Set H) ≤
      Subgroup.normalizer ((W.map K.subtype) : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  -- The automorphism of ↥K induced by conjugation by `g ∈ N_H(K)`.
  set cg : ↥K ≃* ↥K := K.normalizerMonoidHom (⟨g, hg⟩ : ↥(Subgroup.normalizer K))
    with hcg_def
  -- W characteristic ⇒ `cg` fixes `W`.
  have hWfix : W.map (cg : ↥K →* ↥K) = W :=
    (Subgroup.characteristic_iff_map_eq.mp ‹W.Characteristic›) cg
  -- `↑(cg w) = g * ↑w * g⁻¹` for `w : ↥K`.
  have hcg_apply : ∀ w : ↥K, ((cg w : ↥K) : H) = g * (w : H) * g⁻¹ := fun w => rfl
  have hcg_symm_apply : ∀ w : ↥K, ((cg.symm w : ↥K) : H) = g⁻¹ * (w : H) * g := by
    intro w
    have h := hcg_apply (cg.symm w)
    rw [cg.apply_symm_apply] at h
    -- h : ↑w = g * ↑(cg.symm w) * g⁻¹  ⇒  ↑(cg.symm w) = g⁻¹ * ↑w * g.
    rw [h]; group
  intro y
  simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hwW, rfl⟩
    -- y = ↑w, conjugate by g lands in W.map subtype via cg.
    refine ⟨cg w, ?_, ?_⟩
    · -- cg w ∈ W since cg fixes W.
      rw [← hWfix]; exact ⟨w, hwW, rfl⟩
    · rw [hcg_apply]
  · rintro ⟨w, hwW, hyeq⟩
    -- y conjugated back: g⁻¹ y g ∈ W.map subtype.
    refine ⟨cg.symm w, ?_, ?_⟩
    · rw [← hWfix] at hwW
      obtain ⟨w', hw'W, hw'eq⟩ := hwW
      -- cg.symm w = w' ∈ W.
      have : cg.symm w = w' := by rw [← hw'eq]; exact cg.symm_apply_apply w'
      rw [this]; exact hw'W
    · rw [hcg_symm_apply, hyeq]; group

end OddOrder.Isaacs.Ch07


