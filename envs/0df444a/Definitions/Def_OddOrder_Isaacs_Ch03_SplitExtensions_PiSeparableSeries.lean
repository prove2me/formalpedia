-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_PiSeparableSeries
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_PiSeparableSeries
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:00:54.107817+00:00
-- url     : https://prove2.me/theorems/8dca0dc0-11ad-4ca9-9cd9-e557c4748263
-- title:
--   Isaacs Lemma 3.18: series characterization of $\pi$-separability
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, Lemma 3.18 (pp. 90–91), connecting the repository's definition of $\pi$-separability (the upper $\pi$-Fitting series reaches $\top$) with the book's definition via a normal series with $\pi$ or $\pi'$ factors. Key results: `le_piFittingSeries_of_ladder` (the upper series is the fastest: any increasing $G$-normal ladder whose factors are $\pi$-numbers or $\pi'$-numbers lies inside it), `isPiSeparable_of_normal_ladder`, and `isPiSeparable_of_isPiGroup` ($\pi$-groups are $\pi$-separable).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/PiSeparableSeries.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/PiSeparableSeries.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Theorem315

namespace OddOrder.Isaacs.Ch03

open scoped Pointwise

section

variable {G : Type*} [Group G]

/-- If `O_π(G) = ⊥`, then also `O_π(G/⊥) = ⊥`.

This is the quotient-by-`⊥` bridge used to transfer the first nontrivial
`piFittingSeries` step back from `G ⧸ ⊥` to `G`. -/
private theorem oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (hbot : oPiCore π G = ⊥) :
    oPiCore π (G ⧸ (⊥ : Subgroup G)) = ⊥ := by
  let q : G →* G ⧸ (⊥ : Subgroup G) := QuotientGroup.mk' (⊥ : Subgroup G)
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq_inj : Function.Injective q := by
    have hker : q.ker = ⊥ := by
      dsimp [q]
      exact QuotientGroup.ker_mk' (⊥ : Subgroup G)
    exact (MonoidHom.ker_eq_bot_iff q).mp hker
  apply Subgroup.comap_injective hq_surj
  apply le_antisymm
  · rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact (oPiCore.comap_le_of_injective π q hq_inj).trans (le_of_eq hbot)
  · rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact bot_le

/-- **π-separable disjunction**: a finite nontrivial π-separable group has a nontrivial
first π-Fitting layer, i.e. `O_π(G) ⊔ O_{π'}(G) ≠ ⊥`. -/
theorem oPiCore_sup_ne_bot_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [Nontrivial G] [IsPiSeparable π G] :
    (oPiCore π G ⊔ oPiCore {p | p ∉ π} G) ≠ ⊥ := by
  have hF1_ne_bot : piFittingSeries π G 1 ≠ ⊥ := by
    intro hF1
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    have hQsup_bot : (oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
        oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G))) = ⊥ := by
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (⊥ : Subgroup G))
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      -- `piFittingSeries π G 1` は定義 (`piFittingSeries_succ`/`_zero` とも `rfl`) より
      -- ちょうどこの comap (bump 後は simp 経由だと instance 経路がずれるので defeq で渡す).
      exact hF1
    have h_all_bot : ∀ n, piFittingSeries π G n = ⊥ := by
      intro n
      induction n with
      | zero =>
        exact piFittingSeries_zero π G
      | succ n ih =>
        let e : G ⧸ piFittingSeries π G n ≃* G ⧸ (⊥ : Subgroup G) :=
          QuotientGroup.quotientMulEquivOfEq ih
        let Sₙ : Subgroup (G ⧸ piFittingSeries π G n) :=
          oPiCore π (G ⧸ piFittingSeries π G n) ⊔
            oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)
        have hSₙ_map : Sₙ.map e.toMonoidHom =
            oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
              oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G)) := by
          dsimp [Sₙ, e]
          rw [Subgroup.map_sup, oPiCore.map_eq_of_mulEquiv π,
            oPiCore.map_eq_of_mulEquiv {p | p ∉ π}]
        have hSₙ_bot : Sₙ = ⊥ := by
          refine (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom)
            (H := Sₙ) e.injective).mp ?_
          rw [hSₙ_map, hQsup_bot]
        rw [piFittingSeries_succ]
        change Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n)) Sₙ = ⊥
        rw [hSₙ_bot, MonoidHom.comap_bot, QuotientGroup.ker_mk', ih]
    have htop_bot : (⊤ : Subgroup G) = ⊥ := by
      rw [← hn, h_all_bot n]
    exact top_ne_bot htop_bot
  have hF0_lt : piFittingSeries π G 0 < piFittingSeries π G 1 := by
    refine lt_of_le_of_ne (piFittingSeries_le_succ π G 0) ?_
    intro hEq
    exact hF1_ne_bot (by rw [← hEq, piFittingSeries_zero])
  have hQsup0 :=
    (piFittingSeries_lt_succ_iff π (G := G) 0).mp hF0_lt
  have hQsup : (oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
      oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G))) ≠ ⊥ := by
    -- `piFittingSeries π G 0 = ⊥` は `rfl` (bump 後は simp 経由だと instance 経路が
    -- ずれるので defeq で渡す).
    exact hQsup0
  intro hsup_bot
  have hπ_bot : oPiCore π G = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hsup_bot]
    exact le_sup_left
  have hπ'_bot : oPiCore {p | p ∉ π} G = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hsup_bot]
    exact le_sup_right
  have hQπ_bot : oPiCore π (G ⧸ (⊥ : Subgroup G)) = ⊥ :=
    oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot π hπ_bot
  have hQπ'_bot : oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G)) = ⊥ :=
    oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot {p | p ∉ π} hπ'_bot
  exact hQsup (by rw [hQπ_bot, hQπ'_bot, bot_sup_eq])

/-- **π-separable disjunction**, split form:
`O_π(G) ≠ ⊥ ∨ O_{π'}(G) ≠ ⊥`. -/
theorem exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [Nontrivial G] [IsPiSeparable π G] :
    oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥ := by
  have hsup := oPiCore_sup_ne_bot_of_isPiSeparable (G := G) π
  by_cases hπ : oPiCore π G = ⊥
  · right
    intro hπ'
    exact hsup (by rw [hπ, hπ', bot_sup_eq])
  · exact Or.inl hπ

end

end OddOrder.Isaacs.Ch03


