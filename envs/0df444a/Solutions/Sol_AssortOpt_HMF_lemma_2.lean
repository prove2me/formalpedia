-- Prove2me | solution 1 for AssortOpt.HMF.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:34:20.81259+00:00
-- url     : https://prove2.me/submissions/e4683b24-c4d3-4df9-9875-8bf88a6355b4

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

open AssortOpt.HMF

namespace HMFLemma2Counter

/-- Three lists over items `{0,1,2,3}`, all ending in item `0`, each with probability `1/3`. -/
noncomputable def Dc : ListDist 4 where
  supp := {[1, 0], [2, 0], [1, 3, 0]}
  p := fun _ => 1 / 3
  nodup := by decide
  pos := by intro ℓ _; norm_num
  sum_one := by
    rw [Finset.sum_const]
    have : ({[1, 0], [2, 0], [1, 3, 0]} : Finset (List (Fin 4))).card = 3 := by decide
    rw [this]; norm_num

lemma supp_eq : Dc.supp = {[1, 0], [2, 0], [1, 3, 0]} := rfl

lemma prefixes_eq : prefixes Dc = {[1], [1, 0], [2], [2, 0], [1, 3], [1, 3, 0]} := by
  unfold prefixes
  rw [supp_eq]
  decide

lemma cond_zero (S' : Finset (Fin 4)) (j' : Fin 4) (ρ : List (Fin 4))
    (hext : ∀ ℓ ∈ Dc.supp, ρ <+: ℓ → ℓ.toFinset ⊆ ρ.toFinset)
    (hd : Disjoint S' ρ.toFinset) : condChoiceProb Dc S' j' ρ = 0 := by
  unfold condChoiceProb
  rw [Finset.sum_eq_zero, zero_div]
  intro ℓ hℓ
  obtain ⟨hℓs, hpre, hch⟩ := by simpa only [Finset.mem_filter] using hℓ
  exfalso
  have hj'S : j' ∈ S' := by
    have := List.find?_some hch
    simpa using this
  have hj'ℓ : j' ∈ ℓ := List.mem_of_find?_eq_some hch
  exact Finset.disjoint_left.mp hd hj'S (hext ℓ hℓs hpre (List.mem_toFinset.mpr hj'ℓ))

lemma key_ext : ∀ σ ∈ prefixes Dc, σ.getLast? = some 0 →
    ∀ ℓ ∈ Dc.supp, σ <+: ℓ → ℓ.toFinset ⊆ σ.toFinset := by
  rw [prefixes_eq, supp_eq]
  decide

lemma key_single : ∀ σ ∈ prefixes Dc, ∀ σ' ∈ prefixes Dc, σ.getLast? = σ'.getLast? →
    σ.getLast? ≠ some 0 → σ = σ' := by
  rw [prefixes_eq]
  decide

lemma hmf : HasHistoryMonotoneFutures Dc := by
  intro ρ hρ ρ' hρ' hend hns S' hd j' _
  by_cases h0 : ρ.getLast? = some 0
  · have h0' : ρ'.getLast? = some 0 := hend ▸ h0
    rw [Finset.disjoint_union_right] at hd
    rw [cond_zero S' j' ρ (key_ext ρ hρ h0) hd.1, cond_zero S' j' ρ' (key_ext ρ' hρ' h0') hd.2]
  · exact absurd (key_single ρ hρ ρ' hρ' hend h0 ▸ Finset.Subset.refl _) hns

lemma tier_eq : tierDomain Dc ∅ 0 = {[1, 0], [2, 0], [1, 3, 0]} := by
  unfold tierDomain
  rw [prefixes_eq]
  decide

end HMFLemma2Counter

open HMFLemma2Counter in
theorem solution : ¬ (∀ {n : ℕ} (D : ListDist n), HasHistoryMonotoneFutures D →
    ∀ (S : Finset (Fin n)) (j : Fin n), j ∉ S →
      ∃ (T : ℕ) (τ : List (Fin n) → ℕ), IsTierPartition D S j T τ) := by
  intro h
  obtain ⟨T, τ, h1, -, h3, h4⟩ := h Dc hmf ∅ 0 (Finset.notMem_empty _)
  have ha : [1, 0] ∈ tierDomain Dc ∅ 0 := by rw [tier_eq]; decide
  have hb : [2, 0] ∈ tierDomain Dc ∅ 0 := by rw [tier_eq]; decide
  have hc : [1, 3, 0] ∈ tierDomain Dc ∅ 0 := by rw [tier_eq]; decide
  -- incomparable prefixes must share a tier
  have same : ∀ ρ ∈ tierDomain Dc ∅ 0, ∀ ρ' ∈ tierDomain Dc ∅ 0,
      ¬ ρ.toFinset ⊂ ρ'.toFinset → ¬ ρ'.toFinset ⊂ ρ.toFinset → τ ρ = τ ρ' := by
    intro ρ hρ ρ' hρ' n1 n2
    rcases lt_trichotomy (τ ρ) (τ ρ') with hlt | heq | hgt
    · exact absurd (h3 ρ' hρ' ρ hρ hlt).1 n1
    · exact heq
    · exact absurd (h3 ρ hρ ρ' hρ' hgt).1 n2
  have hab : τ [1, 0] = τ [2, 0] := same _ ha _ hb (by decide) (by decide)
  have hbc : τ [2, 0] = τ [1, 3, 0] := same _ hb _ hc (by decide) (by decide)
  rcases h4 (τ [1, 0]) (h1 _ ha) with hA | hB
  · have := (hA [1, 0] ha [1, 3, 0] hc rfl (by rw [← hbc, ← hab]) (by decide)).1
    exact this (by decide)
  · have := hB [1, 0] ha [2, 0] hb rfl hab.symm
    exact absurd this (by decide)
