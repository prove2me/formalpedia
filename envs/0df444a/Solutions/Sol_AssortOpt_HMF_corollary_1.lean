-- Prove2me | solution 1 for AssortOpt.HMF.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:25:12.222741+00:00
-- url     : https://prove2.me/submissions/70c866a8-b718-4ac8-a338-6cfea40db919

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

open AssortOpt.HMF

theorem solution {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    (T : ℕ) (τ : List (Fin n) → ℕ) (hτ : IsTierPartition D S j T τ) :
    ∀ ρ ∈ tierDomain D S j, ∀ ρ' ∈ tierDomain D S j,
      (τ ρ' < τ ρ ∨ (τ ρ = τ ρ' ∧ ρ.toFinset ≠ ρ'.toFinset)) →
      adjPrice D r S ρ ≤ adjPrice D r S ρ' := by
  obtain ⟨h1, -, h3, h4⟩ := hτ
  intro ρ hρ ρ' hρ' h
  have hend : ∀ σ ∈ tierDomain D S j, endPrice r σ = r j := by
    intro σ hσ
    have := (Finset.mem_filter.mp hσ).2.1
    unfold endPrice
    rw [this]
    rfl
  unfold adjPrice
  rw [hend ρ hρ, hend ρ' hρ']
  have key : (∀ j' ∈ S, condChoiceProb D S j' ρ' ≤ condChoiceProb D S j' ρ) →
      r j - ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ ≤
        r j - ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ' := by
    intro hle
    have : ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ' ≤ ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ :=
      Finset.sum_le_sum (fun j' hj' => mul_le_mul_of_nonneg_left (hle j' hj') (hr j'))
    linarith
  rcases h with hlt | ⟨heq, hne⟩
  · exact key (h3 ρ hρ ρ' hρ' hlt).2
  · rcases h4 (τ ρ) (h1 ρ hρ) with ha | hb
    · have hρρ' : ρ ≠ ρ' := fun h => hne (h ▸ rfl)
      obtain ⟨-, -, hcond⟩ := ha ρ hρ ρ' hρ' rfl heq.symm hρρ'
      exact key (fun j' hj' => (hcond j' hj').ge)
    · exact absurd (hb ρ hρ ρ' hρ' rfl heq.symm) hne
