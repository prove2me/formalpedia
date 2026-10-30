-- Prove2me | solution 1 for AssortOpt.HMF.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:09:45.324115+00:00
-- url     : https://prove2.me/submissions/511e0845-e76e-45ae-a4d2-a3a90f0a0aa7

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting
import Theorems.Thm_AssortOpt_HMF_proposition_1
import Theorems.Thm_AssortOpt_HMF_proposition_2
import Theorems.Thm_AssortOpt_HMF_proposition_3
import Theorems.Thm_AssortOpt_HMF_opt_policy_assortment

open AssortOpt.HMF

theorem solution {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∃ S : Finset (Fin n), IsGreatest (revMech D r '' {x | IsIC D x}) (revAssort D r S) := by
  obtain ⟨S, hSgr, hSeq⟩ := opt_policy_assortment D hD r hr
  refine ⟨S, ?_, ?_⟩
  · obtain ⟨hIC, hrev⟩ := (proposition_1 D r hr).1 S
    exact ⟨assortMech S, hIC, hrev⟩
  · rintro v ⟨x, hx, rfl⟩
    -- the support is nonempty since probabilities sum to one
    have hne : D.supp.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have := D.sum_one
      rw [h, Finset.sum_empty] at this
      exact zero_ne_one this
    classical
    let F : Finset (Fin n) → List (Fin n) → ℝ := fun T ℓ => ∑ j ∈ T ∩ ℓ.toFinset, x ℓ j
    have hmax : ∀ T : Finset (Fin n), ∃ ℓ ∈ D.supp, ∀ ℓ' ∈ D.supp, F T ℓ' ≤ F T ℓ :=
      fun T => Finset.exists_max_image D.supp (F T) hne
    choose L hLmem hLmax using hmax
    let f : Finset (Fin n) → ℝ := fun T => F T (L T)
    have hf : ∀ T : Finset (Fin n),
        IsGreatest ((fun ℓ => ∑ j ∈ T ∩ ℓ.toFinset, x ℓ j) '' (D.supp : Set (List (Fin n)))) (f T) := by
      intro T
      refine ⟨⟨L T, hLmem T, rfl⟩, ?_⟩
      rintro w ⟨ℓ', hℓ', rfl⟩
      exact hLmax T ℓ' hℓ'
    obtain ⟨-, -, -, g, hg, hxg⟩ := proposition_2 D r hr x hx f hf
    obtain ⟨φ, hφ, hgφ⟩ := (proposition_3 D r hr).2.2 g hg
    have h1 : revPolicy D r φ ≤ revPolicy D r (assortPolicy S) := hSgr.2 ⟨φ, hφ, rfl⟩
    linarith
