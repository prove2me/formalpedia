-- Prove2me | solution 1 for AuditAdapt.value_eq_inner_Q
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:48:49.498934+00:00
-- url     : https://prove2.me/submissions/1ba21731-1d9c-4054-935c-a3b5579abfe2

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace AuditAdapt

open FoundationsRL.RLBasics

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (μ : Policy S A H) (hμ : IsPolicy H μ) :
    (∀ t, t < H → ∀ s : S, ∀ a : A,
        Q M μ t s a = M.R t s a + ∑ s' : S, M.P t s a s' * V M μ (t + 1) s') ∧
    (∀ t, t < H → ∀ s : S, V M μ t s = ∑ a : A, Q M μ t s a * μ t s a) ∧
    (∀ s : S, V M μ H s = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht s a
    simp only [Q, if_pos ht]
  · intro t ht s
    have hlen : H - t = (H - (t + 1)) + 1 := by omega
    have hlayer : H - 1 - (H - (t + 1)) = t := by omega
    calc
      V M μ t s = valueAux M μ (H - t) s := rfl
      _ = valueAux M μ ((H - (t + 1)) + 1) s := by rw [hlen]
      _ = ∑ a : A, μ t s a *
            (M.R t s a + ∑ s' : S, M.P t s a s' *
              valueAux M μ (H - (t + 1)) s') := by
          simp only [valueAux, hlayer]
      _ = ∑ a : A, Q M μ t s a * μ t s a := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [Q, if_pos ht, V]
          exact mul_comm _ _
  · intro s
    simp [V, valueAux]

end AuditAdapt
