-- Prove2me | solution 1 for AuditAdapt.stateLaw_mem_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:59:35.302214+00:00
-- url     : https://prove2.me/submissions/be5081ff-e914-4ef2-8bef-2463d10ad9fb

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw

namespace AuditAdapt

open FoundationsRL.RLBasics

private lemma stateDist_simplex_aux {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    ∀ (s0 : S) (t : ℕ), t ≤ H →
      (∀ s : S, 0 ≤ stateDist M π s0 t s) ∧
        ∑ s : S, stateDist M π s0 t s = 1 := by
  intro s0 t
  induction t with
  | zero =>
      intro _
      constructor
      · intro s
        by_cases hs : s = s0
        · simp [stateDist, hs]
        · simp [stateDist, hs]
      · simp [stateDist]
  | succ t ih =>
      intro ht
      have htH : t < H := by omega
      have ht_le : t ≤ H := by omega
      have hrec := ih ht_le
      constructor
      · intro s
        change 0 ≤ ∑ sp : S, stateDist M π s0 t sp *
          ∑ a : A, π t sp a * M.P t sp a s
        exact Finset.sum_nonneg fun sp _ =>
          mul_nonneg (hrec.1 sp) (Finset.sum_nonneg fun a _ =>
            mul_nonneg ((hπ t htH sp).1 a) (M.P_nonneg t sp a s))
      · calc
          ∑ s : S, stateDist M π s0 (Nat.succ t) s
              = ∑ sp : S, ∑ s : S, stateDist M π s0 t sp *
                  ∑ a : A, π t sp a * M.P t sp a s := by
                simp only [stateDist]
                exact Finset.sum_comm
          _ = ∑ sp : S, stateDist M π s0 t sp := by
                apply Finset.sum_congr rfl
                intro sp _
                rw [← Finset.mul_sum]
                have hsum :
                    (∑ s : S, ∑ a : A, π t sp a * M.P t sp a s) =
                      ∑ a : A, π t sp a := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [← Finset.mul_sum, M.P_sum_one t sp a, mul_one]
                rw [hsum, (hπ t htH sp).2, mul_one]
          _ = 1 := hrec.2

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (t : ℕ) (ht : t ≤ H) :
    (∀ s : S, 0 ≤ stateLaw M π t s) ∧ ∑ s : S, stateLaw M π t s = 1 := by
  constructor
  · intro s
    unfold stateLaw
    exact Finset.sum_nonneg fun s0 _ =>
      mul_nonneg (M.d1_nonneg s0)
        ((stateDist_simplex_aux M π hπ s0 t ht).1 s)
  · unfold stateLaw
    rw [Finset.sum_comm]
    have hmass : ∀ s0 : S,
        (∑ s : S, M.d1 s0 * stateDist M π s0 t s) = M.d1 s0 := by
      intro s0
      rw [← Finset.mul_sum, (stateDist_simplex_aux M π hπ s0 t ht).2, mul_one]
    simp_rw [hmass]
    exact M.d1_sum_one

end AuditAdapt
