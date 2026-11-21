-- Prove2me | solution 1 for AuditAdapt.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T04:07:03.448472+00:00
-- url     : https://prove2.me/submissions/abe62853-23f6-4893-a334-08027e239720

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost
import Theorems.Thm_AuditAdapt_value_eq_inner_Q
import Theorems.Thm_AuditAdapt_totalCost_eq_initial_value
import Theorems.Thm_FoundationsRL_RLBasics_performance_difference

namespace AuditAdapt

open FoundationsRL.RLBasics

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π μ : Policy S A H) (hπ : IsPolicy H π) (hμ : IsPolicy H μ) :
    totalCost M π - totalCost M μ =
      ∑ t ∈ Finset.range H, ∑ s : S,
        stateLaw M π t s * ((∑ a : A, Q M μ t s a * π t s a) - V M μ t s) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI : IsEmpty A := hA
      by_cases hH : H = 0
      · subst H
        simp [totalCost]
      · exfalso
        cases isEmpty_or_nonempty S with
        | inl hS =>
            letI : IsEmpty S := hS
            have h : (0 : ℝ) = 1 := by
              simpa using M.d1_sum_one
            norm_num at h
        | inr hS =>
            have h : (0 : ℝ) = 1 := by
              simpa using
                (hπ 0 (Nat.pos_of_ne_zero hH) (Classical.choice hS)).2
            norm_num at h
  | inr hA =>
      letI : Nonempty A := hA

      have hinner (t : ℕ) (ht : t < H) (sh : S) :
          -((∑ a : A, μ t sh a * Q M μ t sh a) -
              ∑ a : A, π t sh a * Q M μ t sh a) =
            (∑ a : A, Q M μ t sh a * π t sh a) - V M μ t sh := by
        rw [(value_eq_inner_Q M μ hμ).2.1 t ht sh]
        have hcommμ :
            (∑ a : A, μ t sh a * Q M μ t sh a) =
              ∑ a : A, Q M μ t sh a * μ t sh a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact mul_comm _ _
        have hcommπ :
            (∑ a : A, π t sh a * Q M μ t sh a) =
              ∑ a : A, Q M μ t sh a * π t sh a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact mul_comm _ _
        rw [hcommμ, hcommπ]
        ring

      have value_diff (s0 : S) :
          V M π 0 s0 - V M μ 0 s0 =
            ∑ t ∈ Finset.range H,
              stateExp M π s0 t (fun sh =>
                (∑ a : A, Q M μ t sh a * π t sh a) - V M μ t sh) := by
        have hpd := performance_difference M π μ hπ hμ s0
        calc
          V M π 0 s0 - V M μ 0 s0 = -(V M μ 0 s0 - V M π 0 s0) := by
            ring
          _ = -(∑ h ∈ Finset.range H,
                stateExp M π s0 h (fun sh =>
                  (∑ a' : A, μ h sh a' * Q M μ h sh a') -
                    ∑ a : A, π h sh a * Q M μ h sh a)) := by
            rw [hpd]
          _ = _ := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            simp only [stateExp]
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro sh hsh
            calc
              -(stateDist M π s0 t sh *
                  ((∑ a' : A, μ t sh a' * Q M μ t sh a') -
                    ∑ a : A, π t sh a * Q M μ t sh a)) =
                  stateDist M π s0 t sh *
                    (-((∑ a' : A, μ t sh a' * Q M μ t sh a') -
                      ∑ a : A, π t sh a * Q M μ t sh a)) := by
                ring
              _ = stateDist M π s0 t sh *
                    ((∑ a : A, Q M μ t sh a * π t sh a) - V M μ t sh) := by
                rw [hinner t (Finset.mem_range.mp ht) sh]

      have mix_stateExp (t : ℕ) (f : S → ℝ) :
          (∑ s0 : S, M.d1 s0 * stateExp M π s0 t f) =
            ∑ s : S, stateLaw M π t s * f s := by
        simp only [stateExp, stateLaw]
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro s0 hs0
        ring

      calc
        totalCost M π - totalCost M μ =
            ∑ s0 : S, M.d1 s0 * (V M π 0 s0 - V M μ 0 s0) := by
          rw [totalCost_eq_initial_value M π hπ,
            totalCost_eq_initial_value M μ hμ]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
        _ = ∑ s0 : S, M.d1 s0 *
              (∑ t ∈ Finset.range H,
                stateExp M π s0 t (fun sh =>
                  (∑ a : A, Q M μ t sh a * π t sh a) - V M μ t sh)) := by
          apply Finset.sum_congr rfl
          intro s0 hs0
          rw [value_diff s0]
        _ = ∑ t ∈ Finset.range H, ∑ s0 : S, M.d1 s0 *
              stateExp M π s0 t (fun sh =>
                (∑ a : A, Q M μ t sh a * π t sh a) - V M μ t sh) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          exact mix_stateExp t (fun sh =>
            (∑ a : A, Q M μ t sh a * π t sh a) - V M μ t sh)

end AuditAdapt
