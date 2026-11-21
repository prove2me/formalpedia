-- Prove2me | solution 1 for AuditAdapt.same_state_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T04:04:40.880233+00:00
-- url     : https://prove2.me/submissions/1e1c5cfb-9ec6-4ee4-a2a9-3611f607d26c

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt

open FoundationsRL.RLBasics

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (t : ℕ) (ht : t < H)
    (g : S → ℝ) :
    ∑ s : S, ∑ a : A, stateLaw M π t s * π t s a * g s =
      ∑ s : S, ∑ a : A, stateLaw M π t s * marginal M π t a * g s := by
  classical
  have stateDist_mass : ∀ u : ℕ, u ≤ H → ∀ s0 : S,
      (∑ s : S, stateDist M π s0 u s) = 1 := by
    intro u
    induction u with
    | zero =>
        intro _ s0
        simp [stateDist]
    | succ u ih =>
        intro hu s0
        have huH : u < H := by omega
        have hu_le : u ≤ H := by omega
        simp only [stateDist]
        calc
          (∑ s : S, ∑ sp : S, stateDist M π s0 u sp *
                ∑ a : A, π u sp a * M.P u sp a s) =
              ∑ sp : S, stateDist M π s0 u sp *
                (∑ s : S, ∑ a : A, π u sp a * M.P u sp a s) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro sp hsp
            symm
            rw [Finset.mul_sum]
          _ = ∑ sp : S, stateDist M π s0 u sp := by
            apply Finset.sum_congr rfl
            intro sp hsp
            have hswap :
                (∑ s : S, ∑ a : A, π u sp a * M.P u sp a s) =
                  ∑ a : A, π u sp a * (∑ s : S, M.P u sp a s) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a ha
              symm
              rw [Finset.mul_sum]
            rw [hswap]
            simp [M.P_sum_one, (hπ u huH sp).2]
          _ = 1 := ih hu_le s0
  have stateLaw_mass : ∀ u : ℕ, u ≤ H →
      (∑ s : S, stateLaw M π u s) = 1 := by
    intro u hu
    unfold stateLaw
    rw [Finset.sum_comm]
    calc
      (∑ s0 : S, ∑ s : S, M.d1 s0 * stateDist M π s0 u s) =
          ∑ s0 : S, M.d1 s0 * (∑ s : S, stateDist M π s0 u s) := by
        apply Finset.sum_congr rfl
        intro s0 hs0
        symm
        rw [Finset.mul_sum]
      _ = ∑ s0 : S, M.d1 s0 := by
        apply Finset.sum_congr rfl
        intro s0 hs0
        rw [stateDist_mass u hu s0, mul_one]
      _ = 1 := M.d1_sum_one
  have hmarg : (∑ a : A, marginal M π t a) = 1 := by
    unfold marginal
    rw [Finset.sum_comm]
    calc
      (∑ s : S, ∑ a : A, stateLaw M π t s * π t s a) =
          ∑ s : S, stateLaw M π t s * (∑ a : A, π t s a) := by
        apply Finset.sum_congr rfl
        intro s hs
        symm
        rw [Finset.mul_sum]
      _ = ∑ s : S, stateLaw M π t s := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [(hπ t ht s).2, mul_one]
      _ = 1 := stateLaw_mass t (Nat.le_of_lt ht)
  apply Finset.sum_congr rfl
  intro s hs
  calc
    (∑ a : A, stateLaw M π t s * π t s a * g s) =
        stateLaw M π t s * g s * (∑ a : A, π t s a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = stateLaw M π t s * g s := by
      rw [(hπ t ht s).2, mul_one]
    _ = stateLaw M π t s * g s * (∑ a : A, marginal M π t a) := by
      rw [hmarg, mul_one]
    _ = ∑ a : A, stateLaw M π t s * marginal M π t a * g s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end AuditAdapt
