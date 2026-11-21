-- Prove2me | solution 1 for AuditAdapt.openLoopMarginal_isPolicy
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T04:08:18.574198+00:00
-- url     : https://prove2.me/submissions/982e6e9f-f555-4a30-a174-c5e0393d68a8

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal
import Theorems.Thm_AuditAdapt_stateLaw_mem_simplex
open AuditAdapt

namespace AuditAdapt

open FoundationsRL.RLBasics

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    IsPolicy H (openLoopMarginal M π) := by
  intro t ht s
  have hπt := hπ t ht
  have hd := stateLaw_mem_simplex M π hπ t (Nat.le_of_lt ht)
  constructor
  · intro a
    change 0 ≤ ∑ s' : S, stateLaw M π t s' * π t s' a
    exact Finset.sum_nonneg fun s' _ =>
      mul_nonneg (hd.1 s') ((hπt s').1 a)
  · change (∑ a : A, ∑ s' : S, stateLaw M π t s' * π t s' a) = 1
    calc
      (∑ a : A, ∑ s' : S, stateLaw M π t s' * π t s' a)
          = ∑ s' : S, ∑ a : A, stateLaw M π t s' * π t s' a :=
        Finset.sum_comm
      _ = ∑ s' : S, stateLaw M π t s' * (∑ a : A, π t s' a) := by
        apply Finset.sum_congr rfl
        intro s' _
        rw [Finset.mul_sum]
      _ = ∑ s' : S, stateLaw M π t s' := by
        apply Finset.sum_congr rfl
        intro s' _
        rw [(hπt s').2, mul_one]
      _ = 1 := hd.2

end AuditAdapt
