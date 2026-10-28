-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_KernelRestriction
-- name    : MarkovProcessModule_MarkovProcess_FiniteTime_KernelRestriction
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:57:14.765306+00:00
-- url     : https://prove2.me/theorems/f286ce46-e703-4b89-9a6c-595dc53c6f34
-- title:
--   MarkovProcess.FiniteTime.KernelRestriction
-- statement:
--   # Restricting finite-time kernels
--
--   For a conservative sub-Markov kernel semigroup, restriction along any finite order embedding
--   gives the finite-time kernel at the selected times. This is finite-dimensional kernel
--   infrastructure and does not construct a path-space law or a stochastic process.
--
--   Complete pinned Lean module MarkovProcess.FiniteTime.KernelRestriction by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/KernelRestriction.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Time_FiniteOrderEmbedding
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_KernelDeletion

/-!
# Restricting finite-time kernels

For a conservative sub-Markov kernel semigroup, restriction along any finite order embedding
gives the finite-time kernel at the selected times. This is finite-dimensional kernel
infrastructure and does not construct a path-space law or a stochastic process.
-/

open ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

private theorem fin_orderEmbedding_self_eq_id {n : ℕ} (e : Fin n ↪o Fin n) :
    e = (OrderIso.refl (Fin n)).toOrderEmbedding := by
  let eo : Fin n ≃o Fin n :=
    { Equiv.ofBijective e ⟨e.injective, Finite.surjective_of_injective e.injective⟩ with
      map_rel_iff' := e.le_iff_le }
  apply DFunLike.ext _ _
  intro i
  apply Fin.ext
  exact Fin.coe_orderIso_apply eo i

namespace IsConservative

/-- Restricting a conservative finite-time kernel along any finite order embedding gives the
kernel at the restricted times. -/
theorem finiteTimeKernel_map_restrictPath
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n) :
    (finiteTimeKernel P times).map (FiniteOrderedTimes.restrictPath e) =
      finiteTimeKernel P (times.restrict e) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by
        have hcard := Fintype.card_le_of_injective e e.injective
        simpa only [Fintype.card_fin, Nat.le_zero] using hcard
      subst m
      rw [fin_orderEmbedding_self_eq_id e]
      rw [show (FiniteOrderedTimes.restrictPath (OrderIso.refl (Fin 0)).toOrderEmbedding :
            (Fin 0 → α) → Fin 0 → α) = id by
          funext path
          exact FiniteOrderedTimes.restrictPath_id path]
      rw [Kernel.map_id, FiniteOrderedTimes.restrict_id]
  | succ n ih =>
      have hcard : m ≤ n + 1 := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
      by_cases hm : m = n + 1
      · subst m
        rw [fin_orderEmbedding_self_eq_id e]
        rw [show (FiniteOrderedTimes.restrictPath
              (OrderIso.refl (Fin (n + 1))).toOrderEmbedding :
              (Fin (n + 1) → α) → Fin (n + 1) → α) = id by
            funext path
            exact FiniteOrderedTimes.restrictPath_id path]
        rw [Kernel.map_id, FiniteOrderedTimes.restrict_id]
      · have hmn : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hcard hm)
        obtain ⟨p, d, hd⟩ := exists_factor_succAboveOrderEmb e hmn
        rw [← hd]
        have hdelete := hP.finiteTimeKernel_map_restrictPath_succAbove P times p
        have hdel : Measurable (FiniteOrderedTimes.restrictPath
            (Fin.succAboveOrderEmb p) : (Fin (n + 1) → α) → Fin n → α) :=
          FiniteOrderedTimes.measurable_restrictPath (Fin.succAboveOrderEmb p)
        have hdmeas : Measurable
            (FiniteOrderedTimes.restrictPath d : (Fin n → α) → Fin m → α) :=
          FiniteOrderedTimes.measurable_restrictPath d
        rw [show (FiniteOrderedTimes.restrictPath (d.trans (Fin.succAboveOrderEmb p)) :
              (Fin (n + 1) → α) → Fin m → α) =
            FiniteOrderedTimes.restrictPath d ∘
              FiniteOrderedTimes.restrictPath (Fin.succAboveOrderEmb p) by rfl]
        rw [Kernel.map_comp_right _ hdel hdmeas, hdelete,
          ih (times.restrict (Fin.succAboveOrderEmb p)) d,
          FiniteOrderedTimes.restrict_trans]

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


