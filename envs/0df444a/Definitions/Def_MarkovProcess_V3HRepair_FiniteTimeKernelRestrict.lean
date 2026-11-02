-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeKernelRestrict
-- name    : MarkovProcess_V3HRepair_FiniteTimeKernelRestrict
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:45:00.732879+00:00
-- url     : https://prove2.me/theorems/bb46b8fb-2431-4568-8797-affdc1caf070
-- title:
--   Verified MarkovProcess source repair: FiniteTimeKernelRestrict
-- statement:
--   The finite-time kernel projected to an ordered subfamily of coordinates agrees with the kernel evaluated on those selected times.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted axiom-clean proof module V3HRepaired.FiniteTimeKernelRestrict, archived SHA-256 aac839e3d5050f79ade6d6f001a88d8af6e0aaaf8053f9f0fbaa28e61ce0925d.

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelDeletion_f481fd14
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderEmbedding_889d6815
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas

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

end SubMarkovKernelSemigroup
end MarkovProcess

open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
variable {α : Type*} [MeasurableSpace α]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_restrictPath
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
        obtain ⟨p, d, hd⟩ := p2m_embedded_2bc30ec66304e3a6 e hmn
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


