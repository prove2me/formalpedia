-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeKernelRestrictionCleanV3
-- name    : MarkovProcess_V3HRepair_FiniteTimeKernelRestrictionCleanV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:48:38.697807+00:00
-- url     : https://prove2.me/theorems/cabbf4cd-c28f-4e4e-ade7-37446f6474a5
-- title:
--   Verified MarkovProcess source repair: FiniteTimeKernelRestrictionCleanV3
-- statement:
--   Conservative finite-time kernels are compatible with restriction to coordinates selected by finite order embeddings. Includes the finite order-embedding factorisation lemmas.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted proof module V3HRepaired.FiniteTimeKernelRestrictionCleanV3, archived SHA-256 4c5683b5de2cbe75aaba78a77703c513275073b702cda580eb9ac7d0c8f87f9f.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d

namespace MarkovProcess

/-- An order embedding `Fin m ↪ Fin (n + 1)` with `m ≤ n` factors through deletion of a
single point. -/
theorem exists_factor_succAboveOrderEmb {m n : ℕ} (e : Fin m ↪o Fin (n + 1)) (h : m ≤ n) :
    ∃ (p : Fin (n + 1)) (d : Fin m ↪o Fin n), d.trans (Fin.succAboveOrderEmb p) = e := by
  classical
  have hns : ¬ Function.Surjective e := by
    intro he
    have hcard := Fintype.card_le_of_surjective e he
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self n) (hcard.trans h)
  rw [Function.Surjective] at hns
  push Not at hns
  obtain ⟨p, hp⟩ := hns
  by_cases plast : p = Fin.last n
  · have hlast : ∀ i, e i ≠ Fin.last n := by
      intro i
      simpa only [plast] using hp i
    let d : Fin m ↪o Fin n :=
      OrderEmbedding.ofStrictMono
        (fun i ↦ (e i).castPred (hlast i))
        (Fin.strictMono_castPred_comp hlast e.strictMono)
    refine ⟨p, d, ?_⟩
    apply DFunLike.ext _ _
    intro i
    change Fin.succAbove p ((e i).castPred (hlast i)) = e i
    rw [plast, Fin.succAbove_last_apply, Fin.castSucc_castPred]
  · let q : Fin n := p.castPred plast
    have hqp : q.castSucc = p := Fin.castSucc_castPred p plast
    have havoid : ∀ i, e i ≠ q.castSucc := by
      intro i
      rw [hqp]
      exact hp i
    have hmono : StrictMono (fun i ↦ q.predAbove (e i)) := by
      intro i j hij
      rw [← (Fin.succAboveOrderEmb p).lt_iff_lt]
      simpa only [Fin.succAboveOrderEmb_apply, ← hqp,
        Fin.succAbove_predAbove (havoid i), Fin.succAbove_predAbove (havoid j)] using
        e.strictMono hij
    let d : Fin m ↪o Fin n :=
      OrderEmbedding.ofStrictMono (fun i ↦ q.predAbove (e i)) hmono
    refine ⟨p, d, ?_⟩
    apply DFunLike.ext _ _
    intro i
    change Fin.succAbove p (q.predAbove (e i)) = e i
    rw [← hqp, Fin.succAbove_predAbove (havoid i)]

end MarkovProcess
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

#print axioms MarkovProcess.exists_factor_succAboveOrderEmb
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_restrictPath_succAbove
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_restrictPath


