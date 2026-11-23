-- Prove2me | Definitions.Def_Mdp_PolicyIteration
-- name    : Mdp_PolicyIteration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:39:38.573318+00:00
-- url     : https://prove2.me/theorems/0f2c1a48-70df-4102-83a3-b74c57008d7e
-- title:
--   Policy Iteration
-- statement:
--   Definitions and structural lemmas for Policy Iteration, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean

import Definitions.Def_Mdp_ValueIteration
import Theorems.Thm_Mdp_DiscountedMDP_bellman_eq_Lpolicy_findPolicy
import Theorems.Thm_Mdp_DiscountedMDP_value_fixedPoint

set_option autoImplicit true
namespace Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
namespace DiscountedMDP
variable (M : DiscountedMDP S A)
noncomputable def policyImprove (d : S → A) (v : S → ℝ) (s : S) : A :=
  if M.r s (d s) + M.l * M.expect s (d s) v = M.bellman v s then d s else M.findPolicy v s
theorem Lpolicy_policyImprove_eq_bellman (d : S → A) (v : S → ℝ) :
    M.Lpolicy (M.policyImprove d v) v = M.bellman v := by
  funext s
  change M.r s (M.policyImprove d v s) + M.l * M.expect s (M.policyImprove d v s) v
      = M.bellman v s
  unfold policyImprove
  split_ifs with h
  · exact h
  · exact (M.bellman_eq_Lpolicy_findPolicy v s).symm
noncomputable def policyStep (d : S → A) : S → A :=
  M.policyImprove d (M.value d)
theorem Lpolicy_mono (d : S → A) : Monotone (M.Lpolicy d) := by
  intro v w hvw
  have hexpect : ∀ s a, M.expect s a v ≤ M.expect s a w := by
    intro s a
    unfold expect
    apply Finset.sum_le_sum
    intro s' _
    exact mul_le_mul_of_nonneg_left (hvw s') ENNReal.toReal_nonneg
  intro s
  change M.Lpolicy d v s ≤ M.Lpolicy d w s
  unfold Lpolicy
  have hstep : M.l * M.expect s (d s) v ≤ M.l * M.expect s (d s) w :=
    mul_le_mul_of_nonneg_left (hexpect s (d s)) M.l_nonneg
  linarith [hstep]
theorem Lpolicy_iterate_tendsto (d : S → A) (v : S → ℝ) :
    Filter.Tendsto (fun n => (M.Lpolicy d)^[n] v) Filter.atTop (nhds (M.value d)) :=
  (M.contractingWith_Lpolicy d).tendsto_iterate_fixedPoint v
theorem Lpolicy_iterate_mono (d : S → A) {v : S → ℝ} (hv : v ≤ M.Lpolicy d v) :
    Monotone (fun n => (M.Lpolicy d)^[n] v) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa using hv
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact M.Lpolicy_mono d ih
theorem Lpolicy_policyStep_ge (d : S → A) :
    M.value d ≤ M.Lpolicy (M.policyStep d) (M.value d) := by
  have heq : M.Lpolicy (M.policyStep d) (M.value d) = M.bellman (M.value d) :=
    M.Lpolicy_policyImprove_eq_bellman d (M.value d)
  rw [heq]
  intro s
  have hle : M.Lpolicy d (M.value d) s ≤ M.bellman (M.value d) s := by
    change M.r s (d s) + M.l * M.expect s (d s) (M.value d) ≤ M.bellman (M.value d) s
    exact Finset.le_sup' (fun a => M.r s a + M.l * M.expect s a (M.value d))
      (Finset.mem_univ (d s))
  rwa [M.value_fixedPoint d] at hle
theorem value_policyStep_ge (d : S → A) : M.value d ≤ M.value (M.policyStep d) := by
  have hmono := M.Lpolicy_iterate_mono (M.policyStep d) (M.Lpolicy_policyStep_ge d)
  have htend := M.Lpolicy_iterate_tendsto (M.policyStep d) (M.value d)
  simpa using hmono.ge_of_tendsto htend 0
theorem eval_eq_imp_policy_eq (d : S → A) (h : M.value d = M.value (M.policyStep d)) :
    d = M.policyStep d := by
  by_contra hne
  obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp hne
  have hnotkeep :
      M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d)
        ≠ M.bellman (M.value d) s₀ := by
    intro hkeep
    apply hs₀
    change d s₀ = M.policyImprove d (M.value d) s₀
    unfold policyImprove
    rw [if_pos hkeep]
  have hle :
      M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d) ≤ M.bellman (M.value d) s₀ :=
    Finset.le_sup' (fun a => M.r s₀ a + M.l * M.expect s₀ a (M.value d))
      (Finset.mem_univ (d s₀))
  have hlt :
      M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d) < M.bellman (M.value d) s₀ :=
    lt_of_le_of_ne hle hnotkeep
  have hval_eq : M.Lpolicy d (M.value d) s₀ = M.value d s₀ :=
    congrFun (M.value_fixedPoint d) s₀
  have hval : M.value d s₀ < M.bellman (M.value d) s₀ := by
    change M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d) = M.value d s₀ at hval_eq
    rwa [hval_eq] at hlt
  have hstep1 : M.Lpolicy (M.policyStep d) (M.value d) s₀ = M.bellman (M.value d) s₀ :=
    congrFun (M.Lpolicy_policyImprove_eq_bellman d (M.value d)) s₀
  rw [← hstep1] at hval
  have hmono := M.Lpolicy_iterate_mono (M.policyStep d) (M.Lpolicy_policyStep_ge d)
  have htend := M.Lpolicy_iterate_tendsto (M.policyStep d) (M.value d)
  have hge : M.Lpolicy (M.policyStep d) (M.value d) ≤ M.value (M.policyStep d) := by
    simpa using hmono.ge_of_tendsto htend 1
  have hfin : M.value d s₀ < M.value (M.policyStep d) s₀ := lt_of_lt_of_le hval (hge s₀)
  rw [h] at hfin
  exact lt_irrefl _ hfin
theorem value_policyStep_iterate_mono (d : S → A) :
    Monotone (fun n => M.value ((M.policyStep)^[n] d)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Function.iterate_succ_apply']
  exact M.value_policyStep_ge ((M.policyStep)^[n] d)
theorem exists_policyStep_fixedPoint (d : S → A) :
    ∃ n, M.policyStep ((M.policyStep)^[n] d) = (M.policyStep)^[n] d := by
  have hval := M.value_policyStep_iterate_mono d
  have key : ∀ p q : ℕ, p < q →
      (M.policyStep)^[p] d = (M.policyStep)^[q] d →
      ∃ n, M.policyStep ((M.policyStep)^[n] d) = (M.policyStep)^[n] d := by
    intro p q hpq heqpq
    have hvaleq : M.value ((M.policyStep)^[p] d) = M.value ((M.policyStep)^[q] d) :=
      congrArg M.value heqpq
    have h1 : M.value ((M.policyStep)^[p] d) ≤ M.value ((M.policyStep)^[p + 1] d) :=
      hval (by omega)
    have h2 : M.value ((M.policyStep)^[p + 1] d) ≤ M.value ((M.policyStep)^[q] d) :=
      hval (by omega)
    have h2' : M.value ((M.policyStep)^[p + 1] d) ≤ M.value ((M.policyStep)^[p] d) := by
      rw [hvaleq]; exact h2
    have heq2 : M.value ((M.policyStep)^[p] d) = M.value ((M.policyStep)^[p + 1] d) :=
      le_antisymm h1 h2'
    have hstep : M.policyStep ((M.policyStep)^[p] d) = (M.policyStep)^[p + 1] d :=
      (Function.iterate_succ_apply' M.policyStep p d).symm
    have heq2' :
        M.value ((M.policyStep)^[p] d) = M.value (M.policyStep ((M.policyStep)^[p] d)) := by
      rw [hstep]; exact heq2
    exact ⟨p, (M.eval_eq_imp_policy_eq _ heq2').symm⟩
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n => (M.policyStep)^[n] d)
  rcases hij.lt_or_gt with hlt | hgt
  · exact key i j hlt heq
  · exact key j i hgt heq.symm
noncomputable def policyIterNum (d : S → A) : ℕ :=
  @Nat.find _ (Classical.decPred _) (M.exists_policyStep_fixedPoint d)
noncomputable def policyIteration (d : S → A) : S → A :=
  (M.policyStep)^[M.policyIterNum d] d
end DiscountedMDP
end Mdp


