-- Prove2me | Definitions.Def_Mdp_ValueIterationAlgorithm
-- name    : Mdp_ValueIterationAlgorithm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:37:01.469135+00:00
-- url     : https://prove2.me/theorems/4dc4c412-a135-430d-89d5-a02069d57fe9
-- title:
--   Value Iteration Algorithm
-- statement:
--   Definitions and structural lemmas for Value Iteration Algorithm, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIterationAlgorithm.lean

import Definitions.Def_Mdp_ValueIteration
import Theorems.Thm_Mdp_DiscountedMDP_bellman_iterate_tendsto

set_option autoImplicit true
namespace Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
namespace DiscountedMDP
variable (M : DiscountedMDP S A)
def stopCond (eps : ℝ) (v : S → ℝ) (n : ℕ) : Prop :=
  2 * M.l * dist (M.bellman^[n + 1] v) (M.bellman^[n] v) < eps * (1 - M.l)
theorem exists_stopCond {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    ∃ n, M.stopCond eps v n := by
  have h1 : Filter.Tendsto (fun n => M.bellman^[n + 1] v) Filter.atTop (nhds M.vOpt) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr (M.bellman_iterate_tendsto v)
  have h2 : Filter.Tendsto (fun n => M.bellman^[n] v) Filter.atTop (nhds M.vOpt) :=
    M.bellman_iterate_tendsto v
  have hdist : Filter.Tendsto (fun n => dist (M.bellman^[n + 1] v) (M.bellman^[n] v))
      Filter.atTop (nhds 0) := by
    have := h1.dist h2
    rwa [dist_self] at this
  have hscaled : Filter.Tendsto (fun n => 2 * M.l * dist (M.bellman^[n + 1] v) (M.bellman^[n] v))
      Filter.atTop (nhds 0) := by
    have := hdist.const_mul (2 * M.l)
    simpa using this
  have hpos : (0 : ℝ) < eps * (1 - M.l) := mul_pos heps (by linarith [M.l_lt_one])
  exact (hscaled.eventually_lt_const hpos).exists
noncomputable def numIters {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) : ℕ :=
  @Nat.find _ (Classical.decPred _) (M.exists_stopCond heps v)
noncomputable def valueIteration (eps : ℝ) (v : S → ℝ) : S → ℝ :=
  if h : 0 < eps then M.bellman^[M.numIters h v + 1] v else M.bellman v
end DiscountedMDP
end Mdp


