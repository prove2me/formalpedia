-- Prove2me | Definitions.Def_Csg_DiscountedValueIteration
-- name    : Csg_DiscountedValueIteration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:30:16.622035+00:00
-- url     : https://prove2.me/theorems/1248af70-0818-4f22-8acf-35ba6ee87aec
-- title:
--   Discounted Value Iteration
-- statement:
--   Definitions and structural lemmas for Discounted Value Iteration, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean

import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_DiscountedCSG_contractingWith_shapley

set_option autoImplicit true
namespace Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
noncomputable def vOpt : S → ℝ :=
  ContractingWith.fixedPoint D.shapley D.contractingWith_shapley
theorem shapley_iterate_tendsto (v : S → ℝ) :
    Filter.Tendsto (fun n => D.shapley^[n] v) Filter.atTop (nhds D.vOpt) :=
  D.contractingWith_shapley.tendsto_iterate_fixedPoint v
def stopCond (eps : ℝ) (v : S → ℝ) (n : ℕ) : Prop :=
  2 * D.l * dist (D.shapley^[n + 1] v) (D.shapley^[n] v) < eps * (1 - D.l)
theorem exists_stopCond {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    ∃ n, D.stopCond eps v n := by
  have h1 : Filter.Tendsto (fun n => D.shapley^[n + 1] v) Filter.atTop (nhds D.vOpt) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr (D.shapley_iterate_tendsto v)
  have h2 : Filter.Tendsto (fun n => D.shapley^[n] v) Filter.atTop (nhds D.vOpt) :=
    D.shapley_iterate_tendsto v
  have hdist : Filter.Tendsto (fun n => dist (D.shapley^[n + 1] v) (D.shapley^[n] v))
      Filter.atTop (nhds 0) := by
    have := h1.dist h2
    rwa [dist_self] at this
  have hscaled : Filter.Tendsto
      (fun n => 2 * D.l * dist (D.shapley^[n + 1] v) (D.shapley^[n] v)) Filter.atTop (nhds 0) := by
    have := hdist.const_mul (2 * D.l)
    simpa using this
  have hpos : (0 : ℝ) < eps * (1 - D.l) := mul_pos heps (by linarith [D.l_lt_one])
  exact (hscaled.eventually_lt_const hpos).exists
noncomputable def numIters {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) : ℕ :=
  @Nat.find _ (Classical.decPred _) (D.exists_stopCond heps v)
noncomputable def valueIteration (eps : ℝ) (v : S → ℝ) : S → ℝ :=
  if h : 0 < eps then D.shapley^[D.numIters h v + 1] v else D.shapley v
end DiscountedCSG
end Csg


