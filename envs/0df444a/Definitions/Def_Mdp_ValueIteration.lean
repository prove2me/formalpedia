-- Prove2me | Definitions.Def_Mdp_ValueIteration
-- name    : Mdp_ValueIteration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:31:08.036464+00:00
-- url     : https://prove2.me/theorems/d3e758a7-ab73-47be-bcf8-339c907ddc82
-- title:
--   Value Iteration
-- statement:
--   Definitions and structural lemmas for Value Iteration, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Theorems.Thm_Mdp_DiscountedMDP_abs_expect_sub_le
import Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman

set_option autoImplicit true
namespace Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
namespace DiscountedMDP
variable (M : DiscountedMDP S A)
noncomputable def vOpt : S → ℝ :=
  ContractingWith.fixedPoint M.bellman M.contractingWith_bellman
noncomputable def Lpolicy (d : S → A) (v : S → ℝ) (s : S) : ℝ :=
  M.r s (d s) + M.l * M.expect s (d s) v
theorem Lpolicy_contracting (d : S → A) (v u : S → ℝ) :
    dist (M.Lpolicy d v) (M.Lpolicy d u) ≤ M.l * dist v u := by
  rw [dist_pi_le_iff (mul_nonneg M.l_nonneg dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  have hbound : |M.expect s (d s) v - M.expect s (d s) u| ≤ dist v u :=
    M.abs_expect_sub_le s (d s) v u
  calc |M.Lpolicy d v s - M.Lpolicy d u s|
      = M.l * |M.expect s (d s) v - M.expect s (d s) u| := by
        rw [show M.Lpolicy d v s - M.Lpolicy d u s
              = M.l * (M.expect s (d s) v - M.expect s (d s) u) from by
              simp only [Lpolicy]; ring,
            abs_mul, abs_of_nonneg M.l_nonneg]
    _ ≤ M.l * dist v u := mul_le_mul_of_nonneg_left hbound M.l_nonneg
theorem lipschitzWith_Lpolicy (d : S → A) : LipschitzWith M.lNN (M.Lpolicy d) :=
  LipschitzWith.of_dist_le_mul fun v u => M.Lpolicy_contracting d v u
theorem contractingWith_Lpolicy (d : S → A) : ContractingWith M.lNN (M.Lpolicy d) :=
  ⟨by exact_mod_cast M.l_lt_one, M.lipschitzWith_Lpolicy d⟩
noncomputable def value (d : S → A) : S → ℝ :=
  ContractingWith.fixedPoint (M.Lpolicy d) (M.contractingWith_Lpolicy d)
theorem exists_argmax (v : S → ℝ) (s : S) :
    ∃ a ∈ (Finset.univ : Finset A), ∀ a' ∈ (Finset.univ : Finset A),
      M.r s a' + M.l * M.expect s a' v ≤ M.r s a + M.l * M.expect s a v :=
  Finset.exists_max_image Finset.univ (fun a => M.r s a + M.l * M.expect s a v) Finset.univ_nonempty
noncomputable def findPolicy (v : S → ℝ) (s : S) : A :=
  (M.exists_argmax v s).choose
end DiscountedMDP
end Mdp


