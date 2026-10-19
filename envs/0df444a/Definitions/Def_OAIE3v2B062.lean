-- Prove2me | Definitions.Def_OAIE3v2B062
-- name    : OAIE3v2B062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:20.942249+00:00
-- url     : https://prove2.me/theorems/9228bd0d-bfc2-429c-8579-ddf1a8c0535e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 63 of 311
-- statement:
--   Definitions bundle 63 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B030` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateStageScalarBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B030

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedCandidateStage_allowance (s m dtags dsampler : ℕ)
    {v budget : ℝ} (hv : 2 ≤ v) (htags : (dtags : ℝ) ≤ v)
    (hsampler : (dsampler : ℝ) ≤ v) (hbudget : budget ≤ v) :
    ((s : ℝ) + 1) * ((dtags : ℝ) + 1) ^ s * Real.exp budget *
      ((((m : ℝ) + 1) * ((dsampler : ℝ) + 1) ^ m) ^ s) ≤
        Real.exp (allocatedCandidateStageResetInput s m v + 2) := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have htagsExp : (dtags : ℝ) + 1 ≤ Real.exp (v + 1) := by
    linarith only [htags, Real.add_one_le_exp (v + 1)]
  have hsamplerExp : (dsampler : ℝ) + 1 ≤ Real.exp (v + 1) := by
    linarith only [hsampler, Real.add_one_le_exp (v + 1)]
  have hsExp : (s : ℝ) + 1 ≤ Real.exp ((s : ℝ) + 1) := by
    linarith only [Real.add_one_le_exp ((s : ℝ) + 1)]
  have hmExp : (m : ℝ) + 1 ≤ Real.exp ((m : ℝ) + 1) := by
    linarith only [Real.add_one_le_exp ((m : ℝ) + 1)]
  have htagsPow : ((dtags : ℝ) + 1) ^ s ≤ Real.exp ((s : ℝ) * (v + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) htagsExp s
  have hsamplerPow : ((dsampler : ℝ) + 1) ^ m ≤ Real.exp ((m : ℝ) * (v + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hsamplerExp m
  have hinner : ((m : ℝ) + 1) * ((dsampler : ℝ) + 1) ^ m ≤
      Real.exp (((m : ℝ) + 1) + m * (v + 1)) := by
    rw [Real.exp_add]
    exact mul_le_mul hmExp hsamplerPow (by positivity) (Real.exp_nonneg _)
  have hinnerPow : (((m : ℝ) + 1) * ((dsampler : ℝ) + 1) ^ m) ^ s ≤
      Real.exp ((s : ℝ) * (((m : ℝ) + 1) + m * (v + 1))) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hinner s
  calc
    _ ≤ Real.exp ((s : ℝ) + 1) * Real.exp ((s : ℝ) * (v + 1)) * Real.exp budget *
        Real.exp ((s : ℝ) * (((m : ℝ) + 1) + m * (v + 1))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hsExp htagsPow (by positivity) (Real.exp_nonneg _)) (Real.exp_nonneg _))
        hinnerPow (by positivity) (by positivity)
    _ = Real.exp (((s : ℝ) + 1) + s * (v + 1) + budget +
        s * (((m : ℝ) + 1) + m * (v + 1))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hpow : 0 ≤ (v + 2) ^ 4 := by positivity
      unfold allocatedCandidateStageResetInput
      linarith only [hbudget, hpow]

end Erdos3.VectorPolynomial

end

end OAI
end


