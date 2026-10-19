-- Prove2me | Definitions.Def_OAIE3v2B160
-- name    : OAIE3v2B160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:56.098742+00:00
-- url     : https://prove2.me/theorems/7d57677d-cf0e-4a3f-a545-26d01ac41f84
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 162 of 311
-- statement:
--   Definitions bundle 162 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B100`, `OAIE3v2B142`, `OAIE3v2B147`, `OAIE3v2B148` of this split.
--
--   Modules: `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Sampling/PhysicalGridCorrelation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B147
import Definitions.Def_OAIE3v2B148

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedFiniteForwardSchedule_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) := by
  let Q : ℕ → Polynomial ℕ := fun n =>
    preparedFiniteForwardParameterPolynomial A stageCountConstant n +
      preparedFiniteForwardWorkPolynomial A stageCountConstant n +
      preparedFiniteForwardCapPolynomial A stageCountConstant n +
      preparedFiniteForwardCountPolynomial A stageCountConstant n +
      preparedFiniteForwardBranchPolynomial A stageCountConstant n
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (∑ n ∈ Finset.range (depth + 1), Q n)
  refine ⟨C, hC, ?_⟩
  intro x hx n hn
  have hentry : (Q n).eval₂ (Nat.castRingHom ℝ) x ≤ (x + C) ^ C := by
    apply le_trans _ (hbudget x hx)
    rw [Polynomial.eval₂_finsetSum]
    exact Finset.single_le_sum (fun i _ => natPolynomial_eval_nonneg (Q i) hx)
      (Finset.mem_range.mpr (by omega))
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hcap := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have hcount := preparedFiniteForwardCount_nonneg A stageCountConstant n hx
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  simp only [Q, Polynomial.eval₂_add] at hentry
  change preparedFiniteForwardParameter A stageCountConstant n x +
      preparedFiniteForwardWork A stageCountConstant n x +
      preparedFiniteForwardCap A stageCountConstant n x +
      preparedFiniteForwardCount A stageCountConstant n x +
      preparedFiniteForwardBranch A stageCountConstant n x ≤ (x + C) ^ C at hentry
  exact ⟨⟨hp, by linarith⟩, ⟨hw, by linarith⟩, ⟨hcap, by linarith⟩,
    ⟨hcount, by linarith⟩, ⟨hbranch, by linarith⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedBoxPartitions {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ)) :
    ∀ i, FiniteProgressionPartition (N i) :=
  comparableBoxPartitions N (fun i => ⌊ρ * H i / 2⌋₊)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).2.1)

theorem normalizedBoxPartitions_positive {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    0 < (normalizedBoxPartitions N H ρ hlarge hwhole i).length c := by
  exact (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1.trans_le
    (comparableBoxPartitions_length N _ _ _ i c).1

end Erdos3

end

end OAI
end


