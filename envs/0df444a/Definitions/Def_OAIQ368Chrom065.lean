-- Prove2me | Definitions.Def_OAIQ368Chrom065
-- name    : OAIQ368Chrom065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:19:50.157218+00:00
-- url     : https://prove2.me/theorems/84b6fa88-9005-4578-9220-0fcb6141836e
-- title:
--   Definitions bundle OAIQ368Chrom065 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Witness_HistoryMainWitness`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/HistoryMainWitness.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom060` and `OAIQ368Chrom064` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom070`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom060
import Definitions.Def_OAIQ368Chrom064

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_HistoryMainWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Packets
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma chromatic_coefficient (a:Fin n →₀ ℕ) (k:ℕ) :
    ((G.chromatic n).coeff a).coeff k=colorCount G a k := by
  have he:∀κ:Fin n → Fin n,wordCount κ=a ↔ ∀c,(Finset.univ.filter (fun j=>κ j=c)).card=a c:=by
    intro κ
    rw [Finsupp.ext_iff]
    simp only [wordCount_apply]
  unfold NaturalUnitIntervalGraph.chromatic colorCount
  rw [MvPolynomial.coeff_sum,Polynomial.finsetSum_coeff,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro κ hκ
  by_cases hp:G.Proper κ
  · simp only [hp,ite_true, if_true,true_and,coloring_monomial,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_monomial]
    by_cases ha:wordCount κ=a
    · simp only [ha,ite_true, if_true,mul_one,Polynomial.coeff_X_pow,(he κ).mp ha]
      simp [eq_comm]
    · simp only [ha,ite_false, if_false,mul_zero,Polynomial.coeff_zero,(he κ).not.mp ha,false_and]
  · simp [hp]

lemma chromatic_degree_zero (a:Fin n →₀ ℕ) (ha:a.degree≠n):
    (G.chromatic n).coeff a=0 := by
  ext k
  rw [chromatic_coefficient,Polynomial.coeff_zero,colorCount]
  apply Finset.sum_eq_zero
  intro κ hκ
  rw [ite_eq_right]
  rintro ⟨_,hc,_⟩
  have hca:wordCount κ=a:=by ext c; rw [wordCount_apply]; exact hc c
  exact ha (hca ▸ wordCount_degree κ)

end
end ElementaryPositivity.FiniteSearch

end

end OAI
end


