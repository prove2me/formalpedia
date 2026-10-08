-- Prove2me | Definitions.Def_FourRowPermanent
-- name    : FourRowPermanent
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.012813+00:00
-- url     : https://prove2.me/theorems/2a80e17d-9c28-479c-8e90-4f0e00241e04
-- statement:
--   This block sets up notation for a four-site permanent inequality. Sites are Fin 4, a permutation is an element of Perm(Fin 4), a law is a real-valued function ν on the 24 permutations, and Functions are real-valued maps f(i,j) on pairs of sites. IsProbability(ν) means every mass ν(π) is nonnegative and the masses sum to 1. UniformMarginals(ν) means that for every pair of sites i and j, the total mass of permutations with π(i)=j equals 1/4, so each site is sent to each target equally often. totalVariation(ν) is half the sum over permutations of |ν(π)−1/24|, the distance from the uniform law on the 24 permutations. lpNorm(p,f) is the normalized p-norm of a function f on sites, ((1/4)·Σⱼ f(j)^p)^(1/p), using real powers and uniform counting normalization. permanentExpectation(ν,f) is the sum over permutations π of ν(π) times the product over the four sites i of f(i,π(i)), the expected permanent-type product under ν. The block only supplies these definitions and states no inequality or theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FourRowPermanent.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FourRowPermanent.lean; bytes 16..910
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# A robust four-row permanent inequality

`Fin 4` labels four sites. A law is represented by real probability masses;
`IsProbability` asserts nonnegativity and total mass one. All row norms use
the uniform counting normalization.
-/

noncomputable section
namespace FourRow
open scoped BigOperators

abbrev Site := Fin 4
abbrev Perm := Equiv.Perm Site
abbrev Law := Perm → ℝ
abbrev Functions := Site → Site → ℝ

def IsProbability (ν : Law) : Prop :=
  (∀ π, 0 ≤ ν π) ∧ ∑ π, ν π = 1

def UniformMarginals (ν : Law) : Prop :=
  ∀ i j : Site, ∑ π, (if π i = j then ν π else 0) = 1 / 4

def totalVariation (ν : Law) : ℝ :=
  (∑ π, |ν π - 1 / 24|) / 2

def lpNorm (p : ℝ) (f : Site → ℝ) : ℝ :=
  ((∑ j, (f j) ^ p) / 4) ^ (1 / p)

def permanentExpectation (ν : Law) (f : Functions) : ℝ :=
  ∑ π, ν π * ∏ i, f i (π i)



end FourRow
end
end OAI


