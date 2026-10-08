-- Prove2me | Definitions.Def_SelfSimilarCorollaries
-- name    : SelfSimilarCorollaries
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:29.399195+00:00
-- url     : https://prove2.me/theorems/f7793cff-9af1-4789-8507-9f07b54f0fcc
-- statement:
--   An EntropyRateDimension.System over a finite index type ι consists of real numbers ratio(i), offset(i) and weight(i) for each i, such that every contraction ratio satisfies 0<|ratio(i)|<1, every weight is strictly positive, and the weights sum to 1. Its affine maps are affine(i)(x)=ratio(i)·x+offset(i). For a finite word (list) of indices, wordAffine returns a pair of reals defined recursively: the empty word gives (1,0), and for a word i::w with wordAffine(w)=(a,b), the result is (ratio(i)·a, ratio(i)·b+offset(i)). A measure μ on ℝ is SelfSimilar for the system if μ equals the sum over i of ofReal(weight(i)) times the pushforward of μ under affine(i). The lowerHausdorffDimension of a measure μ is the infimum, in the extended nonnegative reals, of the Hausdorff dimensions dimH(E) over all measurable sets E with μ(E)>0. In the Extensions section, NoExactOverlaps(S) is the proposition that wordAffine is injective on finite words, so distinct words give distinct pairs. The symbolEntropy of S is the sum over i of negMulLog(weight(i)), that is, the Shannon entropy −Σ weight(i) log weight(i) of the weight vector. The block contains only these definitions and no theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SelfSimilarCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SelfSimilarCorollaries.lean; bytes 16..1228
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe uι

section

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

structure System (ι : Type uι) [Fintype ι] where
  ratio : ι → ℝ
  offset : ι → ℝ
  weight : ι → ℝ
  ratio_pos : ∀ i, 0 < |ratio i|
  ratio_lt_one : ∀ i, |ratio i| < 1
  weight_pos : ∀ i, 0 < weight i
  weight_sum : ∑ i, weight i = 1

namespace System
variable {ι : Type uι} [Fintype ι]

def affine (S : System ι) (i : ι) (x : ℝ) : ℝ := S.ratio i * x + S.offset i

def wordAffine (S : System ι) : List ι → ℝ × ℝ
  | [] => (1, 0)
  | i :: w => (S.ratio i * (S.wordAffine w).1,
      S.ratio i * (S.wordAffine w).2 + S.offset i)

def SelfSimilar (S : System ι) (μ : Measure ℝ) : Prop :=
  μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

end System

noncomputable def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : MeasurableSet E) (_ : 0 < μ E), dimH E

namespace Extensions
variable {ι : Type uι} [Fintype ι]

def NoExactOverlaps (S : System ι) : Prop := Function.Injective S.wordAffine

noncomputable def symbolEntropy (S : System ι) : ℝ :=
  ∑ i, Real.negMulLog (S.weight i)



end Extensions
end EntropyRateDimension
end
end OAI


