-- Prove2me | Definitions.Def_SelfSimilar
-- name    : SelfSimilar
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:37.318565+00:00
-- url     : https://prove2.me/theorems/8dbe5ee0-b2de-4924-8775-d7f33589542f
-- statement:
--   A System over a finite index type ι consists of a contraction ratio r_i, an offset o_i and a weight p_i for each i, where 0<|r_i|<1, every p_i>0, and the weights sum to 1; affine(i) is the map x ↦ r_i x + o_i on the reals. For a word w=(i₁,…,i_n), wordAffine returns the coefficient pair (a,b) of the composition f_{i₁}∘…∘f_{i_n}, with the empty word giving (1,0), and completeMap applies this to a function Fin n → ι. wordWeight is the product of the weights of the letters of w. mapSupport(n) is the finite set of distinct pairs (a,b) arising from words of length n, and mapMass(n,g) is the total weight of all length-n words whose pair equals g. walkEntropy(n) is the Shannon entropy in bits, namely the sum over g of negMulLog of the mass divided by log 2, of this distribution on composed maps. entropyRate is the infimum over n≥1 of walkEntropy(n)/n. lyapunov is −Σ_i p_i log₂|r_i|. SelfSimilar(S,μ) is the proposition that a measure μ on ℝ equals the sum over i of ofReal(p_i) times the pushforward of μ under affine(i). Finally lowerHausdorffDimension(μ) is the infimum, valued in the extended nonnegative reals, of the Hausdorff dimension dimH E over all measurable sets E with μ(E)>0. The block contains only these definitions and states no theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SelfSimilar.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SelfSimilar.lean; bytes 16..1949
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe uι

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

def completeMap (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ × ℝ :=
  S.wordAffine (List.ofFn w)

noncomputable def wordWeight (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ :=
  ∏ j, S.weight (w j)

noncomputable def mapSupport (S : System ι) (n : ℕ) : Finset (ℝ × ℝ) := by
  classical
  exact Finset.univ.image (S.completeMap (n := n))

noncomputable def mapMass (S : System ι) (n : ℕ) (g : ℝ × ℝ) : ℝ := by
  classical
  exact ∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
    S.wordWeight w

noncomputable def walkEntropy (S : System ι) (n : ℕ) : ℝ :=
  (∑ g ∈ S.mapSupport n, Real.negMulLog (S.mapMass n g)) / Real.log 2

noncomputable def entropyRate (S : System ι) : ℝ :=
  sInf (Set.range fun n : ℕ => S.walkEntropy (n + 1) / (n + 1 : ℕ))

noncomputable def lyapunov (S : System ι) : ℝ :=
  -(∑ i, S.weight i * (Real.log |S.ratio i| / Real.log 2))

def SelfSimilar (S : System ι) (μ : Measure ℝ) : Prop :=
  μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

end System

noncomputable def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : MeasurableSet E) (_ : 0 < μ E), dimH E
open MeasureTheory



end EntropyRateDimension
end OAI


