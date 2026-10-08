-- Prove2me | Definitions.Def_CompactBanach
-- name    : CompactBanach
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.560764+00:00
-- url     : https://prove2.me/theorems/4970a65f-ac3c-49aa-b742-9ecf8d77e750
-- statement:
--   For a subset K of a metric space and a natural number b, DoublingAtMost(K,b) means that, for every point x in K and every real radius r>0, there is a finite set of at most b centers in K such that every y in K with dist(y,x)<r lies at distance less than r/2 from one of those centers. Thus each open ball in K can be covered by at most b open balls of half its radius, with all centers belonging to K. For another metric space E, AdmitsBiLipschitzEmbedding(K,E) is the proposition that there exist a map f:K→E, a real scale a>0, and a real distortion bound D≥1 such that a dist(x,y)≤dist(f(x),f(y))≤Da dist(x,y) for every x,y in K. The lower bound ensures that f is injective. Neither definition assumes that K is compact or that either ambient space is a Banach space.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CompactBanach.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CompactBanach.lean; bytes 16..978
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

                                                                                
                                                                              
                                                                                
                                                     

universe u v
namespace CompactBanach

def DoublingAtMost {B : Type*} [MetricSpace B] (K : Set B) (bound : ℕ) : Prop :=
  ∀ x : K, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset K, centers.card ≤ bound ∧
      ∀ y : K, dist y x < r → ∃ c ∈ centers, dist y c < r / ((2 : ℕ) : ℝ)

def AdmitsBiLipschitzEmbedding {B : Type*} [MetricSpace B] (K : Set B)
    (E : Type*) [MetricSpace E] : Prop :=
  ∃ f : K → E, ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ x y : K, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y

                                                                       


end CompactBanach
end OAI


