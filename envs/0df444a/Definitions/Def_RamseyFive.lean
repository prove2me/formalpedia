-- Prove2me | Definitions.Def_RamseyFive
-- name    : RamseyFive
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:20.581285+00:00
-- url     : https://prove2.me/theorems/5c71f6ca-fd00-4e4f-97fe-9b524e9f3faa
-- statement:
--   RamseyProperty(s,t,n) is the proposition that every simple graph G on the vertex set Fin n contains either a set of exactly s vertices forming a clique in G or a set of exactly t vertices that is independent in G. ramsey(s,t) is defined as the infimum (least element) of the set of natural numbers n for which RamseyProperty(s,t,n) holds, with the natural-number convention that this is 0 if the set is empty. SharpBounds is a defined proposition, not an established theorem: it asserts that there is a constant C>0 such that for every ε>0 there is a threshold t₀ such that for all natural numbers t≥t₀, both t⁴/(log t)^(3+ε) ≤ ramsey(5,t) and ramsey(5,t) ≤ C·t⁴/(log t)³ hold, where the lower bound uses the real power of log t with exponent 3+ε. SharpExponent is likewise a defined proposition stating that the quantity (4·log t − log ramsey(5,t)) / log(log t) tends to 3 as t tends to infinity through the natural numbers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RamseyFive.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RamseyFive.lean; bytes 16..774
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SharpRamseyFive

def RamseyProperty (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ A : Finset (Fin n), G.IsNClique s A) ∨
    (∃ B : Finset (Fin n), G.IsNIndepSet t B)

noncomputable def ramsey (s t : ℕ) : ℕ := sInf {n : ℕ | RamseyProperty s t n}

def SharpBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    (t : ℝ) ^ 4 / Real.rpow (Real.log t) (3 + ε) ≤ (ramsey 5 t : ℝ) ∧
    (ramsey 5 t : ℝ) ≤ C * (t : ℝ) ^ 4 / (Real.log t) ^ 3

def SharpExponent : Prop :=
  Filter.Tendsto
    (fun t : ℕ => (4 * Real.log (t : ℝ) - Real.log (ramsey 5 t : ℝ)) /
      Real.log (Real.log (t : ℝ)))
    Filter.atTop (nhds (3 : ℝ))



end SharpRamseyFive
end OAI


