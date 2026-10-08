-- Prove2me | Definitions.Def_SharpLogRamsey
-- name    : SharpLogRamsey
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:20.239744+00:00
-- url     : https://prove2.me/theorems/01a3dfcc-79a3-4536-b839-f5bba8befc8b
-- statement:
--   RamseyProperty(s,t,N) says that every simple graph on N labelled vertices either contains a clique of size s or has a complement containing a clique of size t, that is, an independent set of size t. ramsey(s,t) is the infimum (least element) of the set of N for which this property holds. MainBounds(s) is a defined proposition, not an established theorem: there is a single constant C>0, chosen independently of ε, such that for every ε>0 there is a threshold t₀ so that for all t≥t₀, t^(s−1)/(log t)^((s−2)+ε) ≤ ramsey(s,t) ≤ C·t^(s−1)/(log t)^(s−2). Here s−1 and s−2 are natural-number subtractions, truncated at zero, and the lower-bound exponent is the real number (s−2)+ε. MainLimit(s) is likewise a defined proposition: as t→∞ through the natural numbers, the quantity ((s−1)·log t − log ramsey(s,t)) / log log t converges to the real number s−2, again with s−2 truncated at zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SharpLogRamsey.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SharpLogRamsey.lean; bytes 16..1097
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SharpLogRamsey

/-- Every graph has an s-clique or an independent set of size t. -/
def RamseyProperty (s t N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ A : Finset (Fin N), G.IsNClique s A) ∨
    (∃ B : Finset (Fin N), Gᶜ.IsNClique t B)

noncomputable def ramsey (s t : ℕ) : ℕ := sInf {N | RamseyProperty s t N}

/-- The upper-bound constant is chosen independently of epsilon. -/
def MainBounds (s : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (t : ℝ) ^ (s - 1) / Real.rpow (Real.log (t : ℝ)) ((s - 2 : ℕ) + ε)
        ≤ (ramsey s t : ℝ) ∧
      (ramsey s t : ℝ) ≤ C * (t : ℝ) ^ (s - 1) /
        (Real.log (t : ℝ)) ^ (s - 2)

/-- The logarithmic exponent converges along all natural orders. -/
def MainLimit (s : ℕ) : Prop :=
  Filter.Tendsto
    (fun t : ℕ =>
      (((s - 1 : ℕ) : ℝ) * Real.log (t : ℝ) - Real.log (ramsey s t : ℝ)) /
        Real.log (Real.log (t : ℝ)))
    Filter.atTop (nhds ((s - 2 : ℕ) : ℝ))



end SharpLogRamsey
end OAI


