-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline
-- name    : ChenCapacityTerminals_Exact_RootedHeadline
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T05:42:37.640499+00:00
-- url     : https://prove2.me/theorems/72927304-4716-4912-b1d9-4a75b5e505e7
-- title:
--   Rooted form of the headline fixed-pair reduction
-- statement:
--   This is the prescribed-root specialization of the headline fixed-pair reduction. For every fixed polynomial bound on raw arc count and capacities, one deterministic bounded-word oracle program must return an exact minimum entering shore avoiding the supplied root. Its total submitted-network volume and outside work are $\widetilde O((m+n)\sqrt n)$, including the separately stated linear raw-input preprocessing term. It makes $\widetilde O(\sqrt n)$ calls, and every submitted network has $O(n)$ vertices and $O(m+n)$ arcs.
--
--   The constants and logarithm exponent are uniform over the input class, the program precedes the instance, and every guarantee holds for every lawful integral flow-and-shore oracle. This predicate isolates the dyadic schedule and normalized packing from the final two-orientation argument for global minimum cut.
--
--   **Formalization Note** Here $m$ is represented by `supportSize`, namely $n$ plus the number of positive coalesced loopless ordered pairs. Raw arc count remains explicit in the outside-work bound.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, Theorem 1.1 and its rooted proof, paper pp. 1 and 9–10 (PDF pp. 2 and 10–11), §§4–4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- The rooted half of the headline fixed-pair reduction.  This is the same uniform
bounded-word specification as `HeadlineReduction`, restricted to a prescribed root. -/
def RootedHeadlineReduction (P : WordProgram) : Prop :=
  (∃ O, LawfulWordOracle O) ∧
  ∀ p q : ℕ, ∃ B : ℕ, ∃ C : ℝ, ∃ k : ℕ, 0 < B ∧ 0 < C ∧
    ∀ (G : IntegerInput) (r : ℕ), G.Valid → r < G.n → G.polynomial p q →
      ∀ W ≥ B * (Nat.log2 G.n + 1), ∀ O, LawfulWordOracle O →
        ∃ time trace out,
          WordRun P O 0 (TrulySubcubicAPSP.loadWords W (inputWords G (some r))) time trace out ∧
          WordOutput G (some r) out ∧
          (flowVolume trace : ℝ) ≤ C * supportSize G * Real.sqrt G.n * polylog G.n G.arcs.length k ∧
          (time + (inputWords G (some r)).length + G.n : ℕ) ≤
            C * ((supportSize G : ℝ) * Real.sqrt G.n + G.n + G.arcs.length) *
            polylog G.n G.arcs.length k ∧
          (trace.length : ℝ) ≤ C * Real.sqrt G.n * polylog G.n G.arcs.length k ∧
          (∀ Q ∈ trace, (Q.graph.n : ℝ) ≤ C * G.n ∧
            (Q.graph.arcs.length : ℝ) ≤ C * supportSize G)

end ChenCapacityTerminals.Exact


