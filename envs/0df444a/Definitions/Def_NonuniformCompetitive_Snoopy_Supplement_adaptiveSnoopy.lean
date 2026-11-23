-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_adaptiveSnoopy
-- name    : NonuniformCompetitive_Snoopy_Supplement_adaptiveSnoopy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:53:15.607814+00:00
-- url     : https://prove2.me/theorems/99635804-41fd-4203-bb98-d974e7b99335
-- title:
--   Bounded causal caching interactions and adaptive online comparison
-- statement:
--   A request strategy observes the completed request, moment state and after state of a caching algorithm before choosing its next request. Truncating at $N$ bounds the number of requests on every coin outcome. Observed finite-valued states must be measurable random variables.
--
--   Adaptive online competitiveness from $s_0$ requires one additive constant $a$ with
--   $$\mathbf E C_A(\sigma(S))\le c\,\mathbf E C_B(\sigma(S))+a$$
--   for every bounded causal strategy and every causal online competitor $B$ starting at $s_0$, on admissible interactions with measurable costs and finite expected comparator cost. The competitor receives the same realized requests and does not receive future coins. A real signed right-hand side is formed only after the comparator expectation is known finite.
--
--   This extends the published fixed-input caching model to actual adaptive interactions. It does not replace the comparison cost by an offline optimum.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §1, p. 543; Theorem 5 and proof, p. 554

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

attribute [local instance] NonuniformCompetitive.Snoopy.RandomizedAlgorithm.ms

abbrev SnoopyTranscript (n : ℕ) := List (NonuniformCompetitive.Snoopy.Req n ×
  NonuniformCompetitive.Snoopy.State n × NonuniformCompetitive.Snoopy.State n)

/-- A deterministic causal request generator, observing only completed actions.
Truncation at N gives the uniform bound f(S)=N, regardless of random choices. -/
structure SnoopyStrategy (n : ℕ) where
  next : SnoopyTranscript n → Option (NonuniformCompetitive.Snoopy.Req n)

def snoopyPlay {n : ℕ} (A : NonuniformCompetitive.Snoopy.OnlineAlgorithm n)
    (S : SnoopyStrategy n) : ℕ → SnoopyTranscript n
  | 0 => []
  | N + 1 =>
      let h := snoopyPlay A S N
      match S.next h with
      | none => h
      | some r =>
          let σ := h.map (fun x => x.1)
          h ++ [(r, A.moment (σ ++ [r]), A.after (σ ++ [r]))]

def snoopyInput {n : ℕ} (A : NonuniformCompetitive.Snoopy.OnlineAlgorithm n)
    (S : SnoopyStrategy n) (N : ℕ) : List (NonuniformCompetitive.Snoopy.Req n) :=
  (snoopyPlay A S N).map (fun x => x.1)

/-- Observed states are genuine random variables. The finite action space has
its discrete sigma algebra. No restriction to threshold or phase policies occurs. -/
def SnoopyRegular {n p : ℕ} (A : NonuniformCompetitive.Snoopy.RandomizedAlgorithm n p) : Prop :=
  ∀ (σ : List (NonuniformCompetitive.Snoopy.Req n)) (s : NonuniformCompetitive.Snoopy.State n),
    MeasurableSet {i | (A.alg i).moment σ = s} ∧ MeasurableSet {i | (A.alg i).after σ = s}

noncomputable def snoopyInteractingCost {n p : ℕ}
    (A : NonuniformCompetitive.Snoopy.RandomizedAlgorithm n p) (S : SnoopyStrategy n)
    (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ i, (A.alg i).cost p (snoopyInput (A.alg i) S N) ∂A.μ

noncomputable def snoopyComparatorCost {n p : ℕ}
    (A : NonuniformCompetitive.Snoopy.RandomizedAlgorithm n p) (S : SnoopyStrategy n)
    (N : ℕ) (B : NonuniformCompetitive.Snoopy.OnlineAlgorithm n) : ℝ≥0∞ :=
  ∫⁻ i, B.cost p (snoopyInput (A.alg i) S N) ∂A.μ

/-- Adaptive ONLINE comparison, not an offline optimum. The one additive
constant precedes every bounded strategy and every causal competitor. Entirely
infinite-cost competitors are irrelevant to a finite cost comparison. Regularity
of the interacting costs is explicit on each test, rather than inferred from
fixed-sequence measurability alone. -/
def SnoopyAdaptiveCompetitive {n p : ℕ}
    (A : NonuniformCompetitive.Snoopy.RandomizedAlgorithm n p)
    (s₀ : NonuniformCompetitive.Snoopy.State n) (c : ℝ) : Prop :=
  (∀ i, (A.alg i).after [] = s₀) ∧
  ∃ a : ℝ, ∀ (N : ℕ) (S : SnoopyStrategy n) (B : NonuniformCompetitive.Snoopy.OnlineAlgorithm n),
    B.after [] = s₀ →
    (∀ i, NonuniformCompetitive.Snoopy.Admissible (snoopyInput (A.alg i) S N)) →
    Measurable (fun i => (A.alg i).cost p (snoopyInput (A.alg i) S N)) →
    Measurable (fun i => B.cost p (snoopyInput (A.alg i) S N)) →
    snoopyComparatorCost A S N B ≠ ⊤ →
    snoopyInteractingCost A S N ≤
      ENNReal.ofReal (c * (snoopyComparatorCost A S N B).toReal + a)

end NonuniformCompetitive.Snoopy.Supplement


