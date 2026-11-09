-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling
-- name    : ThinningSprinkling306_ToughCycles_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:45.012882+00:00
-- url     : https://prove2.me/theorems/7b40514e-2fe6-43f9-8f94-d2041c38c338
-- title:
--   Bernoulli subset laws and the joint nested thinning law
-- statement:
--   For a finite vertex set and real $p\in[0,1]$, sampling uses Mathlib's Bernoulli subset probability measure. Each vertex is retained independently with probability $p$. Multiple sampled sets use the product measure, so all membership bits across vertices and sets are independent.
--
--   The nested law takes independent sets $A,B,C$, with parameters $p,1/2,1/2$, and sets
--   $$
--   V_p=A,\qquad V_{p/2}=A\cap B,\qquad V_{p/4}=A\cap B\cap C.
--   $$
--   The resulting random sets have the paper's joint conditional-halving law, beyond merely having the correct marginals. All events lie in finite measurable spaces and all measures are probability measures.
--
--   This module supplies probabilities without an integrability convention or a nonmeasurable pushforward. A total parameter helper clamps inputs to $[0,1]$; every theorem uses valid probabilities, and the derived sprinkling rates are eventually valid in the stated regime, so the helper changes no theorem instance.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 5, Section 2, pp. 5–6 (PDF pp. 7–8) (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Mathlib
import Mathlib.Probability.Distributions.SetBernoulli

namespace ThinningSprinkling306.ToughCycles

/-- Extension outside [0,1]; all theorem instances use probabilities in [0,1]. -/
def probabilityParameter (p : ℝ) : unitInterval :=
  ⟨max 0 (min 1 p), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

/-- The actual Bernoulli subset law from Mathlib; every event is measurable on this finite space. -/
noncomputable def sampleProbability {n : ℕ} (p : ℝ)
    (E : Finset (Fin n) → Prop) : ℝ := by
  classical
  exact (ProbabilityTheory.setBernoulli (Set.univ : Set (Fin n)) (probabilityParameter p)).real
    {S | E S.toFinset}

/-- Product law: all sets, and all their vertex-membership bits, are independent. -/
noncomputable def independentProbability {n r : ℕ} (p : Fin r → ℝ)
    (E : (Fin r → Finset (Fin n)) → Prop) : ℝ := by
  classical
  exact (MeasureTheory.Measure.pi fun i =>
    ProbabilityTheory.setBernoulli (Set.univ : Set (Fin n))
      (probabilityParameter (p i))).real
    {S | E (fun i => (S i).toFinset)}

/-- Two independent conditional halvings of a p-random set. -/
noncomputable def nestedProbability {n : ℕ} (p : ℝ)
    (E : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) → Prop) : ℝ :=
  independentProbability (n := n) (r := 3) (fun i => if i.val = 0 then p else 1 / 2)
    (fun U => E (U 0) (U 0 ∩ U 1) (U 0 ∩ U 1 ∩ U 2))

end ThinningSprinkling306.ToughCycles


