-- Prove2me | Definitions.Def_TopDownParity1043_Main_RandomSets
-- name    : TopDownParity1043_Main_RandomSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:18:04.436719+00:00
-- url     : https://prove2.me/theorems/4a1384b3-2667-4989-884e-89731da09d1a
-- title:
--   §1.3 — Bernoulli random coordinate sets
-- statement:
--   Let $V$ be a finite coordinate set and let $p\in[0,1]$. The law of a random subset formed by including coordinates independently with probability $p$ assigns the weight
--   $$\Pr_p[R]=p^{|R|}(1-p)^{|V|-|R|}\qquad(R\subseteq V).$$
--
--   Event probabilities and nonnegative expectations are finite sums against these weights. The fixed bias $1/4$ is named for Lemma 12. A family $\mathcal A\subseteq2^V$ is downward closed if $R\in\mathcal A$ and $S\subseteq R$ imply $S\in\mathcal A$.
--
--   This common probability interface keeps all random-set statements on the same independent product law, including the endpoints $p=0,1$. The bias type explicitly restricts its domain to the closed unit interval.
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), §1.3 and §4 transfer display, p. 4

import Mathlib

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- §1.3, p.4: Bernoulli biases belong to the closed unit interval. -/
abbrev Bias := Set.Icc (0 : ℝ) 1

/-- Probability of a particular independent Bernoulli set. -/
def setWeight {V : Type} [Fintype V] [DecidableEq V] (p : Bias) (R : Finset V) : ℝ :=
  (p : ℝ) ^ R.card * (1 - (p : ℝ)) ^ (Fintype.card V - R.card)

/-- Event probability under independent inclusion of each coordinate with probability p. -/
noncomputable def setProb {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (E : Finset V → Prop) : ℝ := by
  classical
  exact ∑ R : Finset V, if E R then setWeight p R else 0

/-- Extended nonnegative expectation under the same finite product law. -/
noncomputable def setMean {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (a : Finset V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ R : Finset V, ENNReal.ofReal (setWeight p R) * a R

/-- The fixed one-quarter bias of Lemma 12 and the transfer display. -/
noncomputable def quarterBias : Bias := ⟨1 / 4, by norm_num⟩

/-- Downward closure on the full powerset of the coordinate set. -/
def DownwardClosed {V : Type} (A : Set (Finset V)) : Prop :=
  ∀ R ∈ A, ∀ S : Finset V, S ⊆ R → S ∈ A

end TopDownParity1043.Main


