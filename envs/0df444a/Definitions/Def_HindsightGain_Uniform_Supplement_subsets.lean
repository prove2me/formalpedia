-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_subsets
-- name    : HindsightGain_Uniform_Supplement_subsets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:05.700265+00:00
-- url     : https://prove2.me/theorems/e901b9d1-59e1-49e2-8135-89979398f8f6
-- title:
--   Independent retention and uniform fixed-size subset laws
-- statement:
--   Let $V$ be a finite set and $p=(p_i)_{i\in V}$ real numbers. The random set $S$ that retains each $i\in V$ independently with probability $p_i$ has the law
--   $$\mathbb P(S=T)=\prod_{i\in T}p_i\prod_{i\notin T}(1-p_i)\qquad(T\subseteq V).$$
--   For an event $E$ of the random set, its probability is $\sum_{T:\,E(T)}\mathbb P(S=T)$; the expectation of a set function $f$ is $\sum_T\mathbb P(S=T)f(T)$, and its variance is $\mathbb E\big(f(S)-\mathbb Ef(S)\big)^2$. Uniform retention $S_p$ is the case $p_i=p$ for all $i$. For an integer $q$, the probability of $E$ for a uniformly random $q$-element subset is the proportion $\#\{T:|T|=q,\ E(T)\}/\binom{|V|}{q}$.
--
--   These finite laws are the sampling models of the CSP, graph and quantum applications.
--
--   **Formalization Note** All laws are exact finite sums; there is no measure-theoretic coupling. For $p_i\in[0,1]$ the weights form a probability distribution.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §1.2 p.5, §5.1 p.22, §5.3 p.25, §7 p.29

import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace HindsightGain.Uniform.Supplement

/-- Exact law of independent retention with inclusion probabilities `p i`:
`P(S) = ∏_{i ∈ S} p_i · ∏_{i ∉ S} (1 - p_i)` (pp.5, 23). -/
def subsetProb {V : Type} [Fintype V] (p : V → ℝ) (S : Finset V) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

/-- Probability of an event `E` of the random set under independent retention. -/
def bernProb {V : Type} [Fintype V] (p : V → ℝ) (E : Finset V → Prop) : ℝ :=
  ∑ S : Finset V, if E S then subsetProb p S else 0

/-- Expectation of a set function under independent retention. -/
def bernExp {V : Type} [Fintype V] (p : V → ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ S : Finset V, subsetProb p S * f S

/-- Variance of a set function under independent retention. -/
def bernVar {V : Type} [Fintype V] (p : V → ℝ) (f : Finset V → ℝ) : ℝ :=
  bernExp p (fun S => (f S - bernExp p f) ^ 2)

/-- Probability of an event for a uniformly random `q`-element subset (pp.8, 29). -/
def unifProb {V : Type} [Fintype V] (q : ℕ) (E : Finset V → Prop) : ℝ :=
  (((Finset.univ : Finset V).powersetCard q).filter E).card / ((Fintype.card V).choose q : ℝ)

end HindsightGain.Uniform.Supplement


