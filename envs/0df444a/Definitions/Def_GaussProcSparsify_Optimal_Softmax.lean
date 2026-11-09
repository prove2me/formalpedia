-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Softmax
-- name    : GaussProcSparsify_Optimal_Softmax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:22.20758+00:00
-- url     : https://prove2.me/theorems/c7cec9d6-65cd-4d71-8348-64a7237c5ae8
-- title:
--   Softmax interpolation and its weights
-- statement:
--   Let $\iota$ be a finite index set, let $v_t(\theta)\in\mathbb R^n$ and $a_t(\theta)\in\mathbb R$ be paths, and let $\beta>0$. Define
--   $$H_\theta(g)=\frac1\beta\log\sum_{t\in\iota}\exp\bigl(\beta(\langle g,v_t(\theta)\rangle+a_t(\theta))\bigr).$$
--   Its weights are
--   $$\omega_t^\theta(g)=\frac{\exp(\beta(\langle g,v_t(\theta)\rangle+a_t(\theta)))}{\sum_{r\in\iota}\exp(\beta(\langle g,v_r(\theta)\rangle+a_r(\theta)))}.$$
--   The module also defines the candidate velocity $\sum_t\omega_t^\theta(g)(\langle g,v'_t(\theta)\rangle+a'_t(\theta))$. It does not assert a chain rule or an approximation bound. Lemmas 11 and 24 share this exact formula. Their hypotheses require the index set to be nonempty, so the logarithm and denominator have their intended positive arguments.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), equation (10), PDF p. 14 (printed p. 13); Lemma 24, PDF p. 39 (printed p. 38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

namespace GaussProcSparsify.Optimal

/-- H_θ in (10), PDF p. 14, and Lemma 24, PDF p. 39.
Theorems require a nonempty finite index type and β > 0. -/
noncomputable def softmax {n : ℕ} {ι : Type} [Fintype ι] (β : ℝ)
    (v : ι → ℝ → Vec n) (a : ι → ℝ → ℝ) (θ : ℝ) (g : Vec n) : ℝ :=
  Real.log (∑ t, Real.exp (β * (inner ℝ g (v t θ) + a t θ))) / β

/-- Softmax weights of (10) / Lemma 24. The denominator is positive on nonempty indices. -/
noncomputable def softmaxWeight {n : ℕ} {ι : Type} [Fintype ι] (β : ℝ)
    (v : ι → ℝ → Vec n) (a : ι → ℝ → ℝ) (θ : ℝ) (g : Vec n) (t : ι) : ℝ :=
  Real.exp (β * (inner ℝ g (v t θ) + a t θ)) /
    (∑ r, Real.exp (β * (inner ℝ g (v r θ) + a r θ)))

/-- The pointwise derivative displayed in Lemma 24, PDF p. 39.
Ambient derivatives agree with derivatives within [0,1] at almost every time. -/
noncomputable def softmaxVelocity {n : ℕ} {ι : Type} [Fintype ι] (β : ℝ)
    (v : ι → ℝ → Vec n) (a : ι → ℝ → ℝ) (θ : ℝ) (g : Vec n) : ℝ :=
  ∑ t, softmaxWeight β v a θ g t *
    (inner ℝ g (deriv (v t) θ) + deriv (a t) θ)

end GaussProcSparsify.Optimal


