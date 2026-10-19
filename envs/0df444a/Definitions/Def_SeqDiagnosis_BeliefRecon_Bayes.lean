-- Prove2me | Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes
-- name    : SeqDiagnosis_BeliefRecon_Bayes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:42.416145+00:00
-- url     : https://prove2.me/theorems/df02c21f-fbc3-4a50-8167-5fb49fb0a0bd
-- title:
--   §2, p. 7 — one-step Bayesian operator, sequential posterior, and reachable beliefs
-- statement:
--   Fix $N+1$ hidden classes and an observation space $\mathcal Y$. For class densities $f_j$, a current belief $q=(q_0,\ldots,q_N)$, and an observation $y$, the one-step Bayesian operator is
--
--   $$\mathcal B(q,y)_j=\frac{q_jf_j(y)}{\sum_{i=0}^N q_i f_i(y)}.$$
--
--   For an arrival-ordered list $y_1,\ldots,y_t$, the posterior $\Pi_t$ starts at the prior $\theta$ and applies this operator successively. The reachable set at time $t$ consists exactly of the posteriors obtained from lists of length $t$.
--
--   These definitions isolate the generic sequential Bayes update used by the paper's exponential-tilting model. Positivity of the denominator is established in a separate theorem under the model assumptions.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, pp. 6–7 (PDF 6–7), §2, Bayesian operator

import Mathlib

namespace SeqDiagnosis.BeliefRecon

/-- One observation updates every class weight by its likelihood and normalizes it. -/
noncomputable def bayes {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (q : Fin (N + 1) → ℝ) (y : Y) :
    Fin (N + 1) → ℝ :=
  fun j => q j * f j y / ∑ i, q i * f i y

/-- The posterior is obtained by updating in the order of the observations. -/
noncomputable def belief {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (θ : Fin (N + 1) → ℝ) (ys : List Y) :
    Fin (N + 1) → ℝ :=
  ys.foldl (bayes f) θ

/-- Beliefs reachable after exactly `t` observations. -/
def reachable {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (θ : Fin (N + 1) → ℝ) (t : ℕ) :
    Set (Fin (N + 1) → ℝ) :=
  {q | ∃ ys : List Y, ys.length = t ∧ belief f θ ys = q}

end SeqDiagnosis.BeliefRecon


