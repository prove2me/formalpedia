-- Prove2me | Definitions.Def_BayesBAI_tapeProb
-- name    : BayesBAI_tapeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:14.928802+00:00
-- url     : https://prove2.me/theorems/0ffb26e0-5b01-4711-bc56-79b8881410f0
-- title:
--   The probability of a reward tape under means $\mu$
-- statement:
--   For means $\mu=(\mu_1,\dots,\mu_K)$, the tape has independent entries with $\omega_{i,t}\sim\mathrm{Bernoulli}(\mu_i)$, so that
--   $$
--   \mathbb P_\mu(\omega)=\prod_{i\in[K]}\prod_{t\in[T]}\mu_i^{\omega_{i,t}}(1-\mu_i)^{1-\omega_{i,t}}.
--   $$
--   This is the law of the rewards of the paper's bandit model.
--
--   **Formalization Note.** The formula is a probability mass function when every $\mu_i\in[0,1]$; statements using it assume this.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1, p.1

import Mathlib
import Definitions.Def_BayesBAI_Tape

namespace BayesBAI

/-- The law of the reward tape under means `μ`: entries are independent and entry `(i, t)` is
Bernoulli(`μ i`), for Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, §1, p.1.

**Formalization Note.** This is a probability mass function when every `μ i ∈ [0, 1]`; every statement
that uses it assumes that. -/
noncomputable def tapeProb {K T : ℕ} (μ : Fin K → ℝ) (ω : Tape K T) : ℝ :=
  ∏ i, ∏ t, if ω i t then μ i else 1 - μ i

end BayesBAI


