-- Prove2me | Definitions.Def_MSetBandit_cvec
-- name    : MSetBandit_cvec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:44.528091+00:00
-- url     : https://prove2.me/theorems/2bfbc6cd-acfb-4cc6-8d37-1dba192c6f70
-- title:
--   The coefficient vector $c_p$ of (13)
-- statement:
--   For $p\in\Delta(\mathcal X)$ with marginal vector $\mu=\mu(p)$, the vector $c_p\in\mathbb R^d$ has coordinates
--   $$
--   c_{p,i}=4\left(\frac{1+\sum_{j=1}^d\frac{\mu_j}{1-\mu_j}}{m}+\frac{1-2\mu_i}{\mu_i(1-\mu_i)}\right),\qquad i\in[d].
--   $$
--   By Lemma 1, $c_p^\top x=4\phi_p(x)$ for every action $x$, which makes the surrogate loss of Algorithm 1 linear in $x$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Lemma 1, Eq. (13), p.11

import Mathlib
import Definitions.Def_MSetBandit_marg

namespace MSetBandit

/-- **The coefficient vector `c_p` of (13).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Lemma 1, Eq. (13), p.11: for every
`i ∈ [d]`,
`c_{p,i} := 4 ( (1 + Σ_{j=1}^d µ_j/(1 − µ_j)) / m + (1 − 2µ_i)/(µ_i(1 − µ_i)) )`, `µ = µ(p)`.

**Formalization Note.** `m` is the action size, a parameter of the action type; the division by
`m` is real division. -/
noncomputable def cvec {d m : ℕ} (p : Action d m → ℝ) : Fin d → ℝ :=
  fun i => 4 * ((1 + ∑ j, marg p j / (1 - marg p j)) / (m : ℝ)
    + (1 - 2 * marg p i) / (marg p i * (1 - marg p i)))

end MSetBandit


