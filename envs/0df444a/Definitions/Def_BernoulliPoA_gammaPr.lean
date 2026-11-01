-- Prove2me | Definitions.Def_BernoulliPoA_gammaPr
-- name    : BernoulliPoA_gammaPr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:46.756235+00:00
-- url     : https://prove2.me/theorems/fec86bad-b6a9-40c3-9e28-f3b4ef4118a9
-- title:
--   The prophet smoothness bound $\gamma_{\mathsf{pr}}(\mathcal C,q)$
-- statement:
--   The best ratio obtainable from $(\lambda,\mu,q)$-smoothness:
--   $$
--   \gamma_{\mathsf{pr}}(\mathcal C,q)=\inf\bigl\{\lambda/(1-\mu):(\lambda,\mu)\text{ satisfies (28)}\bigr\}.
--   $$
--
--   **Formalization Note** The value lies in $[0,\infty]$, and the infimum of the empty set is $\infty$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (29), p.19

import Mathlib
import Definitions.Def_BernoulliPoA_prophetSmoothParams
open scoped ENNReal

namespace BernoulliPoA

/-- **The prophet smoothness bound** `γ_pr(C, q)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §3.2, display (29), p.19:
`γ_pr(C, q) = inf {λ / (1 - μ) : (λ, μ) satisfies (28)}`.

**Formalization Note** The value lies in `ℝ≥0∞`, with `inf ∅ = ⊤`, which is the value `γ_pr(C, q) = ∞` of the proof of Lemma EC.1
(p.ec1). -/
noncomputable def gammaPr (C : Set (ℕ → ℝ)) (q : ℝ) : ℝ≥0∞ :=
  ⨅ x ∈ prophetSmoothParams C q, ENNReal.ofReal (x.1 / (1 - x.2))

end BernoulliPoA


