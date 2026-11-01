-- Prove2me | Definitions.Def_BernoulliPoA_beta
-- name    : BernoulliPoA_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:58.552719+00:00
-- url     : https://prove2.me/theorems/06356bad-28ae-49e2-b9d7-a5cbcc9cf2ab
-- title:
--   The affine functions $\beta_{c,k,m}$
-- statement:
--   For a triple $(c,k,m)$ with $c(k)>0$ and $k\ge 1$,
--   $$
--   \beta_{c,k,m}(\omega)=\frac{c^q(1+m)}{q\,c(k)}\,\omega+\frac{m\,c^q(m)}{k\,c(k)}\,(1-\omega).
--   $$
--
--   **Formalization Note** The quotients are real divisions, so the function is meaningful only under $c(k)>0$, $k\ge1$. Every theorem of the mission reads it under this hypothesis.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (EC.1), p.ec1

import Mathlib
import Definitions.Def_BernoulliPoA_binomExp

namespace BernoulliPoA

/-- **The affine function** `β_{c,k,m}`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Lemma EC.1, display (EC.1), p.ec1:
`β_{c,k,m}(ω) = c^q(1 + m) / (q c(k)) · ω + m c^q(m) / (k c(k)) · (1 - ω)`.

**Formalization Note** The argument `t` is the triple `(c, k, m)`. The quotients are real divisions, meaningful when `c(k) > 0`
and `k ≥ 1`; every theorem of this mission reads `beta` only under this hypothesis (Lemma EC.1 is split accordingly). -/
noncomputable def beta (q : ℝ) (t : (ℕ → ℝ) × ℕ × ℕ) (ω : ℝ) : ℝ :=
  binomExp t.1 q (1 + t.2.2) / (q * t.1 t.2.1) * ω +
    (t.2.2 : ℝ) * binomExp t.1 q t.2.2 / ((t.2.1 : ℝ) * t.1 t.2.1) * (1 - ω)

end BernoulliPoA


