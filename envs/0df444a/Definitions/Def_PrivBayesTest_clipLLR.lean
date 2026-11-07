-- Prove2me | Definitions.Def_PrivBayesTest_clipLLR
-- name    : PrivBayesTest_clipLLR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:52.059415+00:00
-- url     : https://prove2.me/theorems/4f1e4763-8b60-4050-a858-15d4a63856f8
-- title:
--   Clipped log-likelihood ratio $\bar\ell=\min\{c_2,\max\{c_1,\log(p/q)\}\}$
-- statement:
--   Let $P,Q$ be probability measures on $\mathcal X$ with densities $p=dP/d(P+Q)$ and $q=dQ/d(P+Q)$, and let $c_1\le c_2$ be real numbers. The **clipped log-likelihood ratio** is
--
--   $$
--   \bar\ell(x) \;=\; \min\{c_2,\ \max\{c_1,\ \log(p(x)/q(x))\}\},
--   $$
--
--   where $\log(p/q)=+\infty$ if $q=0<p$ and $-\infty$ if $p=0<q$. It takes values in $[c_1,c_2]$. In Proposition 2.5 the dual optimizer is a scaled and shifted copy of $\bar\ell$, and in §2.3 the private test sums $\bar\ell$ over the sample.
--
--   **Formalization Note** $\log(p/q)$ is computed as an extended real and the clipped value is returned as a real number. On the $(P+Q)$-null set where $p=q=0$ the value is $c_1$; any value would do.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Proposition 2.5 item 3, p.11

import Mathlib

open MeasureTheory

namespace PrivBayesTest

/-- The **clipped log-likelihood ratio** `ℓ̄ = min{c₂, max{c₁, log(p/q)}}` of
Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Proposition 2.5 item 3, p.11, where `p` and `q` are the densities of `P` and `Q` with respect
to the dominating measure `P + Q`.

**Formalization Note** `log(p/q)` is computed in `EReal` as `ENNReal.log (p / q)`: it is `+∞` where
`q = 0 < p` and `−∞` where `p = 0 < q` (the paper's conventions), and the clip then gives `c₂`,
respectively `c₁`. On the `(P+Q)`-null set `p = q = 0` the value is `c₁` (any value would do). For
`c₁ ≤ c₂` the result lies in `[c₁, c₂]` and is returned as a real number. -/
noncomputable def clipLLR {X : Type*} [MeasurableSpace X] (P Q : Measure X) (c₁ c₂ : ℝ) (x : X) : ℝ :=
  (min (c₂ : EReal) (max (c₁ : EReal)
    (ENNReal.log (P.rnDeriv (P + Q) x / Q.rnDeriv (P + Q) x)))).toReal

end PrivBayesTest


