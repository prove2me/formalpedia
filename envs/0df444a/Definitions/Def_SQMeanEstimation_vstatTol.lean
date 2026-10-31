-- Prove2me | Definitions.Def_SQMeanEstimation_vstatTol
-- name    : SQMeanEstimation_vstatTol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:59.378577+00:00
-- url     : https://prove2.me/theorems/96d618ec-2c2a-43b5-98d9-8f391ebe17cb
-- title:
--   VSTAT tolerance $\max\{1/n,\sqrt{p(1-p)/n}\}$
-- statement:
--   The **VSTAT tolerance** for parameter $n>0$ and a query of true mean $p$ is
--   $$
--   \tau_n(p)=\max\Big\{\frac1n,\ \sqrt{\frac{p(1-p)}{n}}\Big\}.
--   $$
--   By Definition 2.1, the oracle $\mathrm{VSTAT}_D(n)$, given a query $\phi:\mathcal W\to[0,1]$, may return any value $v$ with $|v-p|\le\tau_n(p)$, where $p=\mathbf E_{w\sim D}[\phi(w)]$. The tolerance is small when $p$ is close to $0$ or $1$, which is what makes VSTAT capture the variance of the query.
--
--   **Formalization Note** The parameter $n$ is a real number: the paper's oracle parameters, such as $(16\log(d)/\varepsilon)^p$ in Theorem 3.15, are not integers.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Definition 2.1, p.11

import Mathlib

namespace SQMeanEstimation

/-- **Tolerance of the VSTAT oracle.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Definition 2.1, p.11: "A statistical query oracle
VSTAT_D(n) is an oracle that given as input any function φ : W → [0, 1] returns some value v such
that |v − p| ≤ max{1/n, √(p(1−p)/n)}, where p ≐ E_{w∼D}[φ(w)]."

`vstatTol n p = max (1/n) (√(p(1−p)/n))` is the allowed error of an answer to a query whose true
mean is `p`.

**Formalization Note.** `n` is a real number: the paper's oracle parameters, such as
`(16 log(d)/ε)^p` in Theorem 3.15, are not integers. -/
noncomputable def vstatTol (n p : ℝ) : ℝ :=
  max (1 / n) (Real.sqrt (p * (1 - p) / n))

end SQMeanEstimation


