-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureH
-- name    : KallMayerSLP_SimpleRecourse_mixtureH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:29.88954+00:00
-- url     : https://prove2.me/theorems/91012601-3e2e-462b-b2c6-3da6fb332467
-- title:
--   The function $H(\xi)=\sum_k\alpha_kF(\xi+u_k)+\sum_k\beta_kF(\xi-l_k)$
-- statement:
--   With $F_{\tilde\xi}$ the distribution function of $\tilde\xi$,
--
--   $$
--   H(\xi) = \sum_{k=0}^{K-1}\alpha_k F_{\tilde\xi}(\xi+u_k) + \sum_{k=0}^{K-1}\beta_k F_{\tilde\xi}(\xi-l_k).
--   $$
--
--   $F_{\tilde\xi}(\cdot+u_k)$ is the distribution function of $\tilde\xi-u_k$ and $F_{\tilde\xi}(\cdot-l_k)$ that of $\tilde\xi+l_k$, so $H$ is a weighted sum of distribution functions of shifted copies of $\tilde\xi$.
--
--   **Formalization Note** $F_{\tilde\xi}$ is Mathlib's `cdf P` of the law $P$ of $\tilde\xi$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, p.239 (PDF 248)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **The function `H`, p.239.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.239 (PDF 248):
`H(ξ) = Σ_{k=0}^{K−1} α_k F_ξ̃(ξ + u_k) + Σ_{k=0}^{K−1} β_k F_ξ̃(ξ − l_k)`.

**Formalization Note.** `F_ξ̃` is `cdf P`, the distribution function of the law `P` of `ξ̃`
(`cdf P x = P(−∞, x]` for a probability measure). -/
noncomputable def mixtureH {K : ℕ} (α β u l : Fin K → ℝ) (P : Measure ℝ) (ξ : ℝ) : ℝ :=
  ∑ k, α k * cdf P (ξ + u k) + ∑ k, β k * cdf P (ξ - l k)

end KallMayerSLP.SimpleRecourse


