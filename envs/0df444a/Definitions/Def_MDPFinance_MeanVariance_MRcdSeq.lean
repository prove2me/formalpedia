-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_MRcdSeq
-- name    : MDPFinance_MeanVariance_MRcdSeq
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:17.371212+00:00
-- url     : https://prove2.me/theorems/9c1ce0a7-ad45-4547-983f-59c07fb02cba
-- title:
--   The sequences $c_n$, $d_n$ of $P(\lambda,b)$'s value function
-- statement:
--   For $n=0,\dots,N$:
--   $$c_n := \Big(\lambda+\frac{1}{1-\gamma}\Big)\Big(\frac{1-p}{1-q}\Big)^{N-n}
--   \qquad\text{(`cSeq`)}, \qquad d_n := \lambda\Big(\frac{p}{q}\Big)^{N-n}
--   \qquad\text{(`dSeq`)}$$
--   where $q:=(1-d)/(u-d)$ is the risk-neutral up-probability. These are the coefficients of
--   Theorem 4.7.1's explicit value function $V_n(x) = c_n(x+b)^- - d_n(x+b)^+$.
--
--   **Formalization Note.** Named `cSeq`/`dSeq` locally under `MeanRiskMarket`, distinct from the
--   mean-variance model's own $(d_n)$ of Eq. (4.34) (chunk pitfall: both use the letter $d$ in the
--   book's own notation for two unrelated sequences).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 126, PDF 140, unnumbered display preceding Theorem 4.7.1

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `c_n := (λ + (1-γ)⁻¹)((1-p)/(1-q))^{N-n}` (Bäuerle–Rieder, p. 126, PDF 140). -/
noncomputable def MeanRiskMarket.cSeq (M : MeanRiskMarket Ω) (lam : ℝ) (n : ℕ) : ℝ :=
  (lam + (1 - M.γ)⁻¹) * ((1 - M.p) / (1 - M.q)) ^ (M.N - n)

/-- `d_n := λ(p/q)^{N-n}` (Bäuerle–Rieder, p. 126, PDF 140). -/
noncomputable def MeanRiskMarket.dSeq (M : MeanRiskMarket Ω) (lam : ℝ) (n : ℕ) : ℝ :=
  lam * (M.p / M.q) ^ (M.N - n)

end MDPFinance.MeanVariance


