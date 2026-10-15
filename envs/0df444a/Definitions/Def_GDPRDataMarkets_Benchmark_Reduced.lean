-- Prove2me | Definitions.Def_GDPRDataMarkets_Benchmark_Reduced
-- name    : GDPRDataMarkets_Benchmark_Reduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:08.157012+00:00
-- url     : https://prove2.me/theorems/2c2bdda8-2356-44ae-93df-4be594149b65
-- title:
--   pp. 49–51 — the reduced thresholds, second-period price and first-period objectives of the proof of Proposition 2
-- statement:
--   The proof of Proposition 2 reduces the benchmark game to one-dimensional optimization problems in the first-period price $p_1$. This file names the expressions it uses, with $r^B_M(v)=(1+\mu-\sigma)v$. None of them enters the equilibrium definition; they are used only to state the intermediate steps of the proof.
--
--   1. The threshold and second-period price when some first-period non-buyers buy in period 2 (p. 49):
--   $$v^B_M(p_1)=\frac{2p_1+(2+\delta)c}{2-\delta+2\delta\sigma},\qquad p^B_{2M}(p_1)=\frac{p_1+\delta(1-\sigma)c}{2-\delta+2\delta\sigma}.$$
--   2. The first-period objective in that regime (p. 49):
--   $$\pi_S(p_1)=\int_{v^B_M(p_1)}^{1}\big(p_1+\delta r^B_M(v)\big)\,dv+\delta\,p^B_{2M}(p_1)\big[v^B_M(p_1)-(p^B_{2M}(p_1)+c)\big].$$
--   3. The threshold and objective when no first-period non-buyer buys in period 2 (p. 50):
--   $$v_N(p_1)=\frac{p_1+(1+\delta)c}{1+\delta\sigma},\qquad \pi_N(p_1)=\int_{v_N(p_1)}^{1}\big(p_1+\delta r^B_M(v)\big)\,dv.$$
--   4. The price of eq. (8):
--   $$p_8=\frac{(1+\delta\sigma)^2-(1+\delta)(1+\delta+\delta\mu)c}{2+\delta+\delta\mu+\delta\sigma}.$$
--
--   **Formalization Note.** The integrals are oriented interval integrals of a polynomial, so $\pi_S$ and $\pi_N$ are the paper's quadratic polynomials in $p_1$ for every real $p_1$, including prices at which the threshold lies outside $[0,1]$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), pp. 49–50, Appendix, proof of Proposition 2, eqs. (6)–(8)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model

namespace GDPRDataMarkets.Benchmark

/-! The reduced expressions of the appendix proof of Proposition 2 (pp. 49–51). They are not
part of the equilibrium definition `IsEquilibrium`; the milestones use them to state the paper's
intermediate optimization problems. -/

/-- `v^B_M(p₁) = (2p₁ + (2 + δ)c)/(2 − δ + 2δσ)`, the first-period threshold when some
first-period non-buyers buy in period 2 (p. 49). -/
noncomputable def vB (P : Params) (p1 : ℝ) : ℝ :=
  (2 * p1 + (2 + P.d) * P.c) / (2 - P.d + 2 * P.d * P.sigma)

/-- `p^B_2M(p₁) = (p₁ + δ(1 − σ)c)/(2 − δ + 2δσ)` (p. 49). -/
noncomputable def qB (P : Params) (p1 : ℝ) : ℝ :=
  (p1 + P.d * (1 - P.sigma) * P.c) / (2 - P.d + 2 * P.d * P.sigma)

/-- The first-period objective of p. 49:
`∫_{v^B_M(p₁)}^1 (p₁ + δ r^B_M(v)) dv + δ p^B_2M(p₁)[v^B_M(p₁) − (p^B_2M(p₁) + c)]`,
with `r^B_M(v) = (1 + μ − σ)v`. -/
noncomputable def piS (P : Params) (p1 : ℝ) : ℝ :=
  (∫ v in (vB P p1)..1, (p1 + P.d * ((1 + P.mu - P.sigma) * v)))
  + P.d * qB P p1 * (vB P p1 - (qB P p1 + P.c))

/-- `v^B_M(p₁) = (p₁ + (1 + δ)c)/(1 + δσ)`, the first-period threshold when no first-period
non-buyer buys in period 2 (p. 50). -/
noncomputable def vN (P : Params) (p1 : ℝ) : ℝ := (p1 + (1 + P.d) * P.c) / (1 + P.d * P.sigma)

/-- The first-period objective of p. 50: `∫_{v^B_M(p₁)}^1 (p₁ + δ r^B_M(v)) dv` with
`r^B_M(v) = (1 + μ − σ)v`. -/
noncomputable def piN (P : Params) (p1 : ℝ) : ℝ :=
  ∫ v in (vN P p1)..1, (p1 + P.d * ((1 + P.mu - P.sigma) * v))

/-- The price of eq. (8), p. 50: `((1 + δσ)² − (1 + δ)(1 + δ + δμ)c)/(2 + δ + δμ + δσ)`. -/
noncomputable def p8 (P : Params) : ℝ :=
  ((1 + P.d * P.sigma) ^ 2 - (1 + P.d) * (1 + P.d + P.d * P.mu) * P.c)
    / (2 + P.d + P.d * P.mu + P.d * P.sigma)

end GDPRDataMarkets.Benchmark


