-- Prove2me | Definitions.Def_ErlangA_Staffing_Model
-- name    : ErlangA_Staffing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:06.669115+00:00
-- url     : https://prove2.me/theorems/487aabc3-cac4-4a23-ae03-85772c566257
-- title:
--   Erlang-A in the QED regime: stationary law $\pi$, $P_N\{W>0\}$, $P_N\{Ab\}$, $P_N\{Bl\}$, the function $w(x,y)$, the limit density $f$ and $\gamma(x,y)$
-- statement:
--   The **Erlang-A queue** ($M/M/N+M$) has Poisson arrivals at rate $\lambda>0$, $N\ge1$ statistically identical agents with exponential service times of rate $\mu>0$, an unlimited waiting room served in order of arrival, and customers whose patience is exponential with rate $\theta>0$, independent of everything else; a waiting customer whose wait reaches its patience abandons. The number of customers in the system is a birth–death process with birth rate $\lambda$ and death rate $\min(k,N)\mu+(k-N)^+\theta$ in state $k$. This module defines the objects in which Theorem 4 of the paper is stated.
--
--   1. **Stationary law** (Appendix B, p. 222, with an unlimited buffer). With the unnormalized weights
--   $$
--   v_k=\begin{cases}\dfrac{(\lambda/\mu)^k}{k!}, & 0\le k\le N,\\[2mm] \displaystyle\prod_{j=N+1}^{k}\frac{\lambda}{N\mu+(j-N)\theta}\cdot\frac{(\lambda/\mu)^N}{N!}, & k>N,\end{cases}
--   $$
--   the stationary probabilities are $\pi_k=v_k/\sum_{j\ge0}v_j$.
--   2. **Delay probability** $P_N\{W>0\}$: the probability that a customer arriving in steady state has to wait. By PASTA and equation (4), p. 221,
--   $$
--   P_N\{W>0\}=\sum_{k\ge N}\pi_k .
--   $$
--   3. **Abandonment probability** $P_N\{Ab\}$: the probability that a customer arriving in steady state abandons (Table 3, p. 215). An arrival that finds $N+n$ customers in the system waits a sum of independent exponentials of rates $N\mu+n\theta,\dots,N\mu$ and abandons with probability $(n+1)\theta/(N\mu+(n+1)\theta)$, so
--   $$
--   P_N\{Ab\}=\sum_{n\ge0}\pi_{N+n}\,\frac{(n+1)\theta}{N\mu+(n+1)\theta}=\frac{\theta}{\lambda}\sum_{k>N}(k-N)\,\pi_k ,
--   $$
--   the second form being the balance equation (2), p. 217.
--   4. **Blocking probability** $P_N\{Bl\}=E(\lambda/\mu,N)$, Erlang's formula for the loss system $M/M/N/N$ (the published `KellyStochasticNetworks.erlang`).
--   5. **The function $w$** of Theorem 3, p. 217: with $h(x)=\varphi(x)/[1-\Phi(x)]$ the hazard rate of the standard normal distribution,
--   $$
--   w(x,y)=\Bigl[1+\frac{h(-xy)}{y\,h(x)}\Bigr]^{-1}.
--   $$
--   6. **The limit density** $f$ of the scaled stationary queue when $0<\theta<\infty$ (proof of Theorem 2\*, Part 2, p. 225): with $c=\sqrt{\theta/\mu}\,h(\beta\sqrt{\mu/\theta})\,w(-\beta,\sqrt{\mu/\theta})$,
--   $$
--   f(x)=\begin{cases} c\,\dfrac{\varphi(x+\beta)}{\varphi(\beta)}, & x\le0,\\[2mm] c\,\dfrac{\varphi(x\sqrt{\theta/\mu}+\beta\sqrt{\mu/\theta})}{\varphi(\beta\sqrt{\mu/\theta})}, & x>0.\end{cases}
--   $$
--   7. **The lower incomplete gamma function** (Appendix B, p. 222): $\gamma(x,y)=\int_0^y t^{x-1}e^{-t}\,dt$, $y>0$.
--
--   These are the quantities whose square-root-staffing asymptotics are the subject of Theorem 4 and Lemmas 1–2.
--
--   **Formalization Note** The normalizing sum and the sums defining $P_N\{W>0\}$ and $P_N\{Ab\}$ are `tsum`s; for $\lambda,\mu,\theta>0$ the weights are summable (every term of the $k>N$ product is at most $\lambda/(N\mu+(k-N)\theta)\to0$), so these are genuine series. Every theorem using them assumes $\lambda,\mu,\theta>0$. $\varphi$, $\Phi$ and $h$ are the published `DimCallCenters.Rationalized.stdPdf`, `stdCdf` and `hazard`. On p. 225 the $x\le0$ line of $f$ is printed as $h(\beta\sqrt{\mu/\theta}\cdot w(\dots)$ with a parenthesis dropped; the corrected form is defined (it integrates to one, and its mass on $(0,\infty)$ is $w(-\beta,\sqrt{\mu/\theta})$). The same objects are defined in the sibling mission on Theorem 1 under `ErlangA.Abandonment`; they are restated here because unpublished drafts cannot be imported.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 215 (Table 3), p. 217 (φ, Φ, h; Theorem 3, w; eq. (2)), pp. 221–222 (Appendix B, eq. (4), π_k, γ), p. 225 (proof of Theorem 2*, Part 2, density f)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Abandonment_Model

namespace ErlangA.Staffing

open DimCallCenters.Rationalized

/-- `P_N{W > 0}`: the probability that a customer arriving in steady state has to wait,
`P{V > 0} = 1 − Σ_{k<N} π_k = Σ_{k ≥ N} π_k` ((4), App. B, p. 221, with PASTA). -/
noncomputable def probWait (N : ℕ) (lam μ θ : ℝ) : ℝ :=
  ∑' n : ℕ, ErlangA.Abandonment.stationaryDist N lam μ θ (N + n)

/-- `P_N{Bl}`: the Erlang-B blocking probability of the `M/M/N/N` loss system with offered load
`λ/μ` and `N` servers. -/
noncomputable def probBlock (N : ℕ) (lam μ : ℝ) : ℝ :=
  KellyStochasticNetworks.erlang (lam / μ) N

/-- The function `w(x, y) = [1 + h(−xy)/(y·h(x))]^{−1}` of Theorem 3, p. 217, where `h` is the
hazard rate of the standard normal distribution. The paper uses it with `y = √(μ/θ) > 0`. -/
noncomputable def w (x y : ℝ) : ℝ :=
  (1 + hazard (-(x * y)) / (y * hazard x))⁻¹

/-- The density `f` of the weak limit `q(∞)` of the scaled stationary queue
`(Q_N(∞) − N)/√N` when `0 < θ < ∞` (App. C, proof of Theorem 2*, Part 2, p. 225, with the
dropped parenthesis of the `x ≤ 0` line restored): with `c = √(θ/μ)·h(β√(μ/θ))·w(−β, √(μ/θ))`,
`f(x) = c·φ(x + β)/φ(β)` for `x ≤ 0` and `f(x) = c·φ(x√(θ/μ) + β√(μ/θ))/φ(β√(μ/θ))` for `x > 0`. -/
noncomputable def limitDensity (β μ θ : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) * w (-β) (Real.sqrt (μ / θ)) *
    (if x ≤ 0 then stdPdf (x + β) / stdPdf β
     else stdPdf (x * Real.sqrt (θ / μ) + β * Real.sqrt (μ / θ)) /
       stdPdf (β * Real.sqrt (μ / θ)))

/-- The lower incomplete gamma function `γ(x, y) = ∫_0^y t^{x−1} e^{−t} dt`, `y > 0`
(App. B, p. 222). -/
noncomputable def lowerGamma (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, t ^ (x - 1) * Real.exp (-t)

end ErlangA.Staffing


