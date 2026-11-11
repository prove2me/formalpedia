-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_Potential
-- name    : OCEClocks_DisplayAds_Potential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:22:56.897074+00:00
-- url     : https://prove2.me/theorems/fb81ea57-8e00-4c34-8637-62e3dd3261e1
-- title:
--   The potential $\Gamma$ (6) and the target ratio $\Gamma^\star=\pi\Gamma$ (7)
-- statement:
--   Fix $\lambda>0$. The **infinitesimal-request age process** started at age $a$ behaves as follows. Its age grows at unit rate, and Poisson arrivals come at rate $\lambda$. At an arrival whose pre-arrival age is $b$, the process stops (the resource wins) with probability $e^{-\lambda e^{-\lambda b}}$, and otherwise the age resets to $0$. Independently, the process stops at rate $e^{-\lambda}$.
--
--   Let $(M^\star_x\mathbf 1)(a)$ be the probability that this process has not stopped by time $x$. With gaps $S_k$ i.i.d. $\mathrm{Exp}(\lambda)$, arrivals $\tau_k=S_0+\dots+S_k$, and pre-arrival ages $b_0=a+S_0$ and $b_k=S_k$ ($k\ge1$),
--
--   $$(M^\star_x\mathbf 1)(a)=e^{-e^{-\lambda}x}\ \mathbb E\Big[\prod_{k:\ \tau_k\le x}\big(1-e^{-\lambda e^{-\lambda b_k}}\big)\Big].$$
--
--   The **potential** (6) and the **target ratio** (7) are
--
--   $$\Gamma(a)=1-\int_0^\infty e^{-x}\,(M^\star_x\mathbf 1)(a)\,dx,\qquad \Gamma^\star=\pi\Gamma=\int_0^\infty\lambda e^{-\lambda a}\,\Gamma(a)\,da.$$
--
--   $\Gamma(a)$ is the conditional competitive ratio given initial age $a$. The dual variables of the primal-dual analysis are measured in $\Gamma$, and $\Gamma^\star$ is the competitive ratio the algorithm attains (Appendix B.2: $\Gamma^\star>0.556$ at $\lambda=9/2$).
--
--   **Formalization Note** The paper introduces $M^\star_x=\lim_{\varepsilon\downarrow0}(M_\varepsilon)^{x/\varepsilon}$, formally $\exp(xL_M)$, and identifies $(M^\star_x\mathbf 1)(a)$ with the survival probability above (p. 11; proof of Lemma 30). `survivalStar λ x a` defines it as that survival probability. The product over the almost surely finitely many arrivals by time $x$ is the infimum over $K$ of the partial products over $k<K$, with factor $1$ when $\tau_k>x$; all factors lie in $[0,1]$. `potential λ a` is $\Gamma(a)$ and `targetRatio λ` is $\Gamma^\star$. $\Gamma$ is not defined through the closed form (31), which is Lemma 30.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), pp. 11–12, §4.2 (infinitesimal-request age process; eqs. (6), (7)); p. 38, proof of Lemma 30

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Kernels

open MeasureTheory ProbabilityTheory

namespace OCEClocks.DisplayAds

/-!
# The potential `Γ` and the target ratio `Γ⋆` ((6), (7))

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), pp. 11–12, §4.2, eqs. (6), (7); the infinitesimal-request age
process is described on p. 11 and in the proof of Lemma 30 (p. 38).

`(M⋆_x 1)(a)` is the probability that the infinitesimal-request age process started at age `a`
has not stopped by time `x`: the age grows at unit rate, Poisson arrivals come at rate `λ`; at an
arrival whose pre-arrival age is `b` the process stops (a win) with probability `e^{-λ e^{-λ b}}`
and otherwise resets the age to `0`; independently it stops at rate `e^{-λ}`.
-/

/-- The probability `1 - e^{-λ e^{-λ b}}` of losing at an arrival with pre-arrival age `b`. -/
noncomputable def arrivalLossProb (lam b : ℝ) : ℝ :=
  1 - Real.exp (-(lam * Real.exp (-(lam * b))))

/-- The pre-arrival age of the `k`-th arrival `τ_k` of the process started at age `a`:
`a + S_0` for the first arrival, `S_k` (the gap since the previous arrival) afterwards. -/
def preArrivalAge (a : ℝ) (S : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a + S 0 else S k

/-- `(M⋆_x 1)(a)`: the survival probability up to time `x` of the infinitesimal-request age
process started at age `a`,
`e^{-e^{-λ} x} · E[∏_{k : τ_k ≤ x} (1 - e^{-λ e^{-λ b_k}})]`, with i.i.d. `Exp(λ)` gaps. The product
over the (almost surely finitely many) arrivals by time `x` is the infimum of its partial products,
whose factors lie in `[0, 1]`. -/
noncomputable def survivalStar (lam x a : ℝ) : ℝ :=
  Real.exp (-(Real.exp (-lam) * x)) *
    ∫ S, (⨅ K : ℕ, ∏ k ∈ Finset.range K,
      (if startedArrival S k ≤ x then arrivalLossProb lam (preArrivalAge a S k) else 1))
      ∂Measure.infinitePi (fun _ : ℕ => expMeasure lam)

/-- The potential (6): `Γ(a) = 1 - ∫_0^∞ e^{-x} (M⋆_x 1)(a) dx`. -/
noncomputable def potential (lam a : ℝ) : ℝ :=
  1 - ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * survivalStar lam x a

/-- The target ratio (7): `Γ⋆ = πΓ = ∫ Γ dπ` with `π = Exp(λ)`. -/
noncomputable def targetRatio (lam : ℝ) : ℝ :=
  ∫ a, potential lam a ∂stationaryAge lam

end OCEClocks.DisplayAds


