-- Prove2me | Definitions.Def_MHSpectralGap_LocalLip_Assumption210
-- name    : MHSpectralGap_LocalLip_Assumption210
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:56:15.883337+00:00
-- url     : https://prove2.me/theorems/d4f49520-c5c1-47f1-9168-55ab82e92244
-- title:
--   Assumption 2.10, p. 12 — the pCN acceptance probability is bounded below near the proposal mean
-- statement:
--   Let $H$ be a real normed space, $\Phi : H\to\mathbb R$, $\delta\in(0,\tfrac12]$ and $\rho=1-(1-2\delta)^{1/2}$. A function $r:\mathbb R_+\to\mathbb R_+$ satisfies **Assumption 2.10** for $\Phi$ if there are $R>0$ and $\alpha_l\in\mathbb R$ such that $r(s)\le\tfrac{\rho}{2}s$ for all $s\ge R$, and for every $x$ with $\|x\|\ge R$,
--
--   $$\inf_{z\in B_{r(\|x\|)}((1-\rho)x)}\alpha(x,z)>\exp(\alpha_l),\qquad \alpha(x,z)=1\wedge\exp(\Phi(x)-\Phi(z)).$$
--
--   In words: far from the origin, a proposal that lands within distance $r(\|x\|)$ of the proposal mean $(1-\rho)x$ is accepted with probability bounded away from zero, uniformly in $x$. This drives the Lyapunov drift and the contraction far out.
--
--   **Formalization Note** The function $r$ is taken on $\mathbb R$, with $r(s)>0$ for $s>0$ and $r(s)\le\frac\rho2 s$ for $s\ge R$. Positivity on positive inputs is necessary to make the balls in (2.4) nonempty; otherwise $r\equiv0$ makes the acceptance bound vacuous. The paper's domain is $\mathbb R_+$, so its "$|s|\ge R$" means $s\ge R$ (requiring the bound also for $s\le-R$ would contradict $r\ge0$). The infimum bound is stated pointwise for every $z$ in the open ball; with $\alpha_l$ existentially quantified this is equivalent. $B_R(0)^c$ is $\{\|x\|\ge R\}$. The acceptance probability is written with the $1\wedge$ of (1.6); the "$=\inf\exp(\Phi(x)-\Phi(z))$" form printed in (2.4) gives an equivalent condition once $\alpha_l$ is allowed to decrease.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 12, Assumption 2.10, (2.4)

import Mathlib
import Definitions.Def_MHSpectralGap_LocalLip_PCN

namespace MHSpectralGap.LocalLip

/-- Assumption 2.10 (p. 12). `r : ℝ₊ → ℝ₊` is encoded as `r : ℝ → ℝ`, with
`r(s) > 0` for `s > 0`. There are `R > 0` and `α_l ∈ ℝ` with
`r(s) ≤ (ρ/2) s` for `s ≥ R`, such that for every
`x` with `‖x‖ ≥ R` (i.e. `x ∈ B_R(0)^c`) and every `z ∈ B_{r(‖x‖)}((1 − ρ)x)` the pCN acceptance
probability `α(x, z) = 1 ∧ exp(Φ(x) − Φ(z))` exceeds `exp(α_l)`. -/
def Assumption210 {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (Φ : H → ℝ) (δ : ℝ)
    (r : ℝ → ℝ) : Prop :=
  (∀ s, 0 < s → 0 < r s) ∧
    ∃ R > 0, ∃ αl : ℝ, (∀ s, R ≤ s → r s ≤ ρ δ / 2 * s) ∧
      ∀ x : H, R ≤ ‖x‖ → ∀ z ∈ Metric.ball ((1 - ρ δ) • x) (r ‖x‖),
        Real.exp αl < min 1 (Real.exp (Φ x - Φ z))

end MHSpectralGap.LocalLip


