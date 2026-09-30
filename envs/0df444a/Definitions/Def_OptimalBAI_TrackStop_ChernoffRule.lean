-- Prove2me | Definitions.Def_OptimalBAI_TrackStop_ChernoffRule
-- name    : OptimalBAI_TrackStop_ChernoffRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:13:48.33536+00:00
-- url     : https://prove2.me/theorems/6918d843-2a3f-4f35-8027-b2eac5165342
-- title:
--   Generalized likelihood ratio statistic and Chernoff's stopping rule (8) for an exponential family
-- statement:
--   Fix a canonical exponential family $(\nu_\theta)_{\theta\in\Theta}$ with densities $\exp(\theta x-b(\theta))$ with respect to $\xi$. After $t$ rounds, let $N_a(t)$ be the number of draws of arm $a$ and $S_a(t)$ the sum of its observed rewards. The log-likelihood of arm $a$'s observations under $\nu_\theta$ is
--   $$\ell_a(t,\theta)=\theta\,S_a(t)-N_a(t)\,b(\theta).$$
--   The **generalized likelihood ratio statistic** for arms $a,b$ is
--   $$Z_{a,b}(t)=\log\frac{\max_{\mu'_a\ge\mu'_b}p_{\mu'_a}(\underline X^a_{N_a(t)})\,p_{\mu'_b}(\underline X^b_{N_b(t)})}{\max_{\mu'_a\le\mu'_b}p_{\mu'_a}(\underline X^a_{N_a(t)})\,p_{\mu'_b}(\underline X^b_{N_b(t)})},$$
--   that is, the supremum of $\ell_a(t,\theta'_a)+\ell_b(t,\theta'_b)$ over $\theta'_a,\theta'_b\in\Theta$ with $\theta'_a\ge\theta'_b$, minus the same supremum over $\theta'_a\le\theta'_b$. Given an exploration rate $\beta(t)$, **Chernoff's stopping rule** is
--   $$\tau=\inf\{t\ge1:\ \exists a\in\mathcal A,\ \forall b\ne a,\ Z_{a,b}(t)>\beta(t)\},$$
--   with $\tau=+\infty$ if no such $t$ exists. The mission uses $\beta(t,\delta)=\log(r(t)/\delta)$.
--
--   This is the stopping half of the Track-and-Stop strategy.
--
--   **Formalization Note** Both suprema are taken in the extended reals: they need not be attained and may be infinite. The condition $Z_{a,b}(t)>\beta(t)$ is written "denominator supremum $+\,\beta(t)<$ numerator supremum", which avoids the undefined difference $\infty-\infty$ (when both suprema are infinite the rule does not stop). The means $\mu'$ of the paper range over $\dot b(\Theta)$; since $\dot b$ is increasing, the constraint $\mu'_a\ge\mu'_b$ is $\theta'_a\ge\theta'_b$. The infimum starts at $t=1$: at $t=0$ there is no observation. On a trajectory, coordinate $s$ is round $s+1$, so the observations at time $t$ are the first $t$ coordinates.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 8, §3.2 (GLR statistic, eq. (8)); pp. 11, 13 (β(t,δ) = log(r(t)/δ))

import Mathlib
import Definitions.Def_TrackAndStop
import Definitions.Def_OptimalBAI_TrackStop_ExpFamily

/-!
Garivier, Kaufmann, *Optimal Best Arm Identification with Fixed Confidence*, arXiv:1602.04589v2,
§3.2, p. 8: the generalized likelihood ratio statistic `Z_{a,b}(t)` of an exponential family and
Chernoff's stopping rule (8), with the threshold `β(t, δ) = log(r(t)/δ)` of Proposition 13 and
Theorem 14 (pp. 11, 13).

Trajectory conventions are those of `Def_BanditTrajectory`: coordinate `s` of
`ω : ℕ → Fin K × ℝ` is round `s + 1`, so the observations available at time `t` are the first `t`
coordinates, and `trajPullCount a t ω` is `N_a(t)`.
-/

open BanditAlgorithm

namespace OptimalBAI.TrackStop

variable {K : ℕ}

/-- `S_a(t)`: the sum of the rewards observed from arm `a` in the first `t` rounds. -/
noncomputable def armRewardSum (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter (fun s => (ω s).1 = a), (ω s).2

/-- The log-likelihood `log p_{ḃ(θ)}(X^a_{N_a(t)}) = θ S_a(t) - N_a(t) b(θ)` of the observations of
arm `a` available at time `t`, under the law `ν_θ` (density `exp(θ x - b(θ))` with respect to `ξ`). -/
noncomputable def logLik (F : ExpFamily) (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) (θ : ℝ) : ℝ :=
  θ * armRewardSum a t ω - (trajPullCount a t ω : ℝ) * F.b θ

/-- The logarithm of the numerator of `Z_{a,b}(t)` (p. 8):
`sup_{μ'_a ≥ μ'_b} log [p_{μ'_a}(X^a) p_{μ'_b}(X^b)]`, i.e. the supremum over `θ'_a, θ'_b ∈ Θ`
with `θ'_a ≥ θ'_b` (the mean map `ḃ` is increasing). It is a supremum in `EReal`: it need not be
attained and may be `+∞`. -/
noncomputable def glrNum (F : ExpFamily) (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : EReal :=
  ⨆ (θa : ℝ) (θb : ℝ) (_ : θa ∈ F.Θ ∧ θb ∈ F.Θ ∧ θb ≤ θa),
    ((logLik F a t ω θa + logLik F b t ω θb : ℝ) : EReal)

/-- The logarithm of the denominator of `Z_{a,b}(t)` (p. 8): the same supremum over
`θ'_a ≤ θ'_b`. -/
noncomputable def glrDen (F : ExpFamily) (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : EReal :=
  ⨆ (θa : ℝ) (θb : ℝ) (_ : θa ∈ F.Θ ∧ θb ∈ F.Θ ∧ θa ≤ θb),
    ((logLik F a t ω θa + logLik F b t ω θb : ℝ) : EReal)

/-- Chernoff's stopping rule (8) (p. 8) with exploration rate `β`:
`τ = inf {t ≥ 1 : ∃ a, ∀ b ≠ a, Z_{a,b}(t) > β(t)}`, where `Z_{a,b}(t) > β(t)` is written
`glrDen + β(t) < glrNum` (no `EReal` subtraction), with value `⊤` if the rule never stops. -/
noncomputable def chernoffTime (F : ExpFamily) (β : ℕ → ℝ) (ω : ℕ → Fin K × ℝ) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, (n : ℕ∞) = t ∧ 1 ≤ n ∧
    ∃ a : Fin K, ∀ b : Fin K, b ≠ a → glrDen F a b n ω + ((β n : ℝ) : EReal) < glrNum F a b n ω}

/-- The exploration rate `β(t, δ) = log(r(t)/δ)` of Proposition 13 and Theorem 14. -/
noncomputable def rateThreshold (r : ℕ → ℝ) (δ : ℝ) (t : ℕ) : ℝ :=
  Real.log (r t / δ)

end OptimalBAI.TrackStop


