-- Prove2me | Definitions.Def_RelaxedIndexability_thresholdValue
-- name    : RelaxedIndexability_thresholdValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:08.118537+00:00
-- url     : https://prove2.me/theorems/051210ca-4517-44fe-b850-56e217d4bfe7
-- title:
--   The linear threshold policy $\pi_{\beta,m}$ and its value $\hat V_{\beta,m}$
-- statement:
--   Fix an arm (transition matrix $\mathbf P$, rewards $B$), a discount factor $\beta$, a subsidy $m$ for passivity, and a belief $\omega$ as a point in the threshold. With the linear threshold function $r(x) = xB'$ (31), the **threshold policy** $\pi_{\beta,m}$ (33) takes at belief $x$ the action
--   $$
--   u(x) = \begin{cases} 1 \text{ (active)}, & xB' > \omega B',\\ 0 \text{ (passive)}, & xB' \le \omega B'. \end{cases}
--   $$
--   In particular the arm is passive at the threshold itself.
--
--   The single-armed problem with subsidy $m$ pays $xB'$ (the expected reward of observing the arm at belief $x$) when the arm is active and $m$ when it is passive. Then:
--
--   1. $\hat V_{\beta,m}(x)$ is the expected total discounted reward of $\pi_{\beta,m}$ started at belief $x$;
--   2. $\hat V_{\beta,m}(x; u)$ is the expected total discounted reward when action $u$ is taken at $x$ and $\pi_{\beta,m}$ is followed afterwards.
--
--   At $x = \omega$ the two action values are the two sides of the indifference equation (37):
--   $$
--   \hat V_{\beta,m}(\omega; u=1) = \omega B' + \beta\,\omega\big(\hat V_{\beta,m}(p_0), \dots, \hat V_{\beta,m}(p_{K-1})\big)', \qquad \hat V_{\beta,m}(\omega; u=0) = m + \beta\,\hat V_{\beta,m}(\mathcal T^1(\omega)).
--   $$
--
--   **Formalization Note** The values are the limits of the $n$-horizon expected discounted rewards (`policyValue`, `actionValue`); they are not defined as solutions of the renewal equations (35)–(36).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (31), p.19; (33), p.20; value function, p.20; (37), p.21

import Mathlib
import Definitions.Def_RelaxedIndexability_policyValue

open Matrix

namespace RelaxedIndexability

variable {K : ℕ}

/-- **The linear threshold rule** (Liu, arXiv:2107.11939v4, (31), (33), pp.19–20): with the belief
`ω` fixed as a point in the threshold and `r(x) = x B′`, the arm is made active at belief `x` iff
`r(x) > r(ω)`, and passive iff `r(x) ≤ r(ω)` (ties, in particular `x = ω`, are passive). -/
noncomputable def thresholdRule (B ω : Fin K → ℝ) (x : Fin K → ℝ) : Bool :=
  decide (ω ⬝ᵥ B < x ⬝ᵥ B)

/-- **The value `V̂_{β,m}(x)` of the threshold policy `π_{β,m}`** (Liu, arXiv:2107.11939v4,
p.20): the expected total discounted reward of the single-arm problem with subsidy `m`, under the
threshold rule (33) with threshold `ω`, started at belief `x`. The immediate reward is `x B′` when
active and the subsidy `m` when passive.

**Formalization Note.** It is the limit of the `n`-horizon expected discounted rewards
(`policyValue`); it is *not* defined as a solution of (35)–(36). -/
noncomputable def thresholdValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) (m : ℝ)
    (x : Fin K → ℝ) : ℝ :=
  policyValue β P (fun y => y ⬝ᵥ B) (fun _ => m) (thresholdRule B ω) x

/-- **`V̂_{β,m}(x; u)`**: the value of taking action `u` (`true` = active, `false` = passive) at
belief `x` and following the threshold policy `π_{β,m}` with threshold `ω` afterwards (Liu,
arXiv:2107.11939v4, (35)–(37), pp.20–21). At `x = ω` the two values are the two sides of (37):
`ωB′ + βω(V̂(p₀), …, V̂(p_{K−1}))′` and `m + βV̂(T¹(ω))`. -/
noncomputable def thresholdActionValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ)
    (m : ℝ) (u : Bool) (x : Fin K → ℝ) : ℝ :=
  actionValue β P (fun y => y ⬝ᵥ B) (fun _ => m) (thresholdRule B ω) u x

end RelaxedIndexability


