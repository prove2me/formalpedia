-- Prove2me | Definitions.Def_RobustBooking_BidPrice_Controls
-- name    : RobustBooking_BidPrice_Controls
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T00:52:03.977986+00:00
-- url     : https://prove2.me/theorems/fe9cb5fa-34f1-42ec-b713-05afff51c74e
-- title:
--   Protection levels θ(f) of Eq. (15), controls Q and P, value accumulation V, policies A_θ and A′_θ, and the m-fare grid (13)
-- statement:
--   **Bid-price controls.** Fix $0 < f_{\min} < f_{\max}$, $r = f_{\min}/f_{\max}$ and capacity $n > 0$. The **protection levels** of Eq. (15) are, for $f_{\min} \le f \le f_{\max}$,
--   $$\theta(f) = \frac{\ln f_{\max} - \ln f}{\ln f_{\max} - \ln f_{\min}}\Big(1 - \frac{1}{1 - \ln r}\Big)n,$$
--   and the **protection-level control function** is $Q(f) = n - \theta(f)$. For a protection-level control function $Q$, the **order quantity control function** is
--   $$P(q) = \min\{f \in [f_{\min}, f_{\max}] : Q(f) \ge q\}, \qquad 0 \le q \le n,$$
--   and the **value accumulation function** of the $P$ of Eq. (15) is $V(q) = \int_0^q P(s)\,ds$.
--
--   With $\hat q$ the quantity already accepted and $\hat q(f)$ the quantity accepted at fares $\le f$, a request with fare $O$ and quantity $d$ is handled as follows.
--   - **Protection-level control policy $A_\theta$** based on $Q$: accept $x = \sup\{\alpha : \alpha + \hat q(f) \le Q(f) \text{ for all } f \in [O, f_{\max}];\ 0 \le \alpha \le d\}$.
--   - **Order quantity control policy $A'_\theta$** based on $P$: if $O < P(\hat q)$ accept $0$; otherwise accept $x = \sup\{\alpha : P(\alpha + \hat q) \le O;\ 0 \le \alpha \le d;\ \alpha + \hat q \le n\}$.
--
--   Finally, for $m \ge 2$ the **$m$-fare grid** of Eq. (13) is the set of fares $f_i^{(m)} = f_{\max}\, r^{(i-1)/(m-1)}$, $i = 1, \dots, m$.
--
--   **Formalization Note.** $P$ is defined from $Q$ as a real `sInf` of $\{f \in [f_{\min}, f_{\max}] : q \le Q(f)\}$, which is bounded below by $f_{\min}$ and, for the $Q$ of Eq. (15), nonempty for $q \le n = Q(f_{\max})$; the closed form of $P$ is *not* built in (that is Lemma 2). The sup in $A_\theta$ ranges over the whole continuum $f \in [O, f_{\max}]$. The paper's unit orders ($0 \le \alpha \le 1$) become $0 \le \alpha \le d$ for sized requests, and $\alpha + \hat q \le n$ keeps the argument of $P$ in its domain $[0, n]$. The sups are real `sSup`s of sets bounded by $d$. $V$ is an interval integral; $P$ is monotone, hence integrable on $[0, q]$.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 956 (Q, P, A_θ, A′_θ), p. 959 (Eq. (13), Eq. (15), V(q))

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy

namespace RobustBooking.BidPrice

/-- The protection levels of the continuous bid-price policy, Eq. (15) (p. 959): for
`f_min ≤ f ≤ f_max`,
`θ(f) = (ln f_max - ln f) / (ln f_max - ln f_min) · (1 - 1 / (1 - ln r)) · n`, `r = f_min / f_max`. -/
noncomputable def theta (fmin fmax n f : ℝ) : ℝ :=
  (Real.log fmax - Real.log f) / (Real.log fmax - Real.log fmin) *
    (1 - 1 / (1 - Real.log (discountRatio fmin fmax))) * n

/-- The protection-level control function of Eq. (15), `Q(f) = n - θ(f)` (p. 956). -/
noncomputable def protectionControl (fmin fmax n f : ℝ) : ℝ :=
  n - theta fmin fmax n f

/-- The order quantity control function associated with a protection-level control function `Q`
(p. 956): `P(q) = min {f ∈ [f_min, f_max] : Q(f) ≥ q}`, for `0 ≤ q ≤ n`. It is written as the real
`sInf` of that set; the set is bounded below by `f_min`, and it is nonempty for `q ≤ Q(f_max)`
(for the `Q` of Eq. (15), `Q(f_max) = n`). -/
noncomputable def orderQuantityControl (fmin fmax : ℝ) (Q : ℝ → ℝ) (q : ℝ) : ℝ :=
  sInf {f : ℝ | f ∈ Set.Icc fmin fmax ∧ q ≤ Q f}

/-- The order quantity control function `P(q)` associated with the protection levels of
Eq. (15). -/
noncomputable def bidPriceP (fmin fmax n : ℝ) : ℝ → ℝ :=
  orderQuantityControl fmin fmax (protectionControl fmin fmax n)

/-- The value accumulation function (p. 959), `V(q) = ∫₀^q P(s) ds`, for the `P` of Eq. (15). -/
noncomputable def valueAccumulation (fmin fmax n q : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..q, bidPriceP fmin fmax n s

/-- The protection-level control policy `A_θ` based on `Q` (p. 956): with `q̂(f)` the quantity
already accepted at fares `≤ f`, request `k + 1` with fare `O` and quantity `d` is accepted to the
extent `x = sup {α : α + q̂(f) ≤ Q(f) for all f ∈ [O, f_max]; 0 ≤ α ≤ d}` (the paper's
`0 ≤ α ≤ 1` for unit orders). The constraint is checked over the whole continuum `[O, f_max]`. -/
noncomputable def protectionLevelPolicy (fmax : ℝ) (Q : ℝ → ℝ) : DetPolicy where
  decide hist q :=
    sSup {α : ℝ | 0 ≤ α ∧ α ≤ q.qty ∧
      ∀ f ∈ Set.Icc q.fare fmax, α + acceptedAtOrBelow f hist ≤ Q f}

/-- The order quantity control policy `A′_θ` based on `P` (p. 956), for capacity `n`: with `q̂` the
total quantity already accepted, request `k + 1` with fare `O` and quantity `d` is rejected if
`O < P(q̂)`; otherwise it is accepted to the extent
`x = sup {α : P(α + q̂) ≤ O; 0 ≤ α ≤ d; α + q̂ ≤ n}` (the paper's `0 ≤ α ≤ 1` for unit orders;
`α + q̂ ≤ n` keeps the argument of `P` in its domain `[0, n]`). Here `P` is the order quantity
control function of `Q`. -/
noncomputable def orderQuantityPolicy (fmin fmax n : ℝ) (Q : ℝ → ℝ) : DetPolicy where
  decide hist q :=
    if q.fare < orderQuantityControl fmin fmax Q (acceptedTotal hist) then 0
    else sSup {α : ℝ | 0 ≤ α ∧ α ≤ q.qty ∧ α + acceptedTotal hist ≤ n ∧
      orderQuantityControl fmin fmax Q (α + acceptedTotal hist) ≤ q.fare}

/-- The fares of the `m`-fare approximation, Eq. (13) (p. 959):
`f_i^(m) = f_max · r^((i - 1)/(m - 1))` for `i = 1, …, m`, `r = f_min / f_max` (used for `m ≥ 2`). -/
noncomputable def gridFares (fmin fmax : ℝ) (m : ℕ) : Set ℝ :=
  {f : ℝ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ m ∧
    f = fmax * discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1))}

end RobustBooking.BidPrice


