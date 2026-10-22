-- Prove2me | Definitions.Def_RobustBooking_MultiFare_NestedPolicies
-- name    : RobustBooking_MultiFare_NestedPolicies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T23:43:34.369046+00:00
-- url     : https://prove2.me/theorems/f1873e5f-ee5e-4a41-961f-534560462ba6
-- title:
--   The protection-level control policy A_θ and the order quantity control policy A′_θ
-- statement:
--   Fix fares $f_1 > \dots > f_m > 0$, capacity $n$, and the controls $Q_i$ and $P$ of Eqs. (7)–(9). When request $k+1$ arrives, of class $c$ with quantity $d$, write $\hat q = \sum_{l \le k} x_l$ for the total accepted so far and $\hat q(f_j) = \sum_{l \le k,\ \mathrm{cls}(r_l) \ge j} x_l$ for the total accepted so far at fares $\le f_j$ (p. 956).
--
--   **Protection-level control $A_\theta$** accepts
--   $$x_{k+1} = \sup\bigl\{\alpha : \alpha + \hat q(f_j) \le Q_j \text{ for every class } j \le c;\ 0 \le \alpha \le d\bigr\},$$
--   i.e. the constraint $\alpha + \hat q(f) \le Q(f)$ for every fare $f = f_j \ge f_c$.
--
--   **Order quantity control $A'_\theta$**: if $f_c < P(\hat q)$ it accepts $x_{k+1} = 0$; otherwise
--   $$x_{k+1} = \sup\bigl\{\alpha : P(\alpha + \hat q) \le f_c;\ \alpha + \hat q \le n;\ 0 \le \alpha \le d\bigr\}.$$
--
--   **Formalization Note.** The paper states both policies for unit orders with $0 \le \alpha \le 1$; with sized requests the bound is $0 \le \alpha \le d$ (for $d = 1$ this is the paper's rule). The constraint $\alpha + \hat q \le n$ in $A'_\theta$ is implicit in the paper because $P$ is defined only on $[0, n]$. The suprema are real `sSup`s of sets bounded above by $d$; if a set were empty its `sSup` would be $0$, which is also the natural reading (accept nothing). Each policy is a deterministic online policy of the booking model; the run clips its proposal to the remaining capacity, which neither policy ever exceeds.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 956 (definitions of q̂, q̂(f), A_θ and A′_θ), p. 957 (Q and P for m fare classes)

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_BookingModel
import Definitions.Def_RobustBooking_MultiFare_ProtectionLevels

namespace RobustBooking.MultiFare

/-- `q̂(f_j)`: the total quantity accepted so far from requests whose fare is `≤ f_j`,
i.e. from the classes `j, j+1, …, m`. -/
def acceptedAtOrBelow (past : List (Request × ℝ)) (j : ℕ) : ℝ :=
  ((past.filter fun p => j ≤ p.1.cls).map Prod.snd).sum

/-- `A_θ`, the protection-level control policy (p. 956) with the controls `Q` of
Eqs. (7)–(9): a request of class `c` asking for `d` gets
`sup {α : α + q̂(f_j) ≤ Q_j for every class j ≤ c (every fare f_j ≥ f_c); 0 ≤ α ≤ d}`. -/
noncomputable def protectionPolicy (m : ℕ) (f : ℕ → ℝ) (n : ℝ) : DetPolicy :=
  fun past r =>
    sSup {α : ℝ | 0 ≤ α ∧ α ≤ r.qty ∧
      ∀ j ∈ Finset.Icc 1 r.cls, α + acceptedAtOrBelow past j ≤ Q m f n j}

/-- `A′_θ`, the order quantity control policy (p. 956) with the function `P` of p. 957:
with `q̂` the total quantity accepted so far, a request of class `c` asking for `d` gets
`0` if `f_c < P(q̂)`, and otherwise `sup {α : P(α + q̂) ≤ f_c; 0 ≤ α ≤ d}`, where
`α + q̂ ≤ n` is required because `P` is defined only on `[0, n]`. -/
noncomputable def orderQuantityPolicy (m : ℕ) (f : ℕ → ℝ) (n : ℝ) : DetPolicy :=
  fun past r =>
    let qhat := (past.map Prod.snd).sum
    if f r.cls < orderPrice m f n qhat then 0
    else sSup {α : ℝ | 0 ≤ α ∧ α ≤ r.qty ∧ α + qhat ≤ n ∧
      orderPrice m f n (α + qhat) ≤ f r.cls}

end RobustBooking.MultiFare


