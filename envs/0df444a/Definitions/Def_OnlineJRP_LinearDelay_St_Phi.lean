-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_St_Phi
-- name    : OnlineJRP_LinearDelay_St_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:44.954334+00:00
-- url     : https://prove2.me/theorems/8cf31c77-94bb-491f-8cbe-1ca4403749d8
-- title:
--   UpdateBudgets: the floor $f_i$, the candidate budgets $\alpha^H_r$ and the left-hand side $\Phi(H)$ of Eq. (2)
-- statement:
--   When a new request $r^\star$ arrives at time $t$, it is revealed and live, and for an active item the **floor** is $f_i=(c_i-d_i(t))_+/W_i$, with $W_i$ and $d_i$ including $r^\star$. For $H\ge 0$ and every revealed request $r$,
--   $$
--   \alpha^H_r=\min\{\alpha_r,\;w_r(t-t_r+H_r)\},\qquad H_r=\begin{cases}H & r\text{ already served},\\ \max\{H,f_{i_r}\}&\text{else},\end{cases}
--   $$
--   with $\alpha_{r^\star}=\infty$ before the call. The left-hand side of Eq. (2) is
--   $$
--   \Phi(H)=\sum_{i\in[n]}\Big(\sum_{r:\,i_r=i}\big(\alpha^H_r-w_r(t-t_r)\big)_+-c_i\Big)_+ .
--   $$
--   Algorithm 2 chooses any $H>0$ with $\Phi(H)=1$ and sets $\alpha_r\leftarrow\alpha^H_r$.
--
--   **Formalization Note** The inner sum ranges over the requests revealed so far. A request released at time $t$ but not yet processed has no budget yet.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Algorithm 2 and Eq. (2), p. 6; floor, p. 5; the name Φ, p. 7

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_St_sl

namespace OnlineJRP.LinearDelay

namespace St

open Finset

variable {n : ℕ}

/-- The floor `f_i := (c_i - d_i(t))₊ / W_i` of an active item at the current time (p. 5). It is only
read at active items, where `W_i > 0`. -/
noncomputable def floorF (st : St n) (c : Fin n → ℝ) (i : Fin n) : ℝ :=
  max (c i - st.d i st.now) 0 / st.W i

/-- The state in which the new request `r` has been revealed and the clock moved to `t_r`, with the
budgets not yet updated: Algorithm 2 is "called at time `t` after a new request has been revealed"
(p. 6). The new position has `svc = none` since service only ever touches revealed positions. -/
def reveal (st : St n) (r : Req n) : St n :=
  { st with rev := st.rev ++ [r], now := r.t }

open Classical in
/-- The candidate budget `α^H_r := min{α_r, w_r (t - t_r + H_r)}` of Algorithm 2, line 2 (p. 6), at the
arrival of `r`, where `H_r := H` for a served request and `H_r := max{H, f_{i_r}}` otherwise.

**Formalization Note** The new request has `α_r = ∞` before the call (line 1), encoded by the branch
that omits the minimum. `W`, `d` and `f` include the new request. -/
noncomputable def budgetH (st : St n) (c : Fin n → ℝ) (r : Req n) (H : ℝ)
    (p : Fin (st.reveal r).rev.length) : ℝ :=
  let q := (st.reveal r).req p
  let Hr := if (st.reveal r).svc p = none then max H ((st.reveal r).floorF c q.i) else H
  if (p : ℕ) < st.rev.length then
    min (st.α p) (q.w * (r.t - q.t + Hr))
  else
    q.w * (r.t - q.t + Hr)

/-- `Φ(H)`, the left-hand side of Eq. (2), p. 6 (name from p. 7):
`∑_{i ∈ [n]} (∑_{r : i_r = i, t_r ≤ t} (α^H_r - w_r (t - t_r))₊ - c_i)₊`, with two nested positive parts.

**Formalization Note** The inner sum ranges over all requests revealed so far, including the new one:
Algorithm 2 line 2 says "every revealed request", and a request released at time `t` but not yet
revealed has no budget yet. -/
noncomputable def Phi (st : St n) (c : Fin n → ℝ) (r : Req n) (H : ℝ) : ℝ :=
  ∑ i : Fin n, max
    ((∑ p ∈ univ.filter (fun p : Fin (st.reveal r).rev.length => ((st.reveal r).req p).i = i),
        max (st.budgetH c r H p - ((st.reveal r).req p).w * (r.t - ((st.reveal r).req p).t)) 0)
      - c i) 0

end St

end OnlineJRP.LinearDelay


