-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_St_sl
-- name    : OnlineJRP_LinearDelay_St_sl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:54.318943+00:00
-- url     : https://prove2.me/theorems/bd26d501-3108-48cb-b066-7cf917bf0d07
-- title:
--   Forecast quantities at a state: $W_i$, $d_i$, $\tau_r$, $\tau_i$, $\tau_{\min}$, $D$, $\mathrm{ALG}$, $u_i$, the slack $\mathrm{sl}$, $M$ and the ghost usage $G$
-- statement:
--   For a state, with $\rho=1+x$ and joint cost $1$: a request is **live** from its revelation until it is served and an item is **active** if it has a live request. For $v$ at or after the current time,
--   $$
--   W_i=\sum_{r\text{ live},\,i_r=i}w_r,\qquad d_i(v)=\sum_{r\text{ live},\,i_r=i}w_r(v-t_r),\qquad \tau_r=t_r+\frac{\alpha_r}{w_r},
--   $$
--   $\tau_i=\min_{r\text{ live},\,i_r=i}\tau_r$ is the **deadline** of an active item and $\tau_{\min}=\min_{r\text{ live}}\tau_r$ the **checkpoint**. The forecasts are
--   $$
--   D(v)=\sum_{r}\min\{\alpha_r,w_r(v-t_r)\},\qquad u_i(v)=(c_i-x\,d_i(v))_+,
--   $$
--   $$
--   \mathrm{sl}(v)=\rho D(v)-\mathrm{ALG}(v)-\sum_{i\text{ active}}\min\{c_i,x\,d_i(v)\},
--   $$
--   where $\mathrm{ALG}(v)$ is the cost of all purchases so far plus $w_r(s_r-t_r)$ for each served and $w_r(v-t_r)$ for each live request. Finally
--   $$
--   M=\sum_{i:\,u_i(\tau_{\min})=0}W_i,\qquad G(a,b)=\sum_{r\text{ served by time }a}\big(\min\{\alpha_r,w_r(b-t_r)\}-\min\{\alpha_r,w_r(a-t_r)\}\big).
--   $$
--   These are the quantities in which the algorithm and its invariant are stated.
--
--   **Formalization Note** $\tau_i$ and $\tau_{\min}$ are infima of finite sets, read only where the set is nonempty (active items; calls to PlanPurchase, where a request is always live). Every quantity is a function of the state, and no formula depends on the current time except through its argument, so a later state with the same budgets, live sets and purchases has the same forecast. The served requests are read at their internal service time.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Sec. 2, pp. 4–5, 7–8; Eq. (5), p. 8; Sec. 3, p. 10

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_St

namespace OnlineJRP.LinearDelay

namespace St

open Finset

variable {n : ℕ}

/-- The request at a revealed position. -/
def req (st : St n) (p : Fin st.rev.length) : Req n := st.rev.get p

open Classical in
/-- The live revealed positions (p. 4: live from the moment it is revealed until it is served). -/
noncomputable def live (st : St n) : Finset (Fin st.rev.length) :=
  univ.filter fun p => st.svc p = none

/-- The live positions at item `i`. -/
noncomputable def liveAt (st : St n) (i : Fin n) : Finset (Fin st.rev.length) :=
  st.live.filter fun p => (st.req p).i = i

/-- `W_i`, the total weight of the live requests at item `i` (p. 4). -/
noncomputable def W (st : St n) (i : Fin n) : ℝ :=
  ∑ p ∈ st.liveAt i, (st.req p).w

/-- `d_i(v)`, the total delay cost accrued by the live requests at item `i` by time `v` (p. 4),
read at any `v` as the state's forecast (p. 8). -/
noncomputable def d (st : St n) (i : Fin n) (v : ℝ) : ℝ :=
  ∑ p ∈ st.liveAt i, (st.req p).w * (v - (st.req p).t)

/-- The active items: those with a live request (p. 4). -/
noncomputable def active (st : St n) : Finset (Fin n) :=
  univ.filter fun i => (st.liveAt i).Nonempty

/-- The expiration time `τ_r := t_r + α_r / w_r` (p. 5). -/
noncomputable def τ (st : St n) (p : Fin st.rev.length) : ℝ :=
  (st.req p).t + st.α p / (st.req p).w

/-- The deadline `τ_i := min_{r live, i_r = i} τ_r` of an item (p. 7).

**Formalization Note** On an active item this `sInf` of a finite nonempty set is a minimum. On an
inactive item it is the junk value `0`; it is only read at active items. -/
noncomputable def τi (st : St n) (i : Fin n) : ℝ :=
  sInf (st.τ '' (st.liveAt i : Set (Fin st.rev.length)))

/-- The checkpoint `τmin := min_{r live} τ_r` (p. 8).

**Formalization Note** At every call to `PlanPurchase` some request is live, so this `sInf` is a
minimum there. It is only read at such calls. -/
noncomputable def τmin (st : St n) : ℝ :=
  sInf (st.τ '' (st.live : Set (Fin st.rev.length)))

/-- `D(v) := ∑_r min{α_r, w_r (v - t_r)}`, the forecast of the total used budget at `v` (pp. 5, 8),
over all revealed requests, including those already served. -/
noncomputable def D (st : St n) (v : ℝ) : ℝ :=
  ∑ p : Fin st.rev.length, min (st.α p) ((st.req p).w * (v - (st.req p).t))

/-- `ALG(v)`, the forecast of the algorithm's cost (pp. 5, 8): all purchases so far at joint cost `1`,
plus `w_r (s_r - t_r)` for a served request and `w_r (v - t_r)` for a live one. -/
noncomputable def ALG (st : St n) (c : Fin n → ℝ) (v : ℝ) : ℝ :=
  (st.bought.map fun b => 1 + ∑ i ∈ b.2, c i).sum +
    ∑ p : Fin st.rev.length, (st.req p).w * ((st.svc p).getD v - (st.req p).t)

/-- The unpaid fee `u_i(v) := (c_i - x d_i(v))₊`, Eq. (5), p. 8. -/
noncomputable def u (st : St n) (x : ℝ) (c : Fin n → ℝ) (i : Fin n) (v : ℝ) : ℝ :=
  max (c i - x * st.d i v) 0

/-- The slack `sl(v) := ρ D(v) - ALG(v) - ∑_{i active} min{c_i, x d_i(v)}`, Eq. (5), p. 8,
with `ρ = 1 + x`. -/
noncomputable def sl (st : St n) (x : ℝ) (c : Fin n → ℝ) (v : ℝ) : ℝ :=
  (1 + x) * st.D v - st.ALG c v - ∑ i ∈ st.active, min (c i) (x * st.d i v)

open Classical in
/-- `M := ∑_{i : u_i(τmin) = 0} W_i` (p. 10). An inactive item has `W_i = 0`, so the sum is the total
weight of the live requests to active items that are mature at the checkpoint. -/
noncomputable def M (st : St n) (x : ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => st.u x c i st.τmin = 0), st.W i

open Classical in
/-- The ghost usage `G(a, b) := ∑_{r served by time a} (min{α_r, w_r (b - t_r)} - min{α_r, w_r (a - t_r)})`
(p. 10), the first printed form.

**Formalization Note** "Served by time `a`" is read literally. The paper uses `G(a, b)` only when
every request served so far was served no later than `a`, which holds at each use in this mission. -/
noncomputable def G (st : St n) (a b : ℝ) : ℝ :=
  ∑ p ∈ univ.filter (fun p : Fin st.rev.length => ∃ s, st.svc p = some s ∧ s ≤ a),
    (min (st.α p) ((st.req p).w * (b - (st.req p).t)) -
      min (st.α p) ((st.req p).w * (a - (st.req p).t)))

end St

end OnlineJRP.LinearDelay


