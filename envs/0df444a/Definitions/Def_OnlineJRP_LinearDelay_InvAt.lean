-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_InvAt
-- name    : OnlineJRP_LinearDelay_InvAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:59.200603+00:00
-- url     : https://prove2.me/theorems/da95c349-0f16-4b7c-b265-04c6180b43b0
-- title:
--   The invariant (6), the virtual slack $\widetilde{\mathrm{sl}}$, the bound (14), and consecutive calls
-- statement:
--   The **invariant** at a state with reference time $h$ is Eq. (6),
--   $$
--   \mathrm{sl}(\tau_{\min})\ge x+\frac1{x^2}\cdot\frac{G(h,\tau_{\min})}{G(h,\tau_{\min})+M(\tau_{\min}-h)}.
--   $$
--   For a purchase of $S^-$ planned at a previous call (superscript minus), the **virtual slack** is $\widetilde{\mathrm{sl}}=\mathrm{sl}^-(\tau^-_{\min})-1-\sum_{i\in S^-}u^-_i(\tau^-_{\min})$, and at purchase time $t$ the bound (14) is
--   $$
--   \mathrm{sl}^-(\tau^-_{\min})\ge x+\frac1{x^2}\cdot\frac{G^-(t,\tau^-_{\min})}{G^-(t,\tau^-_{\min})+(\tau^-_{\min}-t)\sum_{i\in S^-}W^-_i}.
--   $$
--   Two relations link consecutive calls: a call follows a purchase planned at the previous call, leaving a request live; or a call follows an arrival that interrupts the plan of the previous call.
--
--   **Formalization Note** Each relation names the intermediate ready state existentially; given the previous call and the plan, it is determined.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Eq. (6), p. 10; s̃l, p. 12; Eq. (14), p. 15; Sec. 3.1, p. 10; Sec. 5, p. 17

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_IsRun

namespace OnlineJRP.LinearDelay

open Finset

variable {n : ℕ}

/-- The invariant Eq. (6), p. 10, at a state with reference time `h`:
`sl(τmin) ≥ x + (1/x²) · G(h, τmin) / (G(h, τmin) + M (τmin - h))`. -/
noncomputable def InvAt (x : ℝ) (c : Fin n → ℝ) (st : St n) (h : ℝ) : Prop :=
  x + (1 / x ^ 2) * (st.G h st.τmin / (st.G h st.τmin + st.M x c * (st.τmin - h))) ≤ st.sl x c st.τmin

/-- The virtual slack `s̃l := sl⁻(τ⁻min) - 1 - ∑_{i ∈ S⁻} u⁻_i(τ⁻min)` of a purchase of `S⁻` planned at
the call `st⁻` (p. 12). -/
noncomputable def slTilde (x : ℝ) (c : Fin n → ℝ) (st' : St n) (S : Finset (Fin n)) : ℝ :=
  st'.sl x c st'.τmin - 1 - ∑ i ∈ S, st'.u x c i st'.τmin

/-- The bound Eq. (14), p. 15, for a purchase of `S⁻` at time `t` planned at the call `st⁻`:
`sl⁻(τ⁻min) ≥ x + (1/x²) · G⁻(t, τ⁻min) / (G⁻(t, τ⁻min) + (τ⁻min - t) ∑_{i ∈ S⁻} W⁻_i)`. -/
noncomputable def Bound14 (x : ℝ) (c : Fin n → ℝ) (st' : St n) (S : Finset (Fin n)) (t : ℝ) : Prop :=
  x + (1 / x ^ 2) * (st'.G t st'.τmin / (st'.G t st'.τmin + (st'.τmin - t) * ∑ i ∈ S, st'.W i)) ≤
    st'.sl x c st'.τmin

/-- `st` is a call to `PlanPurchase` triggered by the purchase of `(S, s)` that the call `st'` planned,
with no arrival in between, so that a request stays live (Sec. 3.1, p. 10; Sec. 4, p. 12). -/
def AfterPurchase (x : ℝ) (c : Fin n → ℝ) (σ : List (Req n)) (st' : St n) (S : Finset (Fin n)) (s : ℝ)
    (st : St n) : Prop :=
  ∃ st₁, PlanStep x c st' S s st₁ ∧ BuyStep x c σ st₁ S s st ∧ st.phase = .call

/-- `st` is a call to `PlanPurchase` triggered by an arrival with value `H` that interrupted the plan
made at the call `st'` (Sec. 5, p. 17). For a call following an arrival when no request was live,
there is no such `st'`. -/
def AfterArrival (x : ℝ) (c : Fin n → ℝ) (σ : List (Req n)) (st' : St n) (H : ℝ) (st : St n) : Prop :=
  ∃ st₁ S s, PlanStep x c st' S s st₁ ∧ ArrivalStep c σ st₁ H st

end OnlineJRP.LinearDelay


