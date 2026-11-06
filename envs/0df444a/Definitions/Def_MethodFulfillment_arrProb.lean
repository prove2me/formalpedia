-- Prove2me | Definitions.Def_MethodFulfillment_arrProb
-- name    : MethodFulfillment_arrProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:07.543352+00:00
-- url     : https://prove2.me/theorems/45cc03ec-6e03-4e3b-92c8-8d8c55ee9e81
-- title:
--   Arrival law of one period
-- statement:
--   In each period $t$ at most one order arrives: an order of type $q$ with probability $p_t(q)$, and no order with probability $1-\sum_{q}p_t(q)$. Arrivals are independent across periods, so an arrival sequence $\omega=(\omega_1,\dots,\omega_T)$, where $\omega_t$ is either an order type or "no arrival", has probability
--   $$\prod_{t\in[T]}\Pr(\omega_t).$$
--   This is the law of the arrival process $D$ of the paper; $D_{qt}$ is the indicator that $\omega_t=q$.
--
--   **Formalization Note** "No arrival" is the value `none` of `Option Q`.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), §2, pp.7–8

import Mathlib
import Definitions.Def_MethodFulfillment_Instance

namespace MethodFulfillment

/-- The arrival law of one period (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, §2,
pp.7–8): at Lean time `t` an order of type `q` arrives with probability `p t q` (`some q`), and no
order arrives with the remaining probability `1 - ∑_q p t q` (`none`). Arrivals in different
periods are independent, so the law of a whole arrival sequence `ω : Fin T → Option Q` is
`∏_t arrProb P t (ω t)`.

**Formalization Note.** `none` encodes "no order arrives", which the paper allows ("at most one
order arrives", p.7); the paper's `D_{qt}` is the indicator of `ω t = some q`. -/
def arrProb {I K Q : Type} [Fintype Q] {T : ℕ} (P : Instance I K Q T) (t : Fin T) :
    Option Q → ℝ
  | none => 1 - ∑ q, P.p t q
  | some q => P.p t q

end MethodFulfillment


