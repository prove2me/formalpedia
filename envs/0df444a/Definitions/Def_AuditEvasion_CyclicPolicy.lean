-- Prove2me | Definitions.Def_AuditEvasion_CyclicPolicy
-- name    : AuditEvasion_CyclicPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:22.104659+00:00
-- url     : https://prove2.me/theorems/b483047d-55f1-4465-b0be-516c80b4c156
-- title:
--   Theorem 2, (13)–(14), p.1850 — the cyclic policy with ramp length $t_0$
-- statement:
--   For a ramp length $t_0\ge0$ let $q^{n\star}=\theta h/(F-h)$. The **cyclic policy** acts on the phase after each audit $\tau_{i-1}$ (with $\tau_0=0$) as follows:
--
--   1. there are no impulsive audits;
--   2. for $t\in(\tau_{i-1},\tau_{i-1}+t_0]$ there are no audits and the payment is $P_t=he^{-\theta(\tau_{i-1}+t_0-t)}$ (13);
--   3. for $t>\tau_{i-1}+t_0$, until the next audit, intensive audits run at the constant rate $q^{n\star}$ and the payment is $P_t=h$ (14).
--
--   The optimal policy of Theorem 2 is the cyclic policy with $t_0=t^\star$, the positive root of (12).
--
--   **Formalization Note** The same formula is used at $t=0$ for the empty history, a value never charged with positive probability.
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, Theorem 2, (13)–(14), p.1850

import Mathlib
import Definitions.Def_AuditEvasion_Model

namespace AuditEvasion

/-- The audit rate `q^{n⋆} = θh/(F − h)` of (14), Oper. Res. 72(5) (2024), Theorem 2, p.1850. -/
noncomputable def cyclicRate (p : Params) : ℝ :=
  p.theta * p.h / (p.F - p.h)

/-- The cyclic policy with ramp length `t₀` (Theorem 2, (13)–(14), p.1850): on the phase after a
history with last audit `s = τ_{i−1}` (`τ₀ = 0`), no impulsive audits; no intensive audits and the
payment `P_t = h e^{−θ(s + t₀ − t)}` for `t ≤ s + t₀`; intensive audits at the constant rate
`q^{n⋆} = θh/(F − h)` and the payment `P_t = h` for `t > s + t₀`. The optimal policy of
Theorem 2 is `cyclic p t⋆`.

**Formalization Note** (13) gives the payment on `(τ_{i−1}, τ_{i−1} + t⋆]`; the same formula is
used at `t = 0` for the empty history (a value never charged with positive probability). -/
noncomputable def cyclic (p : Params) (t₀ : ℝ) : Policy where
  pay n H t :=
    if t ≤ lastEpoch n H + t₀ then p.h * Real.exp (-p.theta * (lastEpoch n H + t₀ - t)) else p.h
  qm _ _ _ := 0
  qn n H t := if t ≤ lastEpoch n H + t₀ then 0 else cyclicRate p

end AuditEvasion


