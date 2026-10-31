-- Prove2me | Definitions.Def_DRBaseline_IsBestResponse
-- name    : DRBaseline_IsBestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:42:25.280001+00:00
-- url     : https://prove2.me/theorems/0a566817-0e5a-43ae-8427-317abbed9c1d
-- title:
--   Best-response selection $s^*(b,r\mid\omega)$
-- statement:
--   A function $s(b,r,\omega)$ is a **best-response selection** if for every baseline $b\ge0$, every rebate $r\ge0$ and every demand realization $\omega\in[0,2\Omega]$ (the support of the event-period demand, uniform with mean $\Omega$), the value $s(b,r,\omega)$ solves the customer's problem $\max_{s\le\omega}C_c(s)$.
--
--   Every result of the mission is stated for an arbitrary best-response selection.
--
--   **Formalization Note** The arg max can contain two points for at most two values of $\omega$ per $(b,r)$, so a selection is needed; any two selections differ on a null set, and no measurability is imposed. The firm's domain is the quadrant $b\ge0$, $r\ge0$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.1, p.7 and §3.3, p.9

import Mathlib
import Definitions.Def_DRBaseline_IsCustomerOptimal

namespace DRBaseline

/-- **A best-response selection `s*(b, r | ω)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.1, p.7 (demand `ω` uniform on `[0, 2Ω]`) and §3.3, p.9
("let s∗(b,r|ω) .= arg max_{s≤ω} C_c(s)").

`IsBestResponse Ω cs s` says that for every baseline `b ≥ 0`, every rebate `r ≥ 0` and every
demand realization `ω ∈ [0, 2Ω]`, the value `s b r ω` solves the customer's problem.

**Formalization Note** The arg max is not a singleton at up to two values of `ω` per `(b, r)`,
so statements quantify over an arbitrary selection `s` with this property instead of a fixed
formula. The firm's domain is `b ≥ 0`, `r ≥ 0`. No measurability is imposed: any selection
agrees with the paper's piecewise formula except at finitely many `ω`, so every integral of
it over `[0, 2Ω]` is the paper's. -/
def IsBestResponse (Ω cs : ℝ) (s : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ b r ω : ℝ, 0 ≤ b → 0 ≤ r → 0 ≤ ω → ω ≤ 2 * Ω → IsCustomerOptimal cs b r ω (s b r ω)

end DRBaseline


