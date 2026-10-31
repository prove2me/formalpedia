-- Prove2me | Definitions.Def_DRBaseline_estReduction
-- name    : DRBaseline_estReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:50.14917+00:00
-- url     : https://prove2.me/theorems/ad431028-b31e-4f61-a961-e02d1138a0a0
-- title:
--   Estimated demand reduction $S(s)=(b-(\omega-s))^+$
-- statement:
--   A utility firm cannot observe a customer's demand $\omega$, only its consumption $q$. Given a **baseline** $b$, it estimates the customer's demand reduction as $(b-q)^+$. When the customer shifts $s$ units of demand out of the peak period, its consumption is $q=\omega-s$, so the **estimated demand reduction** is
--
--   $$S(s)=\bigl(b-(\omega-s)\bigr)^+ .$$
--
--   The rebate paid to the customer is $rS(s)$. A customer whose consumption exceeds the baseline is neither paid nor penalized.
--
--   **Formalization Note** $(x)^+$ is written `max x 0`.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.2, p.8 and §3.3, p.9

import Mathlib

namespace DRBaseline

/-- **Estimated demand reduction `S(s) = (b − (ω − s))⁺`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.2, p.8 ("the estimated demand reduction is given by S = (b − q)⁺") and §3.3, p.9
("rS(s) = r(b − q)⁺ = r(b − (ω − s))⁺").

For a baseline `b`, a demand realization `ω` and a shifted amount `s`, the customer's peak
consumption is `q = ω − s` and the firm's estimate of the reduction is `(b − (ω − s))⁺`.

**Formalization Note** `(x)⁺` is written `max x 0`. -/
def estReduction (b ω s : ℝ) : ℝ :=
  max (b - (ω - s)) 0

end DRBaseline


