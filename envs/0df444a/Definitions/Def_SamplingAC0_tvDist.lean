-- Prove2me | Definitions.Def_SamplingAC0_tvDist
-- name    : SamplingAC0_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:42.630605+00:00
-- url     : https://prove2.me/theorems/a57fdade-492f-4f94-847d-16f8d2fb1950
-- title:
--   Statistical distance $\Delta(P,Q)$
-- statement:
--   For distributions $P,Q$ on a finite set $B$, the **statistical distance** is
--
--   $$\Delta(P,Q)=\frac12\sum_{x\in B}\lvert P(x)-Q(x)\rvert .$$
--
--   It lies in $[0,1]$, and every lower bound of the mission is a lower bound on it.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Notation, p.2

import Mathlib
set_option autoImplicit false

namespace SamplingAC0

/-- **Statistical distance.** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027
submission (manuscript sha256 99c33d30…), Notation, p.2: "We write ∆(P, Q) for the statistical
distance 0.5 ∑_x |P(x) − Q(x)| between distributions P and Q".

**Formalization Note.** Distributions on a finite type; the masses are converted to real numbers
with `toReal` before subtracting. -/
noncomputable def tvDist {β : Type} [Fintype β] (P Q : PMF β) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |(P x).toReal - (Q x).toReal|

end SamplingAC0


