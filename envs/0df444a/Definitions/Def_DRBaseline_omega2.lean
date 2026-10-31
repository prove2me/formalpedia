-- Prove2me | Definitions.Def_DRBaseline_omega2
-- name    : DRBaseline_omega2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:32.943046+00:00
-- url     : https://prove2.me/theorems/a36225fe-be87-41c2-9f12-b2288501b134
-- title:
--   Lower threshold $\omega_2(b,r)$ of the customer's response
-- statement:
--   $$\omega_2(b,r)=\begin{cases}\min(\omega_A(b,r),r/c_s) & \text{if } r/c_s\le2\Omega,\\ \min(\omega_A(b,r),2\Omega) & \text{otherwise.}\end{cases}$$
--
--   Up to $\omega_2$ a customer shifts all of its demand (Proposition 1).
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1

import Mathlib
import Definitions.Def_DRBaseline_omegaA

namespace DRBaseline

/-- **Lower threshold `ω₂(b, r)` of the customer's best response.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1: "let ω2(b,r) .=
min(ωA(·), r/cs) if r/cs ≤ 2Ω and ω2(·) .= min(ωA(·),2Ω) otherwise".

Up to `ω₂` the customer shifts all of its demand. -/
noncomputable def omega2 (Ω cs b r : ℝ) : ℝ :=
  if r / cs ≤ 2 * Ω then min (omegaA cs b r) (r / cs) else min (omegaA cs b r) (2 * Ω)

end DRBaseline


