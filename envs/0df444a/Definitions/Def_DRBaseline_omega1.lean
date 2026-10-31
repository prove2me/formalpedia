-- Prove2me | Definitions.Def_DRBaseline_omega1
-- name    : DRBaseline_omega1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:31.556712+00:00
-- url     : https://prove2.me/theorems/31fa7e8d-573d-44bf-87f5-af0d29af913d
-- title:
--   Upper threshold $\omega_1(b,r)$ of the customer's response
-- statement:
--   With $B_1(r)=r/(2c_s)$,
--
--   $$\omega_1(b,r)=\begin{cases}\min(\omega_B(b,r),2\Omega) & \text{if } B_1(r)\le b \text{ and } r/c_s\le2\Omega,\\ \min(\omega_A(b,r),2\Omega) & \text{otherwise.}\end{cases}$$
--
--   Above $\omega_1$ a customer shifts no demand (Proposition 1). The threshold is capped at $2\Omega$, the top of the demand support.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1

import Mathlib
import Definitions.Def_DRBaseline_omegaA
import Definitions.Def_DRBaseline_omegaB

namespace DRBaseline

/-- **Upper threshold `ω₁(b, r)` of the customer's best response.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1: "let ω1(b,r) .=
min(ωB(·),2Ω) if B1(·) ≤ b and r/cs ≤ 2Ω, and ω1(·) .= min(ωA(·),2Ω) otherwise", with
`B₁(r) = r/(2c_s)`.

Above `ω₁` the customer shifts nothing. -/
noncomputable def omega1 (Ω cs b r : ℝ) : ℝ :=
  if r / (2 * cs) ≤ b ∧ r / cs ≤ 2 * Ω then min (omegaB cs b r) (2 * Ω)
  else min (omegaA cs b r) (2 * Ω)

end DRBaseline


