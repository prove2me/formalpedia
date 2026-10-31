-- Prove2me | Definitions.Def_DRBaseline_noProgramCost
-- name    : DRBaseline_noProgramCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:52.04636+00:00
-- url     : https://prove2.me/theorems/1012423d-4ab8-427d-9a8f-c0d8231aea0a
-- title:
--   Expected procurement cost without a program $\bar C$
-- statement:
--   $$\bar C(\rho,\Omega,\Lambda,\Phi,c^h_p,c^l_p)=\rho\,(c^h_p\Omega+c^l_p\Phi)+(1-\rho)\,(c^l_p\Lambda+c^l_p\Phi),$$
--
--   the firm's expected procurement cost when it offers no demand-response program: peak demand has mean $\Omega$ in an event (probability $\rho$) and $\Lambda$ otherwise, off-peak demand has mean $\Phi$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA2

import Mathlib

namespace DRBaseline

/-- **Expected procurement cost without a program `C̄(ρ, Ω, Λ, Φ, c^h_p, c^l_p)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA2:
"Let C̄(ρ,Ω,Λ,Φ,ch_p,cl_p) .= ρ(ch_pΩ + cl_pΦ) + (1 − ρ)(cl_pΛ + cl_pΦ)". -/
def noProgramCost (ρ Ω Λ Φ chp clp : ℝ) : ℝ :=
  ρ * (chp * Ω + clp * Φ) + (1 - ρ) * (clp * Λ + clp * Φ)

end DRBaseline


