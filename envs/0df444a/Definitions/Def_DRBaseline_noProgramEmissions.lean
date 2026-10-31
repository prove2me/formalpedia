-- Prove2me | Definitions.Def_DRBaseline_noProgramEmissions
-- name    : DRBaseline_noProgramEmissions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:52.148813+00:00
-- url     : https://prove2.me/theorems/7a9758bd-f484-448a-a1bd-b1f8efcae19a
-- title:
--   Expected emissions without a program $\bar E$
-- statement:
--   $$\bar E(\rho,\Omega,\Lambda,\Phi,e^h_g,e^l_g)=\rho\,(e^h_g\Omega+e^l_g\Phi)+(1-\rho)\,(e^l_g\Lambda+e^l_g\Phi),$$
--
--   the expected emissions when no demand-response program is offered, with emission intensity $e^h_g$ in an event and $e^l_g$ otherwise and off-peak.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA3

import Mathlib

namespace DRBaseline

/-- **Expected emissions without a program `Ē(ρ, Ω, Λ, Φ, e^h_g, e^l_g)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA3:
"Let Ē(ρ,Ω,Λ,Φ,eh_g,el_g) .= ρ(eh_gΩ + el_gΦ) + (1 − ρ)(el_gΛ + el_gΦ)". -/
def noProgramEmissions (ρ Ω Λ Φ ehg elg : ℝ) : ℝ :=
  ρ * (ehg * Ω + elg * Φ) + (1 - ρ) * (elg * Λ + elg * Φ)

end DRBaseline


