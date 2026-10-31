-- Prove2me | Definitions.Def_DRBaseline_customerObj
-- name    : DRBaseline_customerObj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:32.541066+00:00
-- url     : https://prove2.me/theorems/312fda57-4069-4ee8-adbf-1055971cce28
-- title:
--   Customer's net benefit $C_c(s)=rS(s)-\frac{c_s}{2}s^2$
-- statement:
--   During a demand-response event a customer with peak demand $\omega$, facing baseline $b$ and rebate $r$ per unit of estimated reduction, chooses how much demand $s$ to shift to the off-peak period. Shifting costs $C_s(s)=\frac{c_s}{2}s^2$ (inconvenience), so the customer's **net benefit** is
--
--   $$C_c(s)=r\,S(s)-\frac{c_s}{2}s^2=r\bigl(b-(\omega-s)\bigr)^+-\frac{c_s}{2}s^2 .$$
--
--   Because of the kink of $(\cdot)^+$ this function is not concave in $s$; it is the maximum of two parabolas.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.3, p.9

import Mathlib
import Definitions.Def_DRBaseline_estReduction

namespace DRBaseline

/-- **Customer's net benefit `C_c(s) = r S(s) − (c_s/2) s²`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.3, p.9: "max_{s≤ω} C_c(s) .= rS(s) − C_s(s)", with `C_s(s) = (c_s/2) s²`.

`customerObj cs b r ω s` is the rebate `r · (b − (ω − s))⁺` net of the inconvenience cost
`(c_s/2) s²`, for baseline `b`, rebate `r`, demand realization `ω` and shift `s`. -/
noncomputable def customerObj (cs b r ω s : ℝ) : ℝ :=
  r * estReduction b ω s - cs / 2 * s ^ 2

end DRBaseline


