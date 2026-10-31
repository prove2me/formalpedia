-- Prove2me | Definitions.Def_DRBaseline_netSavings
-- name    : DRBaseline_netSavings
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:32.679995+00:00
-- url     : https://prove2.me/theorems/3bbc1690-0685-4787-b000-94f95a9d94bd
-- title:
--   Firm's expected net cost savings $C(b,r)$
-- statement:
--   With $\Delta c=c^h_p-c^l_p>0$ the difference between the firm's marginal procurement cost in an event and off-event, the **expected net cost savings** from a demand-response program with baseline $b$ and rebate $r$ are
--
--   $$C(b,r)=\rho\,\mathbb E_\omega\Bigl[\Delta c\,s^*(b,r\mid\omega)-r\,S\bigl(s^*(b,r\mid\omega)\bigr)\Bigr],$$
--
--   with $\omega$ uniform on $[0,2\Omega]$: procurement savings on the actual reduction minus the rebate paid on the estimated reduction.
--
--   **Formalization Note** $\Delta c$ is an argument so that savings at two cost differences can be compared; the customer's response does not depend on $\Delta c$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.4, p.10

import Mathlib
import Definitions.Def_DRBaseline_estReduction

namespace DRBaseline

/-- **Firm's expected net cost savings `C(b, r) = ρ E_ω[Δc s*(b,r|ω) − r S(s*(b,r|ω))]`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.4, p.10: "C(b,r) .= ρE_ω[(c^h_p − c^l_p)s∗(b,r|ω) − rS(s∗(b,r|ω))]", with
`Δc = c^h_p − c^l_p` (p.7) and `ω` uniform on `[0, 2Ω]`.

`Δc` is an argument, so that savings at two different cost differences can be compared; the
selection `s` does not depend on `Δc`, since the customer's problem does not.

**Formalization Note** Interval integral with the density `1/(2Ω)` written out; `S` is
`estReduction`. -/
noncomputable def netSavings (Ω ρ Δc : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (b r : ℝ) : ℝ :=
  ρ * ∫ ω in (0 : ℝ)..2 * Ω, (Δc * s b r ω - r * estReduction b ω (s b r ω)) / (2 * Ω)

end DRBaseline


