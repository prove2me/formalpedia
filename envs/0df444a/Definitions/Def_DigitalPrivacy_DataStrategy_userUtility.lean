-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_userUtility
-- name    : DigitalPrivacy_DataStrategy_userUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:02:36.419927+00:00
-- url     : https://prove2.me/theorems/9a1db47d-ff1a-4642-a34a-1b1493e9196e
-- title:
--   User utility $U_i(a_i,\bar a)$, display (1)
-- statement:
--   A unit mass of homogeneous users each choose an activity level $a_i\ge 0$; $\bar a$ denotes the average activity, $\xi\in[0,1]$ the fraction of activity the business collects, and $\omega\ge 0$ the adversaries' demand for user information. User $i$'s utility is
--
--   $$U_i(a_i,\bar a)=a_i-\tfrac12 a_i^2+\beta a_i\bar a+(\rho-\omega)a_i\xi ,$$
--
--   with network effect $\beta\in[0,1)$ and value of data to users $\rho\in[0,1)$.
--
--   The first two terms are the standalone benefit and cost of using the service, the third the network effect, and the last the net information externality: tailored services ($\rho$) against harm from adversaries ($\omega$).
--
--   **Formalization Note** The polynomial is defined for all real arguments; the parameter ranges are hypotheses of the theorems.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), §2.1, display (1), p. 7 (PDF 8); parameters p. 6

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **User utility `Uᵢ(aᵢ, ā) = aᵢ − ½aᵢ² + βaᵢā + (ρ − ω)aᵢξ`, display (1).**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), §2.1, display (1), p. 7 (PDF 8): "Uᵢ(aᵢ, ā) = aᵢ − ½aᵢ² + βaᵢā + (ρ − ω)aᵢξ."
Parameters (p. 6): network effect `β ∈ [0, 1)`, value of data to users `ρ ∈ [0, 1)`;
`ξ ∈ [0, 1]` is the business's data collection, `ω ≥ 0` the adversaries' demand for user
information, `a` user `i`'s own activity and `abar` the average activity `ā`.

**Formalization Note.** The function is the printed polynomial for arbitrary real arguments; the
ranges of the parameters are hypotheses of the theorems that use it. -/
noncomputable def userUtility (β ρ ξ ω a abar : ℝ) : ℝ :=
  a - a ^ 2 / 2 + β * a * abar + (ρ - ω) * a * ξ

end DigitalPrivacy.DataStrategy


