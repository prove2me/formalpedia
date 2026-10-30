-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_profit
-- name    : DigitalPrivacy_DataStrategy_profit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:07.319348+00:00
-- url     : https://prove2.me/theorems/41b7ff48-0216-46b9-8a92-22b654534fc9
-- title:
--   Business profit $\Pi(\xi,C)$ at the subgame outcome, display (2)
-- statement:
--   The business's profit from data strategy $(\xi,C)$ is
--
--   $$\Pi(\xi,C)=(1-P)\,\bar a^*(\xi,C)+P\,\xi\,\bar a^*(\xi,C)-\psi C ,$$
--
--   where $P\in[0,1]$ is the revenue model ($P=0$ purely usage-driven, $P=1$ purely data-driven), $\psi$ the unit cost of protection and $\bar a^*$ the subgame equilibrium activity (3).
--
--   This is the objective the business maximizes in Theorem 1.
--
--   **Formalization Note** The average activity in (2) is replaced by the equilibrium value $\bar a^*(\xi,C)$, as the business anticipates the subgame (§2.4).
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), §2.3, display (2), p. 8 (PDF 9)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_abarStar

namespace DigitalPrivacy.DataStrategy

/-- **The business's profit `Π(ξ, C) = (1 − P)·ā + P·ξā − ψC` at the subgame outcome, display (2).**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), §2.3, display (2), p. 8 (PDF 9): "Π(ξ, C) = (1 − P) · ā + P · ξā − ψC where P ∈ [0, 1]",
with protection cost `ψC` "for some ψ ≥ 0" (p. 8).

**Formalization Note.** The average activity `ā` is the subgame equilibrium `ā*(ξ, C)` of
display (3) (`abarStar`, justified by Proposition 1): the business commits to `(ξ, C)` first and
users and adversaries respond (§2.4, p. 9). -/
noncomputable def profit (β ρ P ψ ξ C : ℝ) : ℝ :=
  (1 - P) * abarStar β ρ ξ C + P * (ξ * abarStar β ρ ξ C) - ψ * C

end DigitalPrivacy.DataStrategy


