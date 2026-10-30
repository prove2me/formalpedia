-- Prove2me | Definitions.Def_PermBlockchain_Transfers_paperStrategy
-- name    : PermBlockchain_Transfers_paperStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:13.240814+00:00
-- url     : https://prove2.me/theorems/249c2f07-a91e-48cf-a411-78c7da8691eb
-- title:
--   The full-adoption profile of the proof of Proposition 4.9
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The profile used in the proof of Proposition 4.9: every manufacturer adopts; a high type sets $P_i=\Psi_i=\gamma$ and a low type sets $P_i=\Psi_i=\max\{\gamma-(h-l),0\}$:
--   $$\{a_i=1,P_i=\Psi_i=\gamma\}_{i\in M_h}\cup\{a_i=1,P_i=\Psi_i=\max\{\gamma-(h-l),0\}\}_{i\in M_l}.$$
--   It is used in the milestones that follow the proof; the goal theorem quantifies over all profiles.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, p. 36 (PDF p. 37)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Strategy

namespace PermBlockchain.Transfers

/-- **The full-adoption profile of the proof of Proposition 4.9.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, p. 36 (PDF p. 37): "{a_i = 1, P_i = Ψ_i = γ}_{i∈M_h} ∪
{a_i = 1, P_i = Ψ_i = max{γ − (h − l), 0}}_{i∈M_l}". Each manufacturer adopts; a high type
sets `P_i = Ψ_i = γ`, a low type `P_i = Ψ_i = max{γ − (h − l), 0}`. -/
noncomputable def paperStrategy {m : ℕ} (γ h l : ℝ) : Strategy m :=
  fun _ τ => match τ.2 with
    | .hi => (true, γ, γ)
    | .lo => (true, max (γ - (h - l)) 0, max (γ - (h - l)) 0)

end PermBlockchain.Transfers


