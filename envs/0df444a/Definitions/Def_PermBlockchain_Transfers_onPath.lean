-- Prove2me | Definitions.Def_PermBlockchain_Transfers_onPath
-- name    : PermBlockchain_Transfers_onPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:47:29.345996+00:00
-- url     : https://prove2.me/theorems/d13623ca-1602-4b5f-9141-c216618b4b1a
-- title:
--   The action profile prescribed under a type assignment
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   For a strategy profile and a type assignment $\theta\in\Theta$, the prescribed action profile gives manufacturer $i$ the action its strategy prescribes for its type $\theta(i)$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, p. 36 (PDF p. 37)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Strategy

namespace PermBlockchain.Transfers

/-- **The action profile a strategy prescribes under the type assignment `θ`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, p. 36 (PDF p. 37). -/
def onPath {m : ℕ} (act : Strategy m) (θ : Mfr m → MType) : Mfr m → Act :=
  fun i => act i (θ i)

end PermBlockchain.Transfers


