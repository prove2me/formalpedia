-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Strategy
-- name    : PermBlockchain_Transfers_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:45:43.255281+00:00
-- url     : https://prove2.me/theorems/bbc952ae-8365-4587-b4bb-153e737b6178
-- title:
--   Manufacturer strategy profile
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A strategy profile assigns to each manufacturer $i$ and each of its possible types $\tau$ an action $(a_i,P_i,\Psi_i)$. Consumers infer manufacturers' types from the observed actions by Bayes' rule, which is why actions are recorded as functions of type.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.2, pp. 12–13 (PDF pp. 13–14); proof of Proposition 4.9, p. 36 (PDF p. 37)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Mfr
import Definitions.Def_PermBlockchain_Transfers_Act

namespace PermBlockchain.Transfers

/-- **A manufacturer strategy profile: each manufacturer's action as a function of its type.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.2, pp. 12–13 (PDF pp. 13–14) and proof of Proposition 4.9, p. 36 (PDF p. 37).

**Formalization Note.** Consumers infer types from actions by Bayes' rule, so a profile records
what each manufacturer `i` does for each of its possible types. -/
abbrev Strategy (m : ℕ) : Type := Mfr m → MType → Act

end PermBlockchain.Transfers


