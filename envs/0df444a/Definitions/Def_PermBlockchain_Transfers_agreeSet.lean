-- Prove2me | Definitions.Def_PermBlockchain_Transfers_agreeSet
-- name    : PermBlockchain_Transfers_agreeSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:49:45.429986+00:00
-- url     : https://prove2.me/theorems/2d62ab62-d819-4ad8-838a-03ab291b7a4a
-- title:
--   Type assignments agreeing with a revelation
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   For a revelation $r$, the agreement set is the set of $\theta\in\Theta$ with $\theta(j)=r_j$ for every manufacturer $j$ whose type is revealed. Since $\Theta$ fixes the number of manufacturers of each type, revealing all types but one determines the remaining one, as used on p. 38: "she is the only manufacturer that is not on the blockchain".
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.2, p. 12 (PDF p. 13); proof of Proposition 4.9, p. 38 (PDF p. 39)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Assignments

namespace PermBlockchain.Transfers

/-- **The type assignments that agree with a revelation.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.2, p. 12 (PDF p. 13) and proof of Proposition 4.9, p. 38 (PDF p. 39).

`agreeSet r` is the set of `θ' ∈ Θ` such that `θ' j = τ` whenever `r j = some τ`. Because `Θ`
fixes the number of manufacturers of each type, revealing all but one type determines the
remaining one ("she is the only manufacturer that is not on the blockchain", p. 38). -/
def agreeSet {m : ℕ} (r : Mfr m → Option MType) : Finset (Mfr m → MType) :=
  (Assignments m).filter (fun θ' => ∀ j, ∀ τ : MType, r j = some τ → θ' j = τ)

end PermBlockchain.Transfers


