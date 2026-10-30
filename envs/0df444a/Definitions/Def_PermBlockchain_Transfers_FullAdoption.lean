-- Prove2me | Definitions.Def_PermBlockchain_Transfers_FullAdoption
-- name    : PermBlockchain_Transfers_FullAdoption
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:10:12.501265+00:00
-- url     : https://prove2.me/theorems/2930fbda-ecfa-4b0a-99fb-88e98862cb35
-- title:
--   Full blockchain adoption
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A strategy profile has full adoption if, for every type assignment, every manufacturer joins the blockchain: $a_i=1$ for all $i\in M$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4, p. 14 (PDF p. 15); §4.2, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_onPath
import Definitions.Def_PermBlockchain_Transfers_Assignments

namespace PermBlockchain.Transfers

/-- **Full blockchain adoption on the equilibrium path.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4, p. 14 (PDF p. 15): "Full Adoption: Every manufacturer joins the blockchain, i.e., a_i = 1
for all i ∈ M"; §4.2, p. 21 (PDF p. 22): "an equilibrium in which all manufacturers adopt
blockchain (i.e., a_i = 1 for all i ∈ M)". -/
def FullAdoption {m : ℕ} (act : Strategy m) : Prop :=
  ∀ θ ∈ Assignments m, ∀ i, (onPath act θ i).1 = true

end PermBlockchain.Transfers


