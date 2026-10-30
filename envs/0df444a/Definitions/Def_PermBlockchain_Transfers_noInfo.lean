-- Prove2me | Definitions.Def_PermBlockchain_Transfers_noInfo
-- name    : PermBlockchain_Transfers_noInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:49:21.901828+00:00
-- url     : https://prove2.me/theorems/bfb84d94-fdec-4c98-85ca-5f2494485cf3
-- title:
--   The empty revelation
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The empty revelation reveals no manufacturer's type. It is what a consumer who does not pay the fee learns from the blockchain, and the information of every consumer at the fee stage.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Mfr

namespace PermBlockchain.Transfers

/-- **The empty revelation: nothing is learned from the blockchain.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 21 (PDF p. 22): with `b_k = 0`, or before any signal, `α = 1/2` signals are
uninformative. `noInfo` is the revelation of a consumer who did not pay the fee, and the
information of every consumer at the fee stage. -/
def noInfo {m : ℕ} : Mfr m → Option MType :=
  fun _ => none

end PermBlockchain.Transfers


