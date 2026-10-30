-- Prove2me | Definitions.Def_PermBlockchain_Transfers_MType
-- name    : PermBlockchain_Transfers_MType
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:19.751693+00:00
-- url     : https://prove2.me/theorems/2dd5ddec-001d-463b-a218-64c07848d289
-- title:
--   Manufacturer type $(q_i,\xi_i)$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A manufacturer type is a pair
--   $$(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$$
--   of a horizontal and a vertical type; there are four types.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Horiz
import Definitions.Def_PermBlockchain_Transfers_Vert

namespace PermBlockchain.Transfers

/-- **A manufacturer type `(q_i, ξ_i) ∈ {A, B} × {h, l}`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered: "Each manufacturer i has a two-dimensional type
(q_i, ξ_i)". -/
abbrev MType : Type := Horiz × Vert

end PermBlockchain.Transfers


