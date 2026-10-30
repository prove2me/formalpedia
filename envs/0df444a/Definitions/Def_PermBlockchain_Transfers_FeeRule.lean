-- Prove2me | Definitions.Def_PermBlockchain_Transfers_FeeRule
-- name    : PermBlockchain_Transfers_FeeRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:55:56.655883+00:00
-- url     : https://prove2.me/theorems/3c6beec1-4e02-49bb-9a79-20f18f9bc74f
-- title:
--   Fee rule $b_k$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A fee rule gives the access decision $b_k\in\{0,1\}$ of a consumer as a function of her information $\mathcal G_k=(t_k,\phi_k,\{a_i,P_i\})$: her type, her outside option and the public history.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, pp. 20–21 (PDF pp. 21–22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Horiz
import Definitions.Def_PermBlockchain_Transfers_Hist

namespace PermBlockchain.Transfers

/-- **A fee rule: consumer `k`'s access decision `b_k` as a function of `G_k`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, pp. 20–21 (PDF pp. 21–22): `b_k ∈ {0, 1}` is chosen with information
`G_k = σ(t_k, φ_k, {a_i, P_i}_{i∈M})`.

`fee t φ x` is the decision of a consumer of type `t` with outside option `φ` at history `x`. -/
abbrev FeeRule (m : ℕ) : Type := Horiz → ℝ → Hist m → Bool

end PermBlockchain.Transfers


