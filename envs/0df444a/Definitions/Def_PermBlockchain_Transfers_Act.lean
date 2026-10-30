-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Act
-- name    : PermBlockchain_Transfers_Act
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:45:05.399274+00:00
-- url     : https://prove2.me/theorems/dd73ab2b-0a67-4f9c-82d8-ac18be16becb
-- title:
--   A manufacturer's action $(a_i,P_i,\Psi_i)$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A manufacturer's action is a triple $(a_i,P_i,\Psi_i)$: the adoption decision $a_i\in\{0,1\}$ ($a_i=1$ joins the blockchain), the consumer price $P_i$ and the price $\Psi_i$ offered to its vendor.
--
--   **Formalization Note** The order quantity is not a separate choice: the manufacturer must fulfil its demand, $\sigma_i=s_i$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11); §3.2, pp. 12–13 (PDF pp. 13–14), displays (5), (8), (9)

import Mathlib

namespace PermBlockchain.Transfers

/-- **A manufacturer's action `(a_i, P_i, Ψ_i)`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.2, pp. 12–13 (PDF pp. 13–14): `a_i ∈ {0, 1}` is the blockchain adoption decision,
`P_i` the consumer price and `Ψ_i` the price offered to the vendor ((5), (8), (9)).

**Formalization Note.** `a_i = 1` is `true`. The order quantity is not a separate choice: the
manufacturer must fulfil its demand, `σ_i = s_i` ((5), (9)). -/
abbrev Act : Type := Bool × ℝ × ℝ

end PermBlockchain.Transfers


