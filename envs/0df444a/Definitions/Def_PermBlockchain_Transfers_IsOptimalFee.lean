-- Prove2me | Definitions.Def_PermBlockchain_Transfers_IsOptimalFee
-- name    : PermBlockchain_Transfers_IsOptimalFee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:59:21.852055+00:00
-- url     : https://prove2.me/theorems/68b8c0b0-8589-40c6-afd5-115cb54aca97
-- title:
--   Optimal fee decisions, display (16)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A fee rule is optimal if at every consumer type, outside option and public history the chosen access decision has a fee-stage value at least as large as the other decision, i.e. it solves (16).
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), display (16)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_feeValue
import Definitions.Def_PermBlockchain_Transfers_FeeRule

namespace PermBlockchain.Transfers

/-- **Optimal fee decisions, display (16).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), (16): `max_{b_k∈{0,1}} E^{b_k}[max{max_{i∈M} u_ik, φ_k} − κ b_k | G_k]`.

At every type `t`, outside option `φ` and public history `x`, the decision `fee t φ x` is at
least as good as the other one. -/
def IsOptimalFee {m : ℕ} (H L h l : ℝ) (β : BeliefSystem m) (κ : ℝ) (fee : FeeRule m) : Prop :=
  ∀ (t : Horiz) (φ : ℝ) (x : Hist m),
    feeValue H L h l β κ x t φ (!(fee t φ x)) ≤ feeValue H L h l β κ x t φ (fee t φ x)

end PermBlockchain.Transfers


