-- Prove2me | Definitions.Def_PermBlockchain_Transfers_PurchaseRule
-- name    : PermBlockchain_Transfers_PurchaseRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:38.13784+00:00
-- url     : https://prove2.me/theorems/30a079b2-4d0e-45b7-aca1-3ffea1142bf6
-- title:
--   Purchase rule $m(k)$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A purchase rule gives, for each consumer type, outside option, public history, access decision and revelation, nonnegative weights on the options: buying from manufacturer $i$, or the outside option ($m(k)=\emptyset$).
--
--   **Formalization Note** Weights (a mixed choice) let ties among manufacturers be split in any proportion.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Hist

namespace PermBlockchain.Transfers

/-- **A purchase rule: the consumer's choice `m(k) ∈ M ∪ {∅}`, as weights on the options.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13): "consumer k purchases the good from manufacturer i(k) if her
utility from doing so (weakly) exceeds φ_k; otherwise she chooses the outside option. Denoting
this choice by m(k) …".

`w t φ x b r o` is the weight a consumer of type `t`, outside option `φ`, at history `x`, with
access decision `b` and revelation `r` puts on option `o` (`none` is the outside option, `some i`
buys from manufacturer `i`).

**Formalization Note.** Weights (a mixed choice) let ties among manufacturers be split in any
proportion; a pure choice is the case of a weight `1`. -/
abbrev PurchaseRule (m : ℕ) : Type :=
  Horiz → ℝ → Hist m → Bool → (Mfr m → Option MType) → Option (Mfr m) → ℝ

end PermBlockchain.Transfers


