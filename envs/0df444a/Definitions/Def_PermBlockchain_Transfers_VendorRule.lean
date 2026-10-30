-- Prove2me | Definitions.Def_PermBlockchain_Transfers_VendorRule
-- name    : PermBlockchain_Transfers_VendorRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:25.72555+00:00
-- url     : https://prove2.me/theorems/40f524d9-dc18-4dc3-82e7-8319696de60b
-- title:
--   Vendor fulfilment rule
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A vendor fulfilment rule gives the fulfilment levels $\sigma_i$ of all orders as a function of the manufacturers' types, the vendor prices $\Psi$ and the demands $s$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Mfr

namespace PermBlockchain.Transfers

/-- **A vendor fulfilment rule `(θ, Ψ, s) ↦ σ`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11): "vendor h selects a fulfillment level, σ_i ≥ 0, for each order
from a manufacturer i with ξ_i = h"; similarly vendor l.

`vend θ Ψ s i` is the fulfilment level `σ_i` of manufacturer `i`'s order, given the types `θ`
(each vendor knows which manufacturers order from it), the vendor prices `Ψ` and the demands `s`. -/
abbrev VendorRule (m : ℕ) : Type :=
  (Mfr m → MType) → (Mfr m → ℝ) → (Mfr m → ℝ) → Mfr m → ℝ

end PermBlockchain.Transfers


