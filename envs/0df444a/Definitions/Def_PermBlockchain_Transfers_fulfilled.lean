-- Prove2me | Definitions.Def_PermBlockchain_Transfers_fulfilled
-- name    : PermBlockchain_Transfers_fulfilled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:06:36.181261+00:00
-- url     : https://prove2.me/theorems/8b7fcb56-6dca-4d79-80fc-2eddecf34ef0
-- title:
--   Fulfilment constraint $\sigma_i=s_i$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   Manufacturer $i$'s demand is fulfilled at an action profile if $\sigma_i=s_i$. The paper assumes "that each manufacturer faces an arbitrarily large cost for not fulfilling any consumer order and therefore needs to ensure that all the anticipated demand $s_i$ is fulfilled, i.e. $\sigma_i=s_i$".
--
--   **Formalization Note** The arbitrarily large cost is encoded as this constraint: an action that leaves $\sigma_i\neq s_i$ is not admissible for manufacturer $i$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 11 (PDF p. 12), display (5); display (9), p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_sigmaOf

namespace PermBlockchain.Transfers

/-- **Manufacturer `i`'s demand is fulfilled: the constraint `σ_i = s_i` of (5) and (9).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 11 (PDF p. 12): "We assume that each manufacturer faces an arbitrarily large cost
for not fulfilling any consumer order and therefore needs to ensure that all the anticipated
demand s_i is fulfilled, i.e. σ_i = s_i"; (9), p. 13 (PDF p. 14).

**Formalization Note.** The arbitrarily large cost is encoded as a constraint: an action under
which `σ_i ≠ s_i` is not admissible for manufacturer `i`. -/
def fulfilled {m : ℕ} (ν : MeasureTheory.Measure ℝ) (fee : FeeRule m) (w : PurchaseRule m)
    (vend : VendorRule m) (θ : Mfr m → MType) (α : Mfr m → Act) (i : Mfr m) : Prop :=
  sigmaOf ν fee w vend θ α i = sOf ν fee w θ α i

end PermBlockchain.Transfers


