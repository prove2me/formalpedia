-- Prove2me | Definitions.Def_PermBlockchain_Transfers_IsMeasurableRules
-- name    : PermBlockchain_Transfers_IsMeasurableRules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:59:53.572363+00:00
-- url     : https://prove2.me/theorems/618d804a-4474-4cd7-8795-7dc2c38cad47
-- title:
--   Measurability of consumers' rules
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The purchase weights are measurable functions of the outside option $\phi$, and the set of outside options for which a consumer pays the fee is measurable, for every type and history.
--
--   **Formalization Note** The paper measures sets of consumers ($s_i=\mu(\{k:m(k)=i\})$, $\mu_\kappa=\mu(\{k:b_k=1\})$) and takes them to be measurable implicitly; without this condition the demand integrals would not be meaningful.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), display (7); §4.2, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_FeeRule
import Definitions.Def_PermBlockchain_Transfers_PurchaseRule

namespace PermBlockchain.Transfers

/-- **Measurability of the consumers' rules in the outside option `φ`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), (7): `s_i = μ({k : m(k) = i})` and §4.2, p. 21 (PDF p. 22):
`μ_κ = μ({k : b_k = 1})` are measures of sets of consumers.

**Formalization Note.** The paper takes these sets to be measurable without saying so. The
clause makes the demand integrals and the fee mass of `demand` and `feeMass` meaningful (a
Bochner integral of a non-measurable function is `0` in Lean). -/
def IsMeasurableRules {m : ℕ} (fee : FeeRule m) (w : PurchaseRule m) : Prop :=
  (∀ t x b r o, Measurable (fun φ => w t φ x b r o)) ∧
  (∀ t x, MeasurableSet {φ : ℝ | fee t φ x = true})

end PermBlockchain.Transfers


