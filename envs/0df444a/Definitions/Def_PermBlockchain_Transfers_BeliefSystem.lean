-- Prove2me | Definitions.Def_PermBlockchain_Transfers_BeliefSystem
-- name    : PermBlockchain_Transfers_BeliefSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:30.701894+00:00
-- url     : https://prove2.me/theorems/8b581885-9ee4-40ba-8cbe-7aea088062c3
-- title:
--   Consumers' belief system
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A belief system gives, for every public history $x$, access decision $b$ and revelation $r$, a function on type assignments, read as the consumer's probability of each $\theta'\in\Theta$. The belief after $b=0$ and the empty revelation is the fee-stage belief, which is also the purchase-stage belief of a consumer who did not pay; the belief after $b=1$ and revelation $r$ is a fee payer's belief.
--
--   **Formalization Note** Beliefs do not depend on the consumer's own type or outside option, which are independent of the manufacturers' types.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), display (6); §4.2, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Hist

namespace PermBlockchain.Transfers

/-- **A belief system for consumers.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), (6): `E[V_ik | F_k]` is computed from the consumer's beliefs about
manufacturers' types; §4.2, p. 21 (PDF p. 22).

`β x b r θ'` is the probability a consumer with access decision `b` assigns to the type
assignment `θ'` after the public history `x` and the revelation `r`. `β x false noInfo` is the
fee-stage belief (and the purchase-stage belief of a consumer who did not pay); `β x true r` is
a fee payer's belief after the blockchain revealed `r`.

**Formalization Note.** Beliefs do not depend on the consumer's own type `t_k` or outside option
`φ_k`, which are independent of the manufacturers' types. -/
abbrev BeliefSystem (m : ℕ) : Type :=
  Hist m → Bool → (Mfr m → Option MType) → (Mfr m → MType) → ℝ

end PermBlockchain.Transfers


