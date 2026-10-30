-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Hist
-- name    : PermBlockchain_Transfers_Hist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:46:19.629123+00:00
-- url     : https://prove2.me/theorems/5e398691-eb01-4237-8364-54b9e02b32cf
-- title:
--   Public history $(\{a_i\},\{P_i\})$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The public history observed by consumers consists of all adoption decisions $a_i$ and all consumer prices $P_i$; the consumer's information at the fee stage is $\mathcal G_k=\sigma(t_k,\phi_k,\{a_i,P_i\}_{i\in M})$. Vendor prices $\Psi_i$ are not observed by consumers.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 21 (PDF p. 22); proof of Proposition 4.9, p. 36 (PDF p. 37)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Mfr

namespace PermBlockchain.Transfers

/-- **The public history `({a_i}, {P_i})` that consumers observe.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 21 (PDF p. 22) and proof of Proposition 4.9, p. 36 (PDF p. 37): the consumer's
information set is `G_k = σ(t_k, φ_k, {a_i, P_i}_{i∈M})`; adoption decisions are "publicly
observable" (p. 12).

**Formalization Note.** Vendor prices `Ψ_i` are not part of `G_k` and are not in the history. -/
abbrev Hist (m : ℕ) : Type := (Mfr m → Bool) × (Mfr m → ℝ)

end PermBlockchain.Transfers


