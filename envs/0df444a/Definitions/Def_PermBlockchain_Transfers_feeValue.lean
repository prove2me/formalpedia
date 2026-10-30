-- Prove2me | Definitions.Def_PermBlockchain_Transfers_feeValue
-- name    : PermBlockchain_Transfers_feeValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:55:32.28046+00:00
-- url     : https://prove2.me/theorems/8ff3a6e2-6898-44c1-9aef-dccb7262a8eb
-- title:
--   Fee-stage value $g(b_k,\phi_k;\cdot)$, display (16)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   With transfers, consumer $k$ chooses whether to pay a fee $\kappa$ for access to the blockchain, solving
--   $$\max_{b_k\in\{0,1\}}\ \mathbb E^{b_k}\Bigl[\max\{\max_{i\in M}u_{ik},\phi_k\}-\kappa b_k\ \Big|\ \mathcal G_k\Bigr].\qquad(16)$$
--   The fee-stage value of $b$ is the expectation, under the fee-stage belief over the true assignment $\theta'$, of the best value after the blockchain reveals what access $b$ shows under $\theta'$ and the consumer updates her belief, minus $\kappa$ if $b=1$. The proof of Proposition 4.9 names this $g(b_k,\phi_k;\phi)$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, pp. 20–21 (PDF pp. 21–22), display (16); proof of Proposition 4.9, p. 36 (PDF p. 37)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_bestValue
import Definitions.Def_PermBlockchain_Transfers_revealed
import Definitions.Def_PermBlockchain_Transfers_noInfo
import Definitions.Def_PermBlockchain_Transfers_BeliefSystem

namespace PermBlockchain.Transfers

/-- **The fee-stage value `g(b_k, φ_k; ·) = E^{b_k}[max{max_i u_ik, φ_k} − κ b_k | G_k]`, display (16).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), (16); proof of Proposition 4.9, p. 36 (PDF p. 37), where it is
named `g(b_k, φ_k; φ)`.

`feeValue H L h l β κ x t φ b` is the expectation, under the fee-stage belief `β x false noInfo`
over the true type assignment `θ'`, of the best value the consumer obtains after the blockchain
reveals `revealed b θ' x` and she updates to `β x b (revealed b θ' x)`, minus the fee `κ` if
`b = true`.

**Formalization Note.** "The consumer's information set G_k when selecting b_k includes her
outside option value, her own type, and manufacturer prices and adoption decisions. Note that G_k
does not include the manufacturer signals" (pp. 20–21): hence the expectation over what the
blockchain will reveal. -/
noncomputable def feeValue {m : ℕ} (H L h l : ℝ) (β : BeliefSystem m) (κ : ℝ) (x : Hist m)
    (t : Horiz) (φ : ℝ) (b : Bool) : ℝ :=
  ∑ θ' ∈ Assignments m, β x false noInfo θ' * bestValue H L h l (β x b (revealed b θ' x)) x t φ
    - (if b then κ else 0)

end PermBlockchain.Transfers


