-- Prove2me | Definitions.Def_PermBlockchain_Transfers_IsOptimalVendor
-- name    : PermBlockchain_Transfers_IsOptimalVendor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:04:07.154612+00:00
-- url     : https://prove2.me/theorems/e411401a-4ad0-4dee-92f5-e08eb8aead9c
-- title:
--   Optimal vendor fulfilment, displays (3)–(4)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A vendor rule is optimal if for every type assignment in $\Theta$, every price vector $\Psi\ge0$ and every demand vector $s\ge0$, its fulfilment levels satisfy $0\le\sigma_i\le s_i$ and, for each vendor, maximize that vendor's profit over all $\sigma'$ with $0\le\sigma'_i\le s_i$ on its manufacturers. This is (3)–(4) solved at every price and demand vector, i.e. the vendors' sequential rationality.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11), displays (3)–(4); §3.2, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Assignments
import Definitions.Def_PermBlockchain_Transfers_vendorProfit
import Definitions.Def_PermBlockchain_Transfers_VendorRule

namespace PermBlockchain.Transfers

/-- **Optimal vendor fulfilment at every price and demand vector, displays (3)–(4).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11), (3) and (4): each vendor maximizes its profit subject to
`0 ≤ σ_i ≤ s_i`, "where Ψ_i ≥ 0 denotes the price offered by manufacturer i, s_i ≥ 0 denotes the
anticipated demand"; §3.2, p. 13 (PDF p. 14): "the high type vendor solves (3) and the low type
vendor solves (4)".

For every `θ ∈ Θ`, every `Ψ ≥ 0` and every `s ≥ 0`, `σ = vend θ Ψ s` satisfies `0 ≤ σ_i ≤ s_i`
and, for each vendor `v`, maximizes `vendorProfit γ cl θ v Ψ` over all `σ'` with
`0 ≤ σ'_i ≤ s_i` on that vendor's manufacturers.

**Formalization Note.** Optimality is required at every `(Ψ, s)`, on and off the path: the
vendors move last, so this is their sequential rationality. -/
def IsOptimalVendor {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (vend : VendorRule m) : Prop :=
  ∀ θ ∈ Assignments m, ∀ Ψ s : Mfr m → ℝ, (∀ i, 0 ≤ Ψ i) → (∀ i, 0 ≤ s i) →
    (∀ i, 0 ≤ vend θ Ψ s i ∧ vend θ Ψ s i ≤ s i) ∧
    ∀ (v : Vert) (σ' : Mfr m → ℝ), (∀ i, (θ i).2 = v → 0 ≤ σ' i ∧ σ' i ≤ s i) →
      vendorProfit γ cl θ v Ψ σ' ≤ vendorProfit γ cl θ v Ψ (vend θ Ψ s)

end PermBlockchain.Transfers


