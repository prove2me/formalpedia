-- Prove2me | Definitions.Def_PermBlockchain_Transfers_vendorProfit
-- name    : PermBlockchain_Transfers_vendorProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:03:19.94632+00:00
-- url     : https://prove2.me/theorems/0a5af684-6047-419c-8080-5c8bb25c78b6
-- title:
--   Vendor profit, displays (3)–(4)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The profit of vendor $v\in\{h,l\}$ from fulfilment levels $\sigma$ is
--   $$\sum_{i:\xi_i=v}\Psi_i\sigma_i-c_v\Bigl(\sum_{i:\xi_i=v}\sigma_i\Bigr),$$
--   the objective of (3) and (4).
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11), displays (3)–(4)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Mfr
import Definitions.Def_PermBlockchain_Transfers_vendorCost

namespace PermBlockchain.Transfers

/-- **The vendor's objective, displays (3) and (4).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11), (3): `Σ_{i:ξ_i=h} Ψ_i σ_i − c_h(Σ_{i:ξ_i=h} σ_i)`, and (4), the same
for vendor `l` with `c_l`.

`vendorProfit γ cl θ v Ψ σ` is the profit of the vendor of type `v` from fulfilment levels `σ`
of the orders of the manufacturers `i` with `(θ i).2 = v`. -/
noncomputable def vendorProfit {m : ℕ} (γ : ℝ) (cl : ℝ → ℝ) (θ : Mfr m → MType) (v : Vert)
    (Ψ σ : Mfr m → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = v), Ψ i * σ i
    - vendorCost γ cl v (∑ i ∈ Finset.univ.filter (fun i => (θ i).2 = v), σ i)

end PermBlockchain.Transfers


