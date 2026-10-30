-- Prove2me | Definitions.Def_PermBlockchain_Transfers_payoff
-- name    : PermBlockchain_Transfers_payoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:40.4033+00:00
-- url     : https://prove2.me/theorems/2eafb6be-18b4-4b0c-aa77-6e9dc9065422
-- title:
--   Manufacturer payoff with transfers, display (15)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   With transfers, manufacturer $i$ solves
--   $$\max_{a_i\in\{0,1\}}\ \Pi(a_i,a_{-i})-\chi_ia_i+\tau_ia_i,\qquad \Pi(a_i,a_{-i})=\max_{P_i,\Psi_i\ge0}P_is_i-\Psi_is_i\ \text{ s.t. }\sigma_i=s_i.$$
--   The payoff at an action profile is $P_is_i-\Psi_is_i+(\tau_i-\chi_i)a_i$, where $\chi_i$ is the adoption cost and $\tau_i$ the transfer.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), display (15); display (9), p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_sOf

namespace PermBlockchain.Transfers

/-- **Manufacturer `i`'s payoff with transfers, the objective of (15).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), (15): `max_{a_i∈{0,1}} Π(a_i, a_{−i}) − χ_i a_i + τ_i a_i`, with
(9), p. 13 (PDF p. 14): `Π(a_i, a_{−i}) := max_{P_i,Ψ_i≥0} P_i · s_i − Ψ_i · s_i s.t. σ_i = s_i`.

`payoff ν fee w χ τ θ α i` is `P_i s_i − Ψ_i s_i + (τ_i − χ_i) a_i` at the action profile `α`. -/
noncomputable def payoff {m : ℕ} (ν : MeasureTheory.Measure ℝ) (fee : FeeRule m)
    (w : PurchaseRule m) (χ τ : Mfr m → ℝ) (θ : Mfr m → MType) (α : Mfr m → Act) (i : Mfr m) :
    ℝ :=
  (α i).2.1 * sOf ν fee w θ α i - (α i).2.2 * sOf ν fee w θ α i +
    (if (α i).1 then τ i - χ i else 0)

end PermBlockchain.Transfers


