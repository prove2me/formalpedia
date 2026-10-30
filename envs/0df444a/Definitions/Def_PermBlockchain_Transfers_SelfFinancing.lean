-- Prove2me | Definitions.Def_PermBlockchain_Transfers_SelfFinancing
-- name    : PermBlockchain_Transfers_SelfFinancing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:09:37.687357+00:00
-- url     : https://prove2.me/theorems/7fa2d337-ca70-40a6-9b27-5b8cda21704f
-- title:
--   Self-financing transfers, display (14)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The system of transfers $(\kappa,\{\tau_i\})$ is self-financing if
--   $$\kappa\cdot\mu_\kappa=\sum_{i\in M}\tau_i\qquad(14)$$
--   on the equilibrium path, for every type assignment, where $\mu_\kappa$ is the mass of consumers who pay the fee.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), display (14)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_feeMass
import Definitions.Def_PermBlockchain_Transfers_onPath
import Definitions.Def_PermBlockchain_Transfers_histOf
import Definitions.Def_PermBlockchain_Transfers_Assignments

namespace PermBlockchain.Transfers

/-- **Self-financing transfers, display (14).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21): "We require that the system of transfers (κ, {τ_i}_{i∈M}) must
be self-financing, in the sense that the payments to manufacturers are fully funded from consumer
payments, without any external financing, i.e. κ · µκ = Σ_{i:i∈M} τ_i (14)".

`SelfFinancing ν κ τ act fee` states (14) on the equilibrium path, for every type assignment. -/
def SelfFinancing {m : ℕ} (ν : MeasureTheory.Measure ℝ) (κ : ℝ) (τ : Mfr m → ℝ)
    (act : Strategy m) (fee : FeeRule m) : Prop :=
  ∀ θ ∈ Assignments m, κ * feeMass ν fee (histOf (onPath act θ)) = ∑ i, τ i

end PermBlockchain.Transfers


