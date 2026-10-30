-- Prove2me | Definitions.Def_PermBlockchain_Transfers_IsTransferEquilibrium
-- name    : PermBlockchain_Transfers_IsTransferEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:08:52.369378+00:00
-- url     : https://prove2.me/theorems/c87e37b3-866d-4e57-ae3f-3616a2151ba6
-- title:
--   Equilibrium of the game with transfers
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   Given the fee $\kappa$ and transfers $(\tau_i)$, a strategy profile, belief system, fee rule, purchase rule and vendor rule form an equilibrium if:
--
--   1. beliefs are Bayes-consistent;
--   2. purchase decisions are optimal at every history, with the tie rule of §3.1;
--   3. fee decisions solve (16) at every history;
--   4. consumers' rules are measurable in the outside option;
--   5. vendors solve (3)–(4) at every price and demand vector;
--   6. for every type assignment $\theta\in\Theta$, at the prescribed action profile: prices are nonnegative, every manufacturer's demand is fulfilled, and no manufacturer gains from a unilateral deviation to any $(a',P',\Psi')$ with $P',\Psi'\ge0$ that keeps its own demand fulfilled, consumers and vendors responding by the rules above.
--
--   **Formalization Note** The paper never defines "equilibrium"; this is the perfect Bayesian equilibrium of its timing. Following (9) and (15), a deviation changes $(a_i,P_i,\Psi_i)$ jointly while the other manufacturers keep their actions, as in the proof of Proposition 4.9 ("Fix $i$ and suppose $a_j=1$ for all $j\in M\setminus\{i\}$ …", p. 37). The conditions hold for every type assignment, so the equilibrium does not depend on whether manufacturers know each other's types (p. 8).
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, pp. 20–21 (PDF pp. 21–22), displays (14)–(16); §3, pp. 10–13 (PDF pp. 11–14), displays (3)–(9)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_IsConsistentBelief
import Definitions.Def_PermBlockchain_Transfers_IsOptimalPurchase
import Definitions.Def_PermBlockchain_Transfers_IsOptimalFee
import Definitions.Def_PermBlockchain_Transfers_IsMeasurableRules
import Definitions.Def_PermBlockchain_Transfers_IsOptimalVendor
import Definitions.Def_PermBlockchain_Transfers_fulfilled
import Definitions.Def_PermBlockchain_Transfers_payoff

namespace PermBlockchain.Transfers

/-- **An equilibrium of the game with transfers `(κ, {τ_i})`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, pp. 20–21 (PDF pp. 21–22): the manufacturers solve (15), the consumers solve (16)
and purchase as in (6)–(7), and the vendors solve (3)–(4); §3.2, pp. 12–13 for the timing.

`IsTransferEquilibrium ν H L h l γ cl χ κ τ act β fee w vend` is the conjunction of:
1. `IsConsistentBelief act β` (Bayes-consistent beliefs);
2. `IsOptimalPurchase` (purchase decisions optimal at every history, tie rule of §3.1);
3. `IsOptimalFee` ((16) at every history);
4. `IsMeasurableRules` (the consumer rules are measurable in `φ`);
5. `IsOptimalVendor` ((3)–(4) at every price and demand vector);
6. for every type assignment `θ ∈ Θ`, at the prescribed profile `α₀ = onPath act θ`: prices are
   nonnegative; every manufacturer's demand is fulfilled; and no manufacturer `i` gains from a
   unilateral deviation to any `(a', P', Ψ')` with `P', Ψ' ≥ 0` that keeps its own demand
   fulfilled, consumers and vendors responding by the rules above.

**Formalization Note.** The paper does not define "equilibrium"; this is the perfect Bayesian
equilibrium of the timing on pp. 12–13 and 20–21. Following (9) and (15), a deviation changes
`(a_i, P_i, Ψ_i)` jointly while the other manufacturers keep their actions, as in the proof of
Proposition 4.9 ("Fix i and suppose a_j = 1 for all j ∈ M ∖ {i} …", p. 37). The conditions are
required for every type assignment, so the equilibrium does not depend on whether manufacturers
know each other's types (p. 8). -/
def IsTransferEquilibrium {m : ℕ} (ν : MeasureTheory.Measure ℝ) (H L h l γ : ℝ) (cl : ℝ → ℝ)
    (χ : Mfr m → ℝ) (κ : ℝ) (τ : Mfr m → ℝ) (act : Strategy m) (β : BeliefSystem m)
    (fee : FeeRule m) (w : PurchaseRule m) (vend : VendorRule m) : Prop :=
  IsConsistentBelief act β ∧ IsOptimalPurchase H L h l β w ∧ IsOptimalFee H L h l β κ fee ∧
  IsMeasurableRules fee w ∧ IsOptimalVendor γ cl vend ∧
  ∀ θ ∈ Assignments m,
    (∀ i, 0 ≤ (onPath act θ i).2.1 ∧ 0 ≤ (onPath act θ i).2.2) ∧
    (∀ i, fulfilled ν fee w vend θ (onPath act θ) i) ∧
    (∀ (i : Mfr m) (a' : Bool) (P' Ψ' : ℝ), 0 ≤ P' → 0 ≤ Ψ' →
      fulfilled ν fee w vend θ (Function.update (onPath act θ) i (a', P', Ψ')) i →
      payoff ν fee w χ τ θ (Function.update (onPath act θ) i (a', P', Ψ')) i ≤
        payoff ν fee w χ τ θ (onPath act θ) i)

end PermBlockchain.Transfers


