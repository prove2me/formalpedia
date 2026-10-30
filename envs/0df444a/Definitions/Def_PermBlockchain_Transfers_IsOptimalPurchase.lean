-- Prove2me | Definitions.Def_PermBlockchain_Transfers_IsOptimalPurchase
-- name    : PermBlockchain_Transfers_IsOptimalPurchase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:58:25.419441+00:00
-- url     : https://prove2.me/theorems/5f3bff6a-3a48-4c57-aa43-ceb429e4d6ae
-- title:
--   Optimal purchase decisions with the tie rule
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A purchase rule is optimal if at every consumer type, outside option, history, access decision and realizable revelation, under the corresponding belief: the weights are nonnegative and sum to $1$; they are positive only on options of maximal value; and they put no weight on the outside option whenever some manufacturer's utility is at least $\phi_k$. The last clause is the paper's rule: "consumer $k$ purchases the good from manufacturer $i(k)$ if her utility from doing so (weakly) exceeds $\phi_k$; otherwise she chooses the outside option".
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_optionValue
import Definitions.Def_PermBlockchain_Transfers_bestValue
import Definitions.Def_PermBlockchain_Transfers_revealed
import Definitions.Def_PermBlockchain_Transfers_BeliefSystem
import Definitions.Def_PermBlockchain_Transfers_PurchaseRule

namespace PermBlockchain.Transfers

/-- **Optimal purchase decisions, with the tie rule of §3.1.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13): "Consumer k ∈ [0, 1] will purchase the good from one of the
manufacturers if her utility from doing so (weakly) exceeds her outside option, i.e., if
max_{i∈M} u_ik ≥ φ_k. Let i(k) be a manufacturer that offers her maximum utility, i.e.,
i(k) ∈ arg max_{i∈M} u_ik."

At every type `t`, outside option `φ`, history `x`, access decision `b` and realizable
revelation `r = revealed b θ x` (`θ ∈ Θ`), with belief `β' = β x b r`: the weights are
nonnegative, sum to one, are positive only on options of maximal value, and put no weight on the
outside option when some manufacturer's utility is at least `φ`.

**Formalization Note.** The last clause is the paper's "(weakly) exceeds": on a tie with the
outside option the consumer buys. Ties among manufacturers may be split arbitrarily. -/
def IsOptimalPurchase {m : ℕ} (H L h l : ℝ) (β : BeliefSystem m) (w : PurchaseRule m) : Prop :=
  ∀ (t : Horiz) (φ : ℝ) (x : Hist m) (b : Bool), ∀ θ ∈ Assignments m,
    (∀ o, 0 ≤ w t φ x b (revealed b θ x) o) ∧
    ∑ o : Option (Mfr m), w t φ x b (revealed b θ x) o = 1 ∧
    (∀ o, 0 < w t φ x b (revealed b θ x) o →
      optionValue H L h l (β x b (revealed b θ x)) x t φ o =
        bestValue H L h l (β x b (revealed b θ x)) x t φ) ∧
    ((∃ i, φ ≤ utility H L h l (β x b (revealed b θ x)) x i t) →
      w t φ x b (revealed b θ x) none = 0)

end PermBlockchain.Transfers


