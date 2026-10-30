-- Prove2me | Definitions.Def_PermBlockchain_Transfers_IsConsistentBelief
-- name    : PermBlockchain_Transfers_IsConsistentBelief
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:51:46.616144+00:00
-- url     : https://prove2.me/theorems/46401f3e-9c98-47b1-b79a-d871b7e912be
-- title:
--   Bayes-consistent consumer beliefs
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   A belief system $\beta$ is consistent with a strategy profile if:
--
--   1. after every history and every revelation that can occur under some $\theta\in\Theta$, $\beta$ is a probability distribution on $\Theta$ supported on the assignments that agree with the revelation;
--   2. after every history $x$ on the path of the profile, the fee-stage belief is the uniform prior on $\Theta$ conditioned on $x$, i.e. uniform on the consistent set;
--   3. after every history, a fee payer's belief is the fee-stage belief conditioned on what the blockchain revealed, whenever that event has positive fee-stage probability.
--
--   This is the belief requirement of a perfect Bayesian equilibrium, with the paper's prior: "it is public knowledge that there are exactly $m$ manufacturers of each type, and consumers assume each manufacturer is equally likely to be of each type ex ante".
--
--   **Formalization Note** Where Bayes' rule does not apply, beliefs are free except for the support condition. The paper does not define its equilibrium notion; this is the standard convention.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13); §3.2, p. 12 (PDF p. 13); §4.2, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_consistentSet
import Definitions.Def_PermBlockchain_Transfers_revealed
import Definitions.Def_PermBlockchain_Transfers_noInfo
import Definitions.Def_PermBlockchain_Transfers_agreeSet
import Definitions.Def_PermBlockchain_Transfers_BeliefSystem

namespace PermBlockchain.Transfers

/-- **Bayes-consistent beliefs (perfect Bayesian equilibrium beliefs).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13): "it is public knowledge that there are exactly m manufacturers
of each type, and consumers assume each manufacturer is equally likely to be of each type ex
ante"; §3.2, p. 12 (PDF p. 13) and §4.2, p. 21 (PDF p. 22) for what the blockchain reveals.

`IsConsistentBelief act β` is the conjunction of:
1. for every history `x`, access decision `b` and realizable revelation `r = revealed b θ x`
   (`θ ∈ Θ`), `β x b r` is a probability distribution on `Θ` supported on `agreeSet r`;
2. if `x` is on the path of `act`, the fee-stage belief `β x false noInfo` is the uniform prior
   on `Θ` conditioned on `x`, i.e. uniform on `consistentSet act x`;
3. a fee payer's belief `β x true r` is the fee-stage belief conditioned on `agreeSet r`
   whenever that event has positive fee-stage probability.

**Formalization Note.** Where Bayes' rule does not apply (off the path of `act`, or after a
revelation of fee-stage probability zero) beliefs are free, subject to clause 1: this is the
perfect Bayesian equilibrium convention; the paper does not define its equilibrium notion. The
support clause is required only for realizable revelations, for which `agreeSet r` is
nonempty. -/
def IsConsistentBelief {m : ℕ} (act : Strategy m) (β : BeliefSystem m) : Prop :=
  (∀ (x : Hist m) (b : Bool), ∀ θ ∈ Assignments m,
      (∀ θ', 0 ≤ β x b (revealed b θ x) θ') ∧
      (∀ θ', 0 < β x b (revealed b θ x) θ' → θ' ∈ agreeSet (revealed b θ x)) ∧
      ∑ θ' ∈ Assignments m, β x b (revealed b θ x) θ' = 1) ∧
  (∀ x : Hist m, (consistentSet act x).Nonempty → ∀ θ',
      β x false noInfo θ' =
        if θ' ∈ consistentSet act x then 1 / ((consistentSet act x).card : ℝ) else 0) ∧
  (∀ x : Hist m, ∀ θ ∈ Assignments m,
      0 < ∑ θ'' ∈ agreeSet (revealed true θ x), β x false noInfo θ'' → ∀ θ',
      β x true (revealed true θ x) θ' =
        if θ' ∈ agreeSet (revealed true θ x) then
          β x false noInfo θ' / ∑ θ'' ∈ agreeSet (revealed true θ x), β x false noInfo θ''
        else 0)

end PermBlockchain.Transfers


