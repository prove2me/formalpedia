-- Prove2me | Definitions.Def_LaconicBarrier_Reduction
-- name    : LaconicBarrier_Reduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:44.783367+00:00
-- url     : https://prove2.me/theorems/d2ff95f6-b811-4fd5-89d6-6c5ce38cbf8a
-- title:
--   Black-box reductions and their target-parameter map
-- statement:
--   A **black-box reduction** $\mathcal R$ is a uniform oracle machine. On $1^\lambda$, a source index $x$ and an advice string $z$ it plays the target challenger $\mathcal C(1^{\lambda'})$ at $\lambda' = f(1^\lambda, |x|)$, its **target-parameter map**, and may query the source adversary as an oracle. With its coins and its view so far (the challenger's messages and the oracle's replies, in order) it decides its next action: send a message to the challenger, query the oracle, or halt. Halting, or exceeding its number of actions, before the challenger stops counts as a loss. The machine is defined on every index and every advice string.
--
--   **Formalization Note** Oracle calls are answered with fresh, independent coins; the reduction sees only the replies. The time bound, the advice length and the query count are separate definitions.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.6, pp.20–21 (Syntax)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier

/-- An event in the view of a reduction: a message from the target challenger, or a reply of the
source-adversary oracle. -/
inductive Ev where
  | fromChal (m : List Bool)
  | reply (a : List Bool)

/-- Whether an event is an oracle reply. -/
def Ev.isReply : Ev → Bool
  | .fromChal _ => false
  | .reply _ => true

/-- The code of an event (a tagged string). -/
def Ev.code : Ev → List Bool
  | .fromChal m => QAdvFew.PoQOracle.tup [[false], m]
  | .reply a => QAdvFew.PoQOracle.tup [[true], a]

/-- An action of a reduction: send a message to the target challenger, query the oracle, or halt. -/
inductive RedAct where
  | toChal (m : List Bool)
  | query (q : List Bool)
  | halt

/-- The code of a reduction action (a tagged tuple). -/
def RedAct.code : RedAct → List Bool
  | .toChal m => QAdvFew.PoQOracle.tup [[false, false], m]
  | .query q => QAdvFew.PoQOracle.tup [[false, true], q]
  | .halt => QAdvFew.PoQOracle.tup [[true]]

/-- A **black-box reduction** `R` with its target-parameter map `f` (Jain, Mathialagan, Roy, *From
Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission
(manuscript sha256 1af78662…), §4.1.6, pp.20–21, "Syntax"): an oracle machine which, on `1^λ`, the
source index `x` and an advice string `z`, plays the target challenger `C(1^{λ′})`, `λ′ = f(1^λ, |x|)`,
while querying the source adversary as an oracle.

With coins `ρ` and its view so far (challenger messages and oracle replies, in order), `next` gives
its next action. At most `fuel λ |x|` actions are taken; halting, or running out of actions, before
the challenger stops is a loss. The machine is defined on every binary index and advice string.

**Formalization Note** The reduction sees only the oracle's replies; each oracle call is answered
with fresh coins (the execution law `Reduction.winProb`). Its time bound is `Reduction.IsTTime`. -/
structure Reduction where
  /-- the number of coins at `(λ, |x|)` -/
  coins : ℕ → ℕ → ℕ
  /-- the number of actions after which the reduction loses -/
  fuel : ℕ → ℕ → ℕ
  /-- the next action from `λ`, the index, the advice, the coins and the view -/
  next : (lam : ℕ) → (x z : List Bool) → (Fin (coins lam x.length) → Bool) → List Ev → RedAct
  /-- the target-parameter map `(λ, n) ↦ f(1^λ, n)` -/
  f : ℕ → ℕ → ℕ

end LaconicBarrier


