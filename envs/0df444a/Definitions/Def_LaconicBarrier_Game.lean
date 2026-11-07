-- Prove2me | Definitions.Def_LaconicBarrier_Game
-- name    : LaconicBarrier_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:44.391204+00:00
-- url     : https://prove2.me/theorems/b13eee79-d85d-40ec-a577-381e09042a75
-- title:
--   Security game $(\mathcal C, c)$
-- statement:
--   A **security game** $(\mathcal C, c)$ consists of a probabilistic challenger $\mathcal C$ and a constant baseline $c \in [0,1)$. On common input $1^\lambda$ the challenger interacts with an adversary and outputs win or lose.
--
--   Concretely, at parameter $\lambda$ the challenger draws $\mathrm{coins}(\lambda)$ coins $\rho$; given the adversary's messages so far it either sends a message or stops with win or lose (it speaks first). After at most $\mathrm{fuel}(\lambda)$ actions a challenger that has not stopped outputs lose.
--
--   **Formalization Note** Coins and rounds are bounded at each $\lambda$. The games of the mission are run only at target parameters $\lambda' = f(1^\lambda, n)$, where the reduction's time bound bounds both; changing a game at other parameters only weakens hardness hypotheses that never look there.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.1, p.15

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier

/-- One action of a challenger: send a message, or stop with the outcome `win` or `lose`. -/
inductive ChalAct where
  | send (m : List Bool)
  | win
  | lose

/-- The code of a challenger action as a bit string (a tagged tuple). -/
def ChalAct.code : ChalAct → List Bool
  | .send m => QAdvFew.PoQOracle.tup [[false], m]
  | .win => QAdvFew.PoQOracle.tup [[true, true]]
  | .lose => QAdvFew.PoQOracle.tup [[true, false]]

/-- A **security game** `(C, c)` (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower
Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Definition
4.1, p.15): a probabilistic challenger `C`, which on common input `1^λ` interacts with an adversary
and outputs `win` or `lose`, and a constant baseline `c ∈ [0, 1)`.

The challenger at parameter `λ` uses `coins λ` coins `ρ`; given the adversary's messages so far,
`next λ ρ` gives its next action (it speaks first). At most `fuel λ` actions are taken; a challenger
that has not stopped by then outputs `lose`.

**Formalization Note** A challenger whose coins or rounds are unbounded at some `λ` is not covered;
this changes no statement of the mission, because the games used are run only at target parameters
`λ′ = f(1^λ, n)` where the reduction's time bound bounds both, and changing a game elsewhere only
weakens hardness hypotheses that never look there. -/
structure Game where
  /-- the number of challenger coins at parameter `λ` -/
  coins : ℕ → ℕ
  /-- the number of challenger actions after which the challenger outputs `lose` -/
  fuel : ℕ → ℕ
  /-- the next action, from `λ`, the coins and the adversary's messages so far -/
  next : (lam : ℕ) → (Fin (coins lam) → Bool) → List (List Bool) → ChalAct
  /-- the baseline -/
  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1

end LaconicBarrier


