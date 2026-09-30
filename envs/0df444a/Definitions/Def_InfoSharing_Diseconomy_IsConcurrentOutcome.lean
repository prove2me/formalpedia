-- Prove2me | Definitions.Def_InfoSharing_Diseconomy_IsConcurrentOutcome
-- name    : InfoSharing_Diseconomy_IsConcurrentOutcome
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:46:15.891386+00:00
-- url     : https://prove2.me/theorems/25018ddb-f3f7-409e-872f-a26d6ea9ad96
-- title:
--   Concurrent information contracting with Pareto-optimal selection, §5.2.1
-- statement:
--   Given a payoff table, the retailer offers both manufacturers the same payment $T \ge 0$ for the information, and they decide simultaneously (Table 1). Manufacturer $i$ receives $M(X,i) - T\,[X_i = I]$ and the retailer $R(X) + nT$.
--
--   1. $X$ is a **pure Nash equilibrium** at $T$ if no manufacturer gains by changing only his own decision.
--   2. It is **Pareto-optimal** if no other pure equilibrium at $T$ gives both manufacturers at least as much and one strictly more.
--   3. $(T, X)$ is a **concurrent outcome** if $T \ge 0$, $X$ is a Pareto-optimal equilibrium at $T$, and no pair $(T', X')$ with $T' \ge 0$ and $X'$ Pareto-optimal at $T'$ gives the retailer more.
--
--   The set of values of $n$ attained by concurrent outcomes is the set of possible $n_d^C$. The manufacturers' total profit is net of the payments.
--
--   **Formalization Note.** Only pure strategies are considered, as in the paper's analysis of Table 1. When two Pareto-optimal equilibria exist at the same $T$, the retailer's best one is selected, which is the choice made in the proof of Proposition 2 at $T = \pi_M(2) - \pi_M(0)$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, §5.2.1, Table 1; p. 260, proof of Proposition 2

import Mathlib
import Definitions.Def_InfoSharing_Shared_PayoffTable
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- Manufacturer `i`'s payoff in the concurrent contracting game (§5.2.1, p. 253, Table 1): his
ex ante profit minus the payment `T` if he buys the information (`X i = informed`). -/
def concManufacturerPayoff (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) (i : Fin 2) : ℝ :=
  P.M X i - if X i = Status.informed then T else 0

/-- The retailer's payoff in the concurrent game: her ex ante profit plus `T` per buyer. -/
def concRetailer (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : ℝ :=
  P.R X + T * (numInformed X : ℝ)

/-- The manufacturers' total payoff (net of the payments) in the concurrent game. -/
def concManufacturersTotal (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : ℝ :=
  ∑ i : Fin 2, concManufacturerPayoff P T X i

/-- `X` is a pure-strategy Nash equilibrium of the manufacturers' game of Table 1 at payment
`T`: no manufacturer gains by unilaterally changing his decision. -/
def IsPureNE (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : Prop :=
  ∀ (i : Fin 2) (s : Status),
    concManufacturerPayoff P T (Function.update X i s) i ≤ concManufacturerPayoff P T X i

/-- `X` is a Pareto-optimal pure equilibrium: no other pure equilibrium gives both
manufacturers at least as much and one of them strictly more. -/
def IsParetoOptimalNE (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : Prop :=
  IsPureNE P T X ∧
  ¬ ∃ X', IsPureNE P T X' ∧
    (∀ i, concManufacturerPayoff P T X i ≤ concManufacturerPayoff P T X' i) ∧
    ∃ i, concManufacturerPayoff P T X i < concManufacturerPayoff P T X' i

/-- An outcome `(T, X)` of concurrent information contracting (§5.2.1, p. 253): the payment is
nonnegative, `X` is a Pareto-optimal equilibrium of the manufacturers' game at `T`, and no
other nonnegative payment with any Pareto-optimal equilibrium gives the retailer more. -/
def IsConcurrentOutcome (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : Prop :=
  0 ≤ T ∧ IsParetoOptimalNE P T X ∧
  ∀ (T' : ℝ) (X' : Fin 2 → Status), 0 ≤ T' → IsParetoOptimalNE P T' X' →
    concRetailer P T' X' ≤ concRetailer P T X

/-- The set of numbers of informed manufacturers attained by concurrent outcomes (the possible
values of the paper's `n_d^C`). -/
def ConcOptN (P : PayoffTable) : Set ℕ :=
  {n | ∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X ∧ numInformed X = n}

end InfoSharing.Diseconomy


