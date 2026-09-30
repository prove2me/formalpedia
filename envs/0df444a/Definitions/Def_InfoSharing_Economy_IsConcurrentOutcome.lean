-- Prove2me | Definitions.Def_InfoSharing_Economy_IsConcurrentOutcome
-- name    : InfoSharing_Economy_IsConcurrentOutcome
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T23:38:26.370788+00:00
-- url     : https://prove2.me/theorems/fb62169f-7cbc-4eec-a14b-fc7c3d026658
-- title:
--   Concurrent information contracting (Table 1): Pareto-optimal equilibria and the retailer's optimal payment
-- statement:
--   Let $M$, $R$ be a payoff table. Under **concurrent contracting** the retailer offers both manufacturers the same payment $T \ge 0$ for the information; the manufacturers decide simultaneously, $X_i = I$ meaning that $i$ pays $T$ and is informed. Payoffs:
--
--   $$u_i(T, X) = M(X, i) - T\,\mathbf 1[X_i = I], \qquad \text{retailer: } R(X) + T\, n(X).$$
--
--   1. $X$ is a **pure equilibrium** at $T$ if no manufacturer gains by switching his own status (all four cells of Table 1 are candidates).
--   2. $X$ is a **Pareto-optimal equilibrium** at $T$ if it is a pure equilibrium and no other pure equilibrium gives both manufacturers at least as much and one of them strictly more.
--   3. An **outcome** is a pair $(T, X)$ with $T \ge 0$ and $X$ a pure equilibrium at $T$ whose retailer payoff equals
--
--   $$\sup\{R(X') + T' n(X') : T' \ge 0,\ X' \text{ Pareto-optimal equilibrium at } T'\}.$$
--
--   $\mathrm{ConcOptN}$ is the set of values $n(X)$ over all outcomes (the possible values of $n_e^C$). The manufacturers' total payoff $\sum_i u_i(T, X)$ is net of the payments.
--
--   **Formalization Note** Only pure strategies are considered, as in the paper's analysis of Table 1. When a Pareto-optimal equilibrium attains the supremum, outcomes are exactly the retailer-optimal equilibria. The supremum form is needed in the production economy: for $c_e \ge c_e^C$ with $\pi_M(0) > \pi_M^U(1)$ the paper's optimal payment $T = \pi_M^I(1) - \pi_M(0)$ with one informed manufacturer (proof of Proposition 7, p. 261) is a limit of Pareto-optimal equilibria but, at that payment, $(U,U)$ Pareto-dominates $(I,U)$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, §5.2.1 and Table 1; p. 256, §6.2; p. 261, proof of Proposition 7

import Mathlib
import Definitions.Def_InfoSharing_Shared_PayoffTable
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- Manufacturer `i`'s payoff in the concurrent contracting game (§5.2.1, p. 253, Table 1; §6.2, p. 256): his
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

/-- An outcome `(T, X)` of concurrent information contracting (§5.2.1, p. 253; §6.2, p. 256).
The retailer offers the same nonnegative payment to both manufacturers, and the manufacturers
play a Pareto-optimal pure equilibrium of Table 1 at that payment. An outcome is a nonnegative
payment `T` and a pure equilibrium `X` at `T` whose retailer payoff equals the supremum of the
retailer's payoffs over all nonnegative payments `T'` and all Pareto-optimal equilibria `X'`
at `T'`: it is at least each of them, and exceeds none of them by `ε` or more.

**Formalization Note.** When a Pareto-optimal equilibrium attains that supremum, the outcomes
are exactly the retailer-optimal pure equilibria. The supremum clause is needed because in the
production economy it is not always attained by a Pareto-optimal equilibrium: for
`c_e^C ≤ c_e < 2/(1+φ)` with `π_M(0) > π_M^U(1)` the retailer's optimal payment is
`T = π_M^I(1) − π_M(0)` with one informed manufacturer (proof of Proposition 7, p. 261), and at
that payment `(U, U)` is also an equilibrium that Pareto-dominates `(I, U)`. -/
def IsConcurrentOutcome (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : Prop :=
  0 ≤ T ∧ IsPureNE P T X ∧
  (∀ (T' : ℝ) (X' : Fin 2 → Status), 0 ≤ T' → IsParetoOptimalNE P T' X' →
    concRetailer P T' X' ≤ concRetailer P T X) ∧
  ∀ ε : ℝ, 0 < ε → ∃ (T' : ℝ) (X' : Fin 2 → Status), 0 ≤ T' ∧ IsParetoOptimalNE P T' X' ∧
    concRetailer P T X < concRetailer P T' X' + ε

/-- The set of numbers of informed manufacturers attained by concurrent outcomes (the possible
values of the paper's `n_e^C`). -/
def ConcOptN (P : PayoffTable) : Set ℕ :=
  {n | ∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X ∧ numInformed X = n}

end InfoSharing.Economy


