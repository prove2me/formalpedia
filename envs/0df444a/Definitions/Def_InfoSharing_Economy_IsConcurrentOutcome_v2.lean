-- Prove2me | Definitions.Def_InfoSharing_Economy_IsConcurrentOutcome_v2
-- name    : InfoSharing_Economy_IsConcurrentOutcome_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:17:28.619238+00:00
-- url     : https://prove2.me/theorems/b789fc8c-e09d-47a4-a385-e809cb02cbfb
-- title:
--   Concurrent information contracting in the production economy: payoffs of Table 1, pure equilibria at a payment, and the retailer-optimal outcome (corrected selection)
-- statement:
--   Given a payoff table, the retailer offers both manufacturers the same payment $T\ge0$ for the demand signal and they decide simultaneously (Table 1, §5.2.1; §6.2 for the production economy). Manufacturer $i$ receives $M(X,i)-T\,[X_i=I]$ and the retailer $R(X)+nT$, $n$ the number of buyers.
--
--   1. $X$ is a **pure Nash equilibrium** at $T$ if no manufacturer gains by changing only his own decision (weak inequalities: an indifferent manufacturer may accept, the paper's tie-breaking convention).
--   2. $(T,X)$ is a **concurrent outcome** if $T\ge0$, $X$ is a pure equilibrium at $T$, and no pair $(T',X')$ with $T'\ge0$ and $X'$ a pure equilibrium at $T'$ gives the retailer more: the retailer chooses the payment, anticipating the manufacturers' equilibrium, to maximize $R(X)+nT$.
--
--   `ConcOptN P` is the set of values of $n$ attained by concurrent outcomes (the possible values of the paper's $n_e^C$); `concManufacturersTotal` is the manufacturers' total profit net of the payments.
--
--   **Formalization Note.** This is the selection the paper's proofs use (proof of Proposition 7, p. 261): for each $n$ the retailer charges the largest payment at which $n$ buyers is an equilibrium — $\pi_M^I(2)-\pi_M^U(1)$ for $n=2$, $\pi_M^I(1)-\pi_M(0)$ for $n=1$ — and picks the best $n$. In the production economy the one-buyer outcome at $T=\pi_M^I(1)-\pi_M(0)$ coexists with the equilibrium $(U,U)$, which both manufacturers weakly prefer, so no Pareto refinement among the manufacturers' equilibria is imposed. The retired module `Def_InfoSharing_Economy_IsConcurrentOutcome` instead took a supremum over Pareto-optimal equilibria, which is not attained at the value of $c_e$ where the two willingness-to-pay levels $\pi_M^I(1)-\pi_M(0)$ and $\pi_M^I(2)-\pi_M^U(1)$ coincide (accepted disproofs of Propositions 7 and 8(a)). For a fixed profile the set of payments sustaining it is closed and the retailer's payoff is continuous and nondecreasing in $T$, so an outcome exists. The declarations `concManufacturerPayoff`, `concRetailer`, `concManufacturersTotal`, `IsPureNE`, `ConcOptN` are unchanged; `IsParetoOptimalNE` is dropped.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, §5.2.1 and Table 1; p. 256, §6.2; p. 261, proof of Proposition 7

import Mathlib
import Definitions.Def_InfoSharing_Shared_PayoffTable
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- Manufacturer `i`'s payoff in the concurrent contracting game (§5.2.1, p. 253, Table 1;
§6.2, p. 256): his ex ante profit minus the payment `T` if he buys the information
(`X i = informed`). -/
def concManufacturerPayoff (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) (i : Fin 2) : ℝ :=
  P.M X i - if X i = Status.informed then T else 0

/-- The retailer's payoff in the concurrent game: her ex ante profit plus `T` per buyer. -/
def concRetailer (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : ℝ :=
  P.R X + T * (numInformed X : ℝ)

/-- The manufacturers' total payoff (net of the payments) in the concurrent game. -/
def concManufacturersTotal (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : ℝ :=
  ∑ i : Fin 2, concManufacturerPayoff P T X i

/-- `X` is a pure-strategy Nash equilibrium of the manufacturers' game of Table 1 at payment
`T`: no manufacturer gains by unilaterally changing his decision. The inequalities are weak:
a manufacturer who is indifferent between buying and not buying may do either, which is the
paper's convention that an indifferent manufacturer accepts the offer. -/
def IsPureNE (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : Prop :=
  ∀ (i : Fin 2) (s : Status),
    concManufacturerPayoff P T (Function.update X i s) i ≤ concManufacturerPayoff P T X i

/-- An outcome `(T, X)` of concurrent information contracting (§5.2.1, p. 253; §6.2, p. 256;
proof of Proposition 7, p. 261). The retailer offers the same nonnegative payment `T` to both
manufacturers, who then play a pure equilibrium `X` of the game of Table 1 at `T`; the retailer
chooses the payment, anticipating the equilibrium, to maximize her payoff `π_R(X) + nT`. An
outcome is a nonnegative payment and a pure equilibrium at that payment that give the retailer
at least as much as every other nonnegative payment with every pure equilibrium at it.

**Formalization Note.** This is the selection the paper's proofs use: for each number `n` of
buyers they take the largest payment at which `n` buyers is an equilibrium (an indifferent
manufacturer accepts) and let the retailer pick the best `n`; in the production economy the
retailer's choice `T = π_M^I(1) − π_M(0)` with one buyer (p. 261) is an equilibrium at which
`(U, U)` is also an equilibrium that both manufacturers weakly prefer, so no Pareto-type
refinement among the manufacturers' equilibria is imposed. The retired version of this
module selected a supremum over Pareto-optimal equilibria, which is not attained at the point
where the two willingness-to-pay levels coincide; this version replaces it. Over all payments
the retailer's payoff for a fixed profile is continuous and the set of payments sustaining it
is closed, so an outcome always exists. -/
def IsConcurrentOutcome (P : PayoffTable) (T : ℝ) (X : Fin 2 → Status) : Prop :=
  0 ≤ T ∧ IsPureNE P T X ∧
  ∀ (T' : ℝ) (X' : Fin 2 → Status), 0 ≤ T' → IsPureNE P T' X' →
    concRetailer P T' X' ≤ concRetailer P T X

/-- The set of numbers of informed manufacturers attained by concurrent outcomes (the possible
values of the paper's `n_e^C`). -/
def ConcOptN (P : PayoffTable) : Set ℕ :=
  {n | ∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X ∧ numInformed X = n}

end InfoSharing.Economy


