-- Prove2me | Definitions.Def_SmoothedNash_runTime
-- name    : SmoothedNash_runTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:31.323853+00:00
-- url     : https://prove2.me/theorems/3e22e421-85e9-452b-92c2-bab815565a86
-- title:
--   Running time in the cost model of Theorem 2.2
-- statement:
--   In the running-time clause of Theorem 2.2, one computation of the deviation payoff vector $U(x)$ costs time $T$, and generating grid points and children and checking the test cost $\mathrm{poly}(mn)$ coordinate operations per unit. For an exponent $\kappa \in \mathbb N$, the **running time** of a run with $E$ payoff-vector computations and $W$ work units is
--   $$
--   T \cdot E + (mn + 1)^{\kappa} \cdot W .
--   $$
--
--   **Formalization Note** The paper leaves the polynomial overhead unspecified; Theorem 2.2's running-time clause is stated for every exponent $\kappa$, which covers every polynomial overhead.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 2.2, p.15, and proof of Theorem 2.2, p.19

import Mathlib
import Definitions.Def_SmoothedNash_RunResult

namespace SmoothedNash

/-- The running time of a run in the cost model of Theorem 2.2 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.15 and 19): `T` per
computation of the deviation-payoff vector `U(x)`, plus `(mn + 1)^κ` coordinate operations per unit
of enumeration and test work ("poly(mn) coordinate operations per generated point").

**Formalization Note** The paper leaves the polynomial overhead unspecified; the theorem is
quantified over every exponent `κ`, which covers every polynomial overhead. -/
noncomputable def runTime {m n : ℕ} (T : ℝ) (κ : ℕ) (r : RunResult m n) : ℝ :=
  T * r.evals + ((m * n + 1 : ℕ) : ℝ) ^ κ * r.work

end SmoothedNash


