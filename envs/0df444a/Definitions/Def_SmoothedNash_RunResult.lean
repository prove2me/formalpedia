-- Prove2me | Definitions.Def_SmoothedNash_RunResult
-- name    : SmoothedNash_RunResult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:44.104531+00:00
-- url     : https://prove2.me/theorems/094e3ac4-865d-444a-aa11-46f90552a464
-- title:
--   Outcome of a run of Algorithm 2
-- statement:
--   The outcome of (a part of) a run of Algorithm 2 consists of
--   1. the returned profile, or **Fail** when no profile is returned;
--   2. the number of computations of the deviation payoff vector $U(c)$ (executions of line 10);
--   3. the number of work units of the cost model of the running-time clause (enumeration of grid points and children, and checking the test).
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2, p.15, and proof of Theorem 2.2, p.19

import Mathlib

namespace SmoothedNash

/-- The outcome of (a prefix of) a run of Algorithm 2 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.15): the returned profile (`none` is
`Fail`), the number of payoff-vector computations (executions of line 10), and the enumeration and
test work of the cost model of `supportRun`. -/
structure RunResult (m n : ℕ) where
  /-- the returned profile, `none` for `Fail` -/
  out : Option (Fin m → Fin n → ℝ)
  /-- the number of computations of `U(c)` (line 10) -/
  evals : ℕ
  /-- the work units of the cost model (`supportRun`) -/
  work : ℕ

end SmoothedNash


