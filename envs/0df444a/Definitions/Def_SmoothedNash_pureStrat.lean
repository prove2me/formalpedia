-- Prove2me | Definitions.Def_SmoothedNash_pureStrat
-- name    : SmoothedNash_pureStrat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:42.075394+00:00
-- url     : https://prove2.me/theorems/2df92254-ab89-4e1d-8023-01ee7468d786
-- title:
--   Pure strategy $e_a$ as a mixed strategy
-- statement:
--   For an action $a \in [n]$, the **pure strategy** $e_a$ is the point mass on $a$:
--   $$
--   e_a(b) = \begin{cases} 1 & b = a, \\ 0 & b \ne a. \end{cases}
--   $$
--   It is the mixed strategy of a player who plays $a$ with probability one, and it is used to write the deviation payoffs $u_i(a, x_{-i})$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §1.1.2, p.6

import Mathlib

namespace SmoothedNash

/-- The pure strategy on action `a`, as a mixed strategy: the point mass `e_a` on `[n]`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §1.1.2, p.6, used in `u_i(a, x_{-i})`). -/
def pureStrat {n : ℕ} (a : Fin n) : Fin n → ℝ := fun b => if b = a then 1 else 0

end SmoothedNash


