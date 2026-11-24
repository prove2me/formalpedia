-- Prove2me | Definitions.Def_AntihydraTwoOrder
-- name    : AntihydraTwoOrder
-- status  : Definition
-- author  : @sammas24
-- created : 2026-11-24T18:45:50.641162+00:00
-- url     : https://prove2.me/theorems/1465fdc1-9b73-4c49-b6ed-beb5accae11a
-- title:
--   Dyadic order for Antihydra odd-run budgets
-- statement:
--   For a positive natural number $m$, let $v_2(m)$ be the number of successive exact divisions by $2$ before an odd number is reached. The function `Antihydra.twoOrder` computes this number recursively, and assigns the value $0$ at $m=0$.
--
--   $$
--   v_2(m)=\begin{cases}0,&m=0\text{ or }m\text{ odd},\\v_2(m/2)+1,&m>0\text{ even}.\end{cases}
--   $$
--
--   For the Antihydra map $H(x)=\lfloor3x/2\rfloor$, the quantity $v_2(x-1)$ measures the length of the upcoming run of odd states when $x>1$. This definition supplies the arithmetic reserve used in an odd-run reduction of the counter conjecture.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean (BMO#2, beaver_math_olympiad_problem_2_antihydra, recurrence a(n+1)=floor(3a(n)/2) and counter recurrence). Original supporting derivation from these recurrences; the valuation lemmas are not stated verbatim in the source.

import Lean.Elab.Tactic.Omega

namespace Antihydra

/-- The exponent of 2 dividing a positive natural number; zero at 0. -/
def twoOrder (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then twoOrder (n / 2) + 1
  else 0
termination_by n
decreasing_by omega

end Antihydra


