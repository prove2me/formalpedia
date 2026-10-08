-- Prove2me | Definitions.Def_FreedmanTail_Bernstein_Exponents
-- name    : FreedmanTail_Bernstein_Exponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:31:36.45707+00:00
-- url     : https://prove2.me/theorems/cf34a015-ec5e-4974-b204-d74f5ab133ea
-- title:
--   Definition (1.2)(a), (d) — e(λ) = e^λ − 1 − λ and Q_λ(v, y) = exp{λy − e(λ)v}
-- statement:
--   This file fixes the two deterministic functions of Freedman's Definition (1.2) that drive the upper tail bounds.
--
--   1. For a real number $\lambda$,
--   $$e(\lambda)=e^{\lambda}-1-\lambda .$$
--   It is nonnegative and vanishes only at $\lambda=0$.
--   2. For real numbers $\lambda$, $v$ and $y$,
--   $$Q_\lambda(v,y)=\exp\{\lambda y-e(\lambda)\,v\}.$$
--   The first argument $v$ plays the role of time (it will be the accumulated conditional variance $T_n$), the second argument $y$ the role of position (the partial sum $S_n$), so that $Q_\lambda(T_n,S_n)=\exp\{\lambda S_n-e(\lambda)T_n\}$.
--
--   The process $Q_\lambda(T_n,S_n)$ is the exponential supermartingale behind every upper bound of the paper; $e(\lambda)$ is the compensator that makes it decrease in expectation when the increments are bounded above by $1$.
--
--   **Formalization Note** Definition (1.2) introduces $\lambda$ as "a positive number"; the functions are defined for every real $\lambda$, and each theorem states the range of $\lambda$ its own page uses ($\lambda\ge0$ in §3).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 101 (PDF p. 2), (1.2) Definition (a), (d)

import Mathlib

namespace FreedmanTail.Bernstein

/-- Freedman (1975), Definition (1.2)(a), p. 101: `e(λ) = e^λ − 1 − λ`. -/
noncomputable def e (lam : ℝ) : ℝ := Real.exp lam - 1 - lam

/-- Freedman (1975), Definition (1.2)(d), p. 101: `Q_λ(v, y) = exp{λy − e(λ)v}`.
The time variable `v` comes first, the space variable `y` second. -/
noncomputable def Q (lam v y : ℝ) : ℝ := Real.exp (lam * y - e lam * v)

end FreedmanTail.Bernstein


