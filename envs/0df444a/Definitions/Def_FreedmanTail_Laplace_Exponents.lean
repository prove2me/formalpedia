-- Prove2me | Definitions.Def_FreedmanTail_Laplace_Exponents
-- name    : FreedmanTail_Laplace_Exponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:34.558633+00:00
-- url     : https://prove2.me/theorems/a8ac7184-46e7-4559-8076-2661126885bb
-- title:
--   Definition (1.2)(b),(e) — f(λ) = e^{−λ} − 1 + λ and R_λ(v, y) = exp{λy − f(λ)v}
-- statement:
--   For a real number $\lambda$ define
--   $$
--   f(\lambda) = e^{-\lambda} - 1 + \lambda ,
--   $$
--   and for real $v$ (a "time" variable, in practice an accumulated conditional variance) and real $y$ (a "space" variable, in practice a partial sum) define
--   $$
--   R_\lambda(v, y) = \exp\{\lambda y - f(\lambda) v\} .
--   $$
--   The function $f$ is nonnegative and vanishes only at $\lambda = 0$. Freedman shows that $R_\lambda(T_n, S_n)$, evaluated along a martingale with increments bounded by $1$ in absolute value, is a submartingale; this is the source of all lower bounds on the Laplace transform of the crossing variance $W_a$.
--
--   **Formalization Note** The paper's Definition (1.2) says "$\lambda$ is a positive number"; the Lean functions are defined for every real $\lambda$, and each theorem states the range of $\lambda$ its page uses. The paper prints (1.2)(e) as $R_\lambda(v,y) = \exp\{\lambda h - f(\lambda) v\}$; the letter $h$ is a misprint for $y$ (compare Lemma (1.3)(d) and Proposition (3.6), where $R_\lambda$ is evaluated at $(T_\sigma, S_\sigma)$), and the definition uses $y$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 101 (PDF p. 2), (1.2) Definition (b), (e)

import Mathlib

namespace FreedmanTail.Laplace

/-- Freedman (1975), Definition (1.2)(b), p. 101: `f(λ) = e^{−λ} − 1 + λ`. -/
noncomputable def f (lam : ℝ) : ℝ := Real.exp (-lam) - 1 + lam

/-- Freedman (1975), Definition (1.2)(e), p. 101: `R_λ(v, y) = exp{λy − f(λ)v}`.
The page prints `exp{λh − f(λ)v}`; `h` is a misprint for `y` (compare (1.3)(d) and (3.6)).
The time variable `v` comes first, the space variable `y` second. -/
noncomputable def R (lam v y : ℝ) : ℝ := Real.exp (lam * y - f lam * v)

end FreedmanTail.Laplace


