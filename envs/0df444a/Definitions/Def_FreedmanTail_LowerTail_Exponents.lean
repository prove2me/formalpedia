-- Prove2me | Definitions.Def_FreedmanTail_LowerTail_Exponents
-- name    : FreedmanTail_LowerTail_Exponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:32:39.329973+00:00
-- url     : https://prove2.me/theorems/76eaeec8-7fd6-43ff-8cfc-78f2f6232304
-- title:
--   Definition (1.2)(a)–(b) — e(λ) = e^λ − 1 − λ and f(λ) = e^{−λ} − 1 + λ
-- statement:
--   For a real number $\lambda$ define the two exponents
--
--   $$
--   e(\lambda)=e^{\lambda}-1-\lambda,\qquad f(\lambda)=e^{-\lambda}-1+\lambda .
--   $$
--
--   Both are nonnegative, vanish at $\lambda=0$, and behave like $\lambda^2/2$ for small $\lambda$. In Freedman's paper $e(\lambda)$ is the exponent of the exponential supermartingale that yields the upper (Bernstein-type) tail bound, and $f(\lambda)$ the exponent of the exponential submartingale that yields the matching lower bound; in this mission they appear in the Laplace-transform hypotheses (4.11a)–(4.11b).
--
--   **Formalization Note** Definition (1.2) says "$\lambda$ is a positive number"; the functions are defined here on all of $\mathbb R$, and every statement that uses them states its own range of $\lambda$ (here $\lambda\ge 0$, as in (4.10)).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 101 (PDF p. 2), (1.2) Definition (a)–(b)

import Mathlib

namespace FreedmanTail.LowerTail

/-- Freedman (1975), Definition (1.2)(a), p. 101: `e(λ) = e^λ − 1 − λ`. -/
noncomputable def e (lam : ℝ) : ℝ := Real.exp lam - 1 - lam

/-- Freedman (1975), Definition (1.2)(b), p. 101: `f(λ) = e^{−λ} − 1 + λ`. -/
noncomputable def f (lam : ℝ) : ℝ := Real.exp (-lam) - 1 + lam

end FreedmanTail.LowerTail


