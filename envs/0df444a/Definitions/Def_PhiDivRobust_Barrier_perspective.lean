-- Prove2me | Definitions.Def_PhiDivRobust_Barrier_perspective
-- name    : PhiDivRobust_Barrier_perspective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:53:27.973367+00:00
-- url     : https://prove2.me/theorems/9f430323-d3b1-4c3d-8a4a-304fb343fc6c
-- title:
--   The perspective g(s, y) = y f(s/y)
-- statement:
--   For a function $f:\mathbb R\to\mathbb R$, its **perspective** is the function of two variables
--
--   $$g(s,y)\;=\;y\,f\!\left(\frac{s}{y}\right),$$
--
--   used on the open quadrant $s>0$, $y>0$. The first variable is $s$, the second is $y$; direction vectors $h=(h_1,h_2)$ are taken with $h_1$ along $s$ and $h_2$ along $y$.
--
--   In the robust counterparts of Ben-Tal et al. (2013), constraints of the form $\lambda f(s_i/\lambda)\le\dots$ (Eqs. (29) and (32)) are perspective constraints, and the self-concordance of their logarithmic barrier rests on bounds for the second and third differentials of $g$.
--
--   **Formalization Note** The function is total on $\mathbb R\times\mathbb R$ (Lean's $s/0=0$ gives $g(s,0)=0$); every statement of the mission evaluates it or its differentials only at points with $s>0$, $y>0$, where it agrees with the paper's $g$ on a neighbourhood.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, proof of Theorem 2, first sentence

import Mathlib

namespace PhiDivRobust.Barrier

/-- The perspective `g(s, y) = y f(s / y)` of `f : ℝ → ℝ` (proof of Theorem 2, Ben-Tal et al. 2013,
p. 350). The first coordinate is `s`, the second is `y`. -/
noncomputable def perspective (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 * f (p.1 / p.2)

end PhiDivRobust.Barrier


