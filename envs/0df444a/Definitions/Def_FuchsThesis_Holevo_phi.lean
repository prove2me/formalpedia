-- Prove2me | Definitions.Def_FuchsThesis_Holevo_phi
-- name    : FuchsThesis_Holevo_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:28.112334+00:00
-- url     : https://prove2.me/theorems/63d55f2e-c9dd-4934-917b-4ab4ce0e184f
-- title:
--   The function $\Phi(x,y)$, reciprocal of the logarithmic mean
-- statement:
--   For positive reals $x,y$,
--
--   $$
--   \Phi(x,y) = \frac{\ln x-\ln y}{x-y}\quad (x\ne y), \qquad \Phi(x,x)=\frac1x .
--   $$
--
--   $1/\Phi(x,y)$ is the logarithmic mean of $x$ and $y$. $\Phi$ gives the second derivative of the von Neumann entropy along a line of states, (3.160).
--
--   **Formalization Note** The source defines $\Phi$ by a contour integral, (3.161), and evaluates it by Cauchy's integral theorem to (3.162)–(3.163); the definition here is that closed form. For non-positive arguments Lean's conventions ($\ln0=0$, $1/0=0$) give finite junk values; the theorems use $\Phi$ only where such arguments do not matter (see their notes).
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.162)–(3.163), p.67 (PDF p.76)

import Mathlib

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.162)–(3.163), p.67 (PDF p.76): the function
`Φ(x, y) = (ln x − ln y)/(x − y)` if `x ≠ y`, and `Φ(x, x) = 1/x`; the reciprocal of the
logarithmic mean of `x` and `y` (p.71).

**Formalization Note.** The source introduces `Φ` by the contour integral (3.161) and evaluates
it by Cauchy's integral theorem in (3.162)–(3.163); the definition here is the evaluated closed
form. `Φ` is meaningful for `x, y > 0`; on other inputs Lean's conventions give junk values
(`Real.log 0 = 0`, `1/0 = 0`). -/
noncomputable def phi (x y : ℝ) : ℝ :=
  if x = y then 1 / x else (Real.log x - Real.log y) / (x - y)

end FuchsThesis.Holevo


