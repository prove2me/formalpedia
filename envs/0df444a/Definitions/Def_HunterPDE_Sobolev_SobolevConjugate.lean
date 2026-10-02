-- Prove2me | Definitions.Def_HunterPDE_Sobolev_SobolevConjugate
-- name    : HunterPDE_Sobolev_SobolevConjugate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:28:02.707913+00:00
-- url     : https://prove2.me/theorems/6c387e19-3e4a-425f-868d-b6e9a6344461
-- title:
--   Definition 3.25 — the Sobolev conjugate p* = np/(n − p)
-- statement:
--   Let $n \in \mathbb{N}$ and $1 \le p < n$. The **Sobolev conjugate** of $p$ is
--   $$p^* = \frac{np}{n - p},$$
--   the unique exponent with $\dfrac{1}{p^*} = \dfrac{1}{p} - \dfrac{1}{n}$ (3.9). It is the only $q$ for which an estimate $\|f\|_{L^q} \le C\|Df\|_{L^p}$ can hold for all $f \in C_c^\infty(\mathbb{R}^n)$, by scaling.
--
--   **Formalization Note.** A real-valued function of $n$ and a real $p$; it is only used under the hypotheses $1 \le p < n$, where it is positive and larger than $p$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 60, Definition 3.25

import Mathlib

namespace HunterPDE.Sobolev

/-- Definition 3.25 of Hunter, *Notes on PDEs*, p. 60: for `1 ≤ p < n`, the Sobolev conjugate of
`p` is `p* = np / (n − p)`, the solution of `1/p* = 1/p − 1/n` (3.9). Only used for `1 ≤ p < n`. -/
noncomputable def sobolevConjugate (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * p / ((n : ℝ) - p)

end HunterPDE.Sobolev


