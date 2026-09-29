-- Prove2me | Definitions.Def_MetodosNumericos_zerosDefs
-- name    : MetodosNumericos_zerosDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:35:46.303538+00:00
-- url     : https://prove2.me/theorems/6c41321f-74e2-43f2-911d-dd087ce6da4d
-- title:
--   Bisection, fixed-point and Newton iterations
-- statement:
--   The four constructions used throughout Chapter 3. For a function $f$ and a starting interval $(a,b)$, the bisection construction produces the brackets $(a_n,b_n)$: at each step the midpoint $m=(a_n+b_n)/2$ replaces $a_n$ when $f(m)<0$ and replaces $b_n$ otherwise; its midpoint is the approximation $x_{n+1}=(a_n+b_n)/2$. For an iteration function $g$, the sequence $x_0$, $x_{n+1}=g(x_n)$ is the Método Iterativo Linear. For a function $f$ and a function $f'$ playing the role of its derivative, the Newton sequence is $x_{n+1}=x_n-f(x_n)/f'(x_n)$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 3: eq. (3.1) p. 39 (bissecção), §3.3 p. 45 (MIL), eq. (3.8) p. 59 (Newton).

import Mathlib

namespace MetodosNumericos

/-- One step of the bisection method (Método da Bissecção) for a function `f`
on a bracketing interval `p = (a, b)` with `f a < 0 < f b`:
the midpoint `m = (a + b) / 2` replaces the endpoint whose sign it matches. -/
noncomputable def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f ((p.1 + p.2) / 2) < 0 then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)

/-- The `n`-th bracketing interval `(aₙ, bₙ)` produced by the bisection method
started from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => bisectStep f (bisect f a b n)

/-- The bisection approximation `xₙ₊₁ = (aₙ + bₙ) / 2`, the midpoint of the
`n`-th bracketing interval. -/
noncomputable def bisectMid (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((bisect f a b n).1 + (bisect f a b n).2) / 2

/-- The successive-approximation sequence of the linear iterative method
(Método Iterativo Linear): `x₀` arbitrary and `xₙ₊₁ = g xₙ`. -/
noncomputable def iterSeq (g : ℝ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => g (iterSeq g x0 n)

/-- The Newton sequence: `x₀` arbitrary and `xₙ₊₁ = xₙ - f xₙ / f' xₙ`,
where `f'` is a function playing the role of the derivative of `f`. -/
noncomputable def newtonSeq (f f' : ℝ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => newtonSeq f f' x0 n - f (newtonSeq f f' x0 n) / f' (newtonSeq f f' x0 n)

end MetodosNumericos


