-- Prove2me | Definitions.Def_Gelbart_hecke_series
-- name    : Gelbart_hecke_series
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T03:30:21.845985+00:00
-- url     : https://prove2.me/theorems/bc78ab4a-6226-40c7-9d96-752dbf514349
-- title:
--   Hecke data: growth condition, $f(z)$ and $\Phi(s)$
-- statement:
--   The three basic objects of Hecke's theory, for a coefficient sequence $a_0, a_1, \dots$ of complex numbers and a period $h > 0$.
--
--   1. **Growth condition.** $a$ has *growth exponent* $c$ when there is a constant $K$ with $\lVert a_n \rVert \le K n^{c}$ for every $n \ge 1$; this is Gelbart's $a_n = O(n^c)$ (§II.B.2, p. 188). The coefficient $a_0$ is unconstrained.
--
--   2. **The form.** $$f(z) = \sum_{n \ge 0} a_n e^{2\pi i n z/h},$$ summed unconditionally; where the family is not summable the value is $0$ by convention, so all assertions about $f$ are restricted to the upper half-plane.
--
--   3. **The completed Dirichlet series.** $$\Phi(s) = \left(\frac{2\pi}{h}\right)^{-s}\Gamma(s)\,\varphi(s), \qquad \varphi(s) = \sum_{n \ge 1} \frac{a_n}{n^{s}},$$ where $\varphi$ is Mathlib's `LSeries`, whose $n = 0$ term is $0$, and the complex powers are principal-branch.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, pp. 187-188, §II.B.2

import Mathlib

namespace Gelbart

/-- Hecke's growth hypothesis on the coefficient sequence: `a n = O (n ^ c)`. -/
def HeckeCoeffGrowth (a : ℕ → ℂ) (c : ℝ) : Prop :=
  ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ K * (n : ℝ) ^ c

/-- The function attached to the coefficients `a` and the period `h`:
`f (z) = ∑_{n ≥ 0} aₙ exp (2πinz/h)`, defined by its `tsum`, so it carries the junk
value `0` off the region of convergence. -/
noncomputable def heckeForm (a : ℕ → ℂ) (h : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * Complex.exp (2 * Real.pi * Complex.I * n * z / h)

/-- The completed Dirichlet series `Φ (s) = (2π/h)^{-s} Γ(s) φ(s)`, where
`φ (s) = ∑_{n ≥ 1} aₙ n^{-s}` is Mathlib's `LSeries a s` (whose `n = 0` term is `0`). -/
noncomputable def heckeCompletedLSeries (a : ℕ → ℂ) (h : ℝ) (s : ℂ) : ℂ :=
  (2 * Real.pi / h : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s

end Gelbart


