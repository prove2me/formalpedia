-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_circleMeanE
-- name    : LeblSCV_Pseudoconvex_circleMeanE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:51:25.865996+00:00
-- url     : https://prove2.me/theorems/7dc2e1dd-4730-428c-a016-247c1921810e
-- title:
--   Circle mean $\frac{1}{2\pi}\int_0^{2\pi} f(a+re^{i\theta})\,d\theta$ of an $\mathbb{R}\cup\{-\infty\}$-valued function
-- statement:
--   For $f : \mathbb{C} \to [-\infty, \infty]$, $a \in \mathbb{C}$ and $r \in \mathbb{R}$, the **circle mean** is the Lebesgue integral
--   $$\frac{1}{2\pi} \int_0^{2\pi} f(a + r e^{i\theta}) \, d\theta = \frac{1}{2\pi}\left( \int_0^{2\pi} f^+(a + re^{i\theta})\,d\theta - \int_0^{2\pi} f^-(a + re^{i\theta})\,d\theta \right),$$
--   where $f^+ = \max(f, 0)$, $f^- = \max(-f, 0)$, and both integrals are taken in $[0, \infty]$.
--
--   The circle mean is the right-hand side of the sub-mean-value property (Proposition 2.4.3 (ii)). The book notes that integrating an upper-semicontinuous function needs the Lebesgue integral. For such an $f$ near the circle, $f^+$ is bounded, so the mean lies in $[-\infty, \infty)$. It equals $-\infty$ exactly when $f^-$ has infinite integral.
--
--   **Formalization Note.** Both parts are lower Lebesgue integrals (`lintegral`) over $(0, 2\pi]$ of `EReal.toENNReal`, and the difference is taken in `EReal`. The value is the book's integral whenever $\int f^+ < \infty$, which holds under the hypotheses where the mean is used. A sanity check in the workspace shows that the mean of a positive constant $c$ is $c$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 81, Proposition 2.4.3 (ii) and the remark following it

import Mathlib

open scoped ENNReal

namespace LeblSCV.Pseudoconvex

/-- The circle mean `(1/2π) ∫₀^{2π} f(a + r e^{iθ}) dθ` of an extended-real-valued
`f : ℂ → ℝ ∪ {−∞}` (Lebl, p. 81, Proposition 2.4.3 (ii)), as a Lebesgue integral: the integral
of the positive part minus the integral of the negative part, both as lower Lebesgue integrals
in `[0, ∞]`. For an upper-semicontinuous `f` on a neighbourhood of the circle the positive part
is bounded, so the value lies in `[−∞, ∞)`, and it is `−∞` exactly when the negative part has
infinite integral. `circleMap a r θ = a + r e^{iθ}`. -/
noncomputable def circleMeanE (f : ℂ → EReal) (a : ℂ) (r : ℝ) : EReal :=
  (((2 * Real.pi)⁻¹ : ℝ) : EReal) *
    (((∫⁻ θ in Set.Ioc 0 (2 * Real.pi), (f (circleMap a r θ)).toENNReal : ℝ≥0∞) : EReal) -
      ((∫⁻ θ in Set.Ioc 0 (2 * Real.pi), (-(f (circleMap a r θ))).toENNReal : ℝ≥0∞) : EReal))

end LeblSCV.Pseudoconvex


