-- Prove2me | Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
-- name    : HunterPDE_Newtonian_FundamentalSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:10:26.894235+00:00
-- url     : https://prove2.me/theorems/79fca4fc-489f-439e-9175-91c9526c4f2d
-- title:
--   Eq. (2.12) — the fundamental solution Γ of Laplace's equation on ℝⁿ, n ≥ 2
-- statement:
--   Let $n \ge 2$ and let $\alpha_n$ denote the Lebesgue measure of the open unit ball of $\mathbb{R}^n$. The **fundamental solution** (free-space Green's function) of Laplace's equation is the function $\Gamma : \mathbb{R}^n \setminus \{0\} \to \mathbb{R}$ given by
--   $$\Gamma(x) = \frac{1}{n(n-2)\alpha_n}\,\frac{1}{|x|^{n-2}} \quad (n \ge 3), \qquad \Gamma(x) = -\frac{1}{2\pi}\log|x| \quad (n = 2).$$
--   With this sign convention (Evans', the opposite of Gilbarg–Trudinger's) $\Gamma$ is harmonic away from the origin and $-\Delta\Gamma = \delta$ in the sense of distributions. It is the kernel of the Newtonian potential.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`, and $\alpha_n$ is `unitBallVolume n`, the real value of the volume of `Metric.ball 0 1`. The book leaves $\Gamma(0)$ undefined; in Lean $1/0 = 0$ and $\log 0 = 0$ give $\Gamma(0) = 0$, a single point of measure zero. The values for $n = 0, 1$ are junk; every theorem assumes $2 \le n$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 33, Eq. (2.12)

import Mathlib

namespace HunterPDE.Newtonian

open MeasureTheory

/-- `αₙ`, the Lebesgue measure of the open unit ball of `ℝⁿ = EuclideanSpace ℝ (Fin n)`
(Hunter, *Notes on PDEs*, Ch. 1, used in (2.12)). -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- The fundamental solution `Γ : ℝⁿ → ℝ` of Laplace's equation, (2.12) of Hunter, *Notes on
PDEs* (p. 33):
`Γ(x) = 1 / (n(n−2)αₙ) · 1/|x|^{n−2}` if `n ≥ 3`, and `Γ(x) = −(1/2π) log |x|` if `n = 2`.
The book uses it only for `n ≥ 2`; every theorem about it assumes `2 ≤ n`, and the values for
`n = 0, 1` are junk. At `x = 0` Lean's conventions `1/0 = 0` and `Real.log 0 = 0` give
`Γ(0) = 0`, a single point of Lebesgue measure zero, where the book leaves `Γ` undefined. The
sign convention is the book's (and Evans'): `−ΔΓ = δ`. -/
noncomputable def fundamentalSolution (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n = 2 then -(1 / (2 * Real.pi)) * Real.log ‖x‖
  else 1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n) * (1 / ‖x‖ ^ (n - 2))

end HunterPDE.Newtonian


