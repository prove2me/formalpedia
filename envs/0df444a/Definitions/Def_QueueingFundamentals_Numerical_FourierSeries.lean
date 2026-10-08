-- Prove2me | Definitions.Def_QueueingFundamentals_Numerical_FourierSeries
-- name    : QueueingFundamentals_Numerical_FourierSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T20:04:44.352739+00:00
-- url     : https://prove2.me/theorems/47313e22-9928-4b7b-ad42-fbd743b0e4aa
-- title:
--   The Laplace transform and the Fourier-series approximant $f_{A,n}(t)$
-- statement:
--   For a real function $f$ defined on $[0,\infty)$, its **Laplace transform** at a complex argument $s$ is
--
--   $$\bar f(s)=\int_0^\infty e^{-st} f(t)\,dt \qquad (8.15).$$
--
--   For parameters $A$ and $t>0$ and an integer $n\ge 0$, the **truncated Fourier-series approximant** of Eq. (8.25) is
--
--   $$f_{A,n}(t)=\frac{e^{A/2}}{2t}\left[\bar f\!\left(\frac{A}{2t}\right)+2\sum_{k=1}^{n}(-1)^k\,\mathrm{Re}\,\bar f\!\left(\frac{A+2k\pi i}{2t}\right)\right].$$
--
--   It is the trapezoidal-rule discretization of the real inversion integral (8.21) with step $h=\pi/(2t)$ and abscissa $b=A/(2t)$, truncated after $n$ terms. The infinite version $f_A(t)$ of (8.24) is the limit of $f_{A,n}(t)$ as $n\to\infty$; Algorithm 8.1 of the book computes Euler averages of these partial sums.
--
--   **Formalization Note** The integral is the Lebesgue (Bochner) integral over $(0,\infty)$; when $e^{-sx}f(x)$ is not integrable it takes the value $0$, so every theorem using this definition assumes a condition (boundedness of $f$ with $\mathrm{Re}\,s>0$) under which the integral converges. The book writes $\bar f(A/(2t))$ without a real part and remarks that it is real; the definition takes its real part, which is the same number whenever the integral converges.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.386 Eq. (8.15); p.390 Eqs. (8.24)–(8.25)

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_laplace

open Complex

namespace QueueingFundamentals.Numerical

/-- The truncated Fourier-series approximant `f_{A,n}(t)` of Eq. (8.25), p.390:
`f_{A,n}(t) = (e^{A/2}/(2t)) [ f̄(A/(2t)) + 2 ∑_{k=1}^{n} (−1)^k Re f̄((A + 2kπi)/(2t)) ]`.
The book writes `f̄(A/(2t))` for the first term and notes it is real; the real part is taken
here. The approximant `f_A(t)` of (8.24) is the limit of `f_{A,n}(t)` as `n → ∞`. -/
noncomputable def fourierApprox (f : ℝ → ℝ) (A t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (A / 2) / (2 * t) *
    ((QueueingFundamentals.Transient.laplace f ((A / (2 * t) : ℝ) : ℂ)).re +
      2 * ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k * (QueueingFundamentals.Transient.laplace f (((A : ℂ) + 2 * (k : ℂ) * (Real.pi : ℂ) * I) / (2 * (t : ℂ)))).re)

end QueueingFundamentals.Numerical


