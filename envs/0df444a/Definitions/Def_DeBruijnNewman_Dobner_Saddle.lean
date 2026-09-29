-- Prove2me | Definitions.Def_DeBruijnNewman_Dobner_Saddle
-- name    : DeBruijnNewman_Dobner_Saddle
-- status  : Definition
-- author  : @adobner
-- created : 2026-09-25T00:01:53.464507+00:00
-- url     : https://prove2.me/theorems/eb84b4c3-71a4-4343-aa42-49895dc291be
-- title:
--   The central saddle segment and gamma error for a fixed Mellin coefficient
-- statement:
--   For the existing Riemann gamma factor
--
--   $$
--   \gamma(s)=\frac{s(s-1)}2\pi^{-s/2}\Gamma(s/2),
--   $$
--
--   define the relative error after retaining the leading linear term by
--
--   $$
--   E(s,z)=\frac{\gamma(z)}
--    {\gamma(s)\exp\!\left(\frac12\operatorname{Log}
--          \left(\frac{s}{2\pi}\right)(z-s)\right)}-1.
--   $$
--
--   For real $t<0$, a positive integer $N$, and a point $s$ of height $y=\operatorname{Im}s$, put
--
--   $$
--   T=|t|,\qquad r(y)=y^{2/3},\qquad
--   z_{t,N,s}(u)=s+\frac{T\log N}{2}+iu.
--   $$
--
--   The central Gaussian–Mellin contribution is
--
--   $$
--   B^{\mathrm{cen}}_{t,N}(s)=
--   \frac1{\sqrt{\pi T}}\int_{-r(y)}^{r(y)}
--   \gamma(z_{t,N,s}(u))
--   \exp\!\left(\frac{(J_t(s)-z_{t,N,s}(u))^2}{T}
--                -z_{t,N,s}(u)\log N\right)\,du.
--   $$
--
--   Here $J_t(s)=s+(T/4)\operatorname{Log}(s/(2\pi))$ is the existing definition. The logarithm of a complex number is the principal logarithm. The segment is oriented upward; its contour Jacobian is included by cancellation with the usual $1/i$ prefactor.
--
--   **Formalization Note.** These quantities are `gammaLinearError`, `mellinWindow`, `mellinSaddlePoint`, and `centralMellinTerm`. The natural-number index $n$ represents $N=n+1$. The definitions are total; analytic theorems impose negative time and sufficiently large positive height. The center used here is the leading saddle $s+T\log N/2$, a fixed-index variant of the paper's corrected saddle $s+\log N/(2A)$ with $A=1/T+1/(4s)$.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Section 4, equation (17), p. 15, Lemma 5, p. 18, and the central-segment calculation in the proof of Lemma 4, pp. 19–20. Fixed-index leading-saddle variant of the paper's corrected saddle; the omitted quadratic gamma term is retained in the relative error.

import Definitions.Def_DeBruijnNewman_Dobner_Mellin

open MeasureTheory Set

namespace DeBruijnNewman.Dobner

/-- Relative error after retaining the leading linear term of `log gamma`.
The local estimate for this error is a separate theorem. -/
noncomputable def gammaLinearError (s z : ℂ) : ℂ :=
  gammaFactor z /
    (gammaFactor s * Complex.exp
      ((1 / 2 : ℂ) * Complex.log (s / ((2 * Real.pi : ℝ) : ℂ)) * (z - s))) - 1

/-- Height of the central segment in Dobner's contour argument. -/
noncomputable def mellinWindow (y : ℝ) : ℝ := y ^ (2 / 3 : ℝ)

/-- The leading saddle for a fixed coefficient, parametrized vertically.
Its real shift is `|t| log(n+1) / 2`. -/
noncomputable def mellinSaddlePoint (t : ℝ) (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  s + ((|t| / 2 * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I

/-- The contribution of the finite segment through the leading saddle.
The contour Jacobian cancels the factor `1/i` in the contour prefactor. -/
noncomputable def centralMellinTerm (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
    ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
      gammaFactor (mellinSaddlePoint t s n u) *
        Complex.exp
          ((J t s - mellinSaddlePoint t s n u) ^ 2 / ((|t| : ℝ) : ℂ) -
            mellinSaddlePoint t s n u * (Real.log ((n : ℝ) + 1) : ℂ))

end DeBruijnNewman.Dobner


