-- Prove2me | Definitions.Def_DeBruijnNewman_Dobner_Mellin
-- name    : DeBruijnNewman_Dobner_Mellin
-- status  : Definition
-- author  : @adobner
-- created : 2026-09-24T22:33:00.725366+00:00
-- url     : https://prove2.me/theorems/c2f1d999-be39-45b8-86d7-22d52cbb63dd
-- title:
--   The individual Gaussian–Mellin coefficients in Dobner's proof
-- statement:
--   These definitions expose the individual coefficients from Dobner's contour argument. For $t<0$ and $N\geq1$, set
--
--   $$
--   B_{t,N}(s)=\frac{1}{\sqrt{\pi|t|}}
--   \int_{\mathbb R}\gamma(2+iv)
--   \exp\!\left(\frac{(J_t(s)-(2+iv))^2}{|t|}
--   -(2+iv)\log N\right)\,dv.
--   $$
--
--   This is equation (17) after parametrizing the upward vertical contour by $z=2+iv$: the factor $i$ in $dz=i\,dv$ cancels the contour prefactor $1/i$. Define also
--
--   $$
--   K_{t,N}(s)=\frac{B_{t,N}(s)}{\gamma_t(s)},\qquad
--   A_{t,N}(s)=\exp\!\left(\frac{t}{4}\log^2N-s\log N\right).
--   $$
--
--   The previously defined $J_t$, $\gamma$, and $\gamma_t$ are unchanged. In Lean, `mellinTerm t s n`, `normalizedMellinTerm t s n`, and `zetaTerm t s n` represent $B_{t,n+1}(s)$, $K_{t,n+1}(s)$, and $A_{t,n+1}(s)$ respectively. Thus the natural-number index zero represents the positive integer one. The definitions are total; analytic claims explicitly impose negative time and appropriate height conditions.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Section 4, equation (17), p. 15, and Lemma 4, p. 16; specialized to the Riemann zeta coefficients.

import Definitions.Def_DeBruijnNewman_Dobner

open MeasureTheory

namespace DeBruijnNewman.Dobner

/-- The Gaussian–Mellin coefficient `B_{t,n+1}(s)` from Dobner, Section 4.
The vertical line `Re z = 2` is parametrized by `z = 2 + i v`; its
Jacobian `i` cancels the `1/i` in the contour normalization. -/
noncomputable def mellinTerm (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
    ∫ v : ℝ, gammaFactor (2 + (v : ℂ) * Complex.I) *
      Complex.exp
        ((J t s - (2 + (v : ℂ) * Complex.I)) ^ 2 / ((|t| : ℝ) : ℂ)
          - (2 + (v : ℂ) * Complex.I) * (Real.log ((n : ℝ) + 1) : ℂ))

/-- The normalized individual Mellin coefficient. -/
noncomputable def normalizedMellinTerm (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  mellinTerm t s n / gammaT t s

/-- The `n+1` summand of the Gaussian-damped zeta Dirichlet series. -/
noncomputable def zetaTerm (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp
    (((t / 4 * Real.log ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ)
      - s * (Real.log ((n : ℝ) + 1) : ℂ))

end DeBruijnNewman.Dobner


