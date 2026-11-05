-- Prove2me | Definitions.Def_ZhangCFL_trAbsPow
-- name    : ZhangCFL_trAbsPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:20.555168+00:00
-- url     : https://prove2.me/theorems/fa664b81-06fc-4511-992d-bd5458c86855
-- title:
--   Trace of a power of the modulus $\operatorname{Tr}|X|^r$
-- statement:
--   For a square complex matrix $X$ write $|X|=(X^*X)^{1/2}$ for its modulus. For a real number $r$, set
--
--   $$
--   \operatorname{Tr}|X|^r = \operatorname{Tr}\,(X^*X)^{r/2} .
--   $$
--
--   For $r>0$ this is $\|X\|_r^r$, the $r$-th power of the Schatten $r$-(quasi)norm, which is the notation of the proof of Theorem 3.3. It is the quantity in which the paper's variational formulas (3.1) and (3.2) are written.
--
--   **Formalization Note** The power is taken of the positive semidefinite matrix $X^*X$ with `OgawaNagaoka.matPow`; for $r>0$, and for every real $r$ when $X$ is invertible, this agrees with $\operatorname{Tr}\big((X^*X)^{1/2}\big)^r$. The value is the real part of the trace.
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, p.4 (modulus |A| = (A*A)^{1/2}) and proof of Theorem 3.3, p.8 (‖A‖_p^p := Tr|A|^p)

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

namespace ZhangCFL

open OgawaNagaoka

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, p.4 (the modulus `|A| = (A*A)^{1/2}`) and proof of Theorem 3.3, p.8
(`‖A‖_p^p := Tr|A|^p`): the trace of a power of the modulus, `Tr|X|^r = Tr (X* X)^{r/2}`.

**Formalization Note.** Computed as `Tr (X* X)^{r/2}` with `OgawaNagaoka.matPow`
(`cfc` with `Real.rpow`) applied to the positive semidefinite matrix `X* X`, which equals
`Tr ((X* X)^{1/2})^r` for every `r > 0` and, for invertible `X`, for every real `r`. The value is
the real part of the trace (the trace of a positive semidefinite matrix is real). -/
noncomputable def trAbsPow {n : Type} [Fintype n] [DecidableEq n] (r : ℝ)
    (X : Matrix n n ℂ) : ℝ :=
  (matPow (X.conjTranspose * X) (r / 2)).trace.re

end ZhangCFL


