-- Prove2me | Definitions.Def_SpectrumLB_tiltedHaar
-- name    : SpectrumLB_tiltedHaar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:32.736203+00:00
-- url     : https://prove2.me/theorems/9b49d72a-5745-4f32-bb41-fa41332fc21c
-- title:
--   Definition 5.4 — the $n$-tilted law $\widetilde{\mathrm{PRP}}^{(n)}_d(a)$
-- statement:
--   Fix $n\in\mathbb N$ and let $X\sim\mathrm{PRP}_d(a)$. The tilted law is the probability measure whose density with respect to the law of $X$ is
--
--   $$
--   \frac{\mathrm{Tr}(X)^n}{\mathbf E[\mathrm{Tr}(X)^n]} .
--   $$
--
--   A draw $\widetilde X$ from it is normalized to the random state $\rho=\widetilde X/\mathrm{Tr}\,\widetilde X$. The tilt is chosen so that the average $n$-copy state is proportional to $\mathbf E[X^{\otimes n}]$, which Proposition 3.5 computes exactly.
--
--   **Formalization Note** The measure is placed on the underlying unitaries $(U_1,\dots,U_K)$, with the same density against the product Haar measure. $\mathrm{Tr}\,X\ge0$ is real; its real part is used. The normalizer is at least $(d\nu_a)^n>0$.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 5.4, p. 21

import Mathlib
import Definitions.Def_SpectrumLB_haarK
import Definitions.Def_SpectrumLB_prpMatrix

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **The `n`-tilted law `PRP~^{(n)}_d(a)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 5.4, p. 21: "X~ is drawn from the tilted distribution whose density with respect to X is
Tr(X)^n / E[Tr(X)^n]".

`tiltedHaar d n a` is the measure on the unitaries with density `Tr(X)^n / E[Tr(X)^n]` against `haarK d K`,
`X = prpMatrix a U`; the tilted matrix `X~` is `prpMatrix a U` under this measure.

**Formalization Note.** `Tr X` is real and `≥ 0` (X is PSD); its real part is used. The normalizer is
`≥ (d ν_a)^n > 0` (Jensen and (3.10)), so this is a probability measure and no division-by-zero junk arises. -/
noncomputable def tiltedHaar (d n : ℕ) {K : ℕ} (a : Fin K → ℕ) :
    Measure (Fin K → Matrix.unitaryGroup (Fin d) ℂ) :=
  (haarK d K).withDensity fun U =>
    ENNReal.ofReal ((prpMatrix a U).trace.re ^ n / ∫ V, (prpMatrix a V).trace.re ^ n ∂haarK d K)

end SpectrumLB


