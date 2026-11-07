-- Prove2me | Definitions.Def_SpectrumLB_haarK
-- name    : SpectrumLB_haarK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:40.637113+00:00
-- url     : https://prove2.me/theorems/792aa927-3f40-4ede-9975-006fe90a1f79
-- title:
--   $K$ independent Haar-random unitaries on $U(d)$
-- statement:
--   The product probability measure on $U(d)^K$ whose factors are the Haar probability measure of the unitary group $U(d)$: the law of $K$ independent Haar-random unitaries $U_1,\dots,U_K$. It is the source of randomness of the product-of-random-projections ensemble (Definition 3.4) and the measure in the concentration inequality (7.14).
--
--   **Formalization Note** The factor is the platform's `QAlgorithms.Schur.unitaryHaar d`, the Haar probability measure on the compact group $U(d)$ with its Borel σ-algebra.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 3.4, p. 14; §7.2, p. 36

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **`K` independent Haar-random unitaries.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 3.4, p. 14 ("drawn independently for i = 1 … K") and §7.2, p. 36 ("K Haar-random unitaries
U_1, …, U_K").

`haarK d K` is the product of `K` copies of the Haar probability measure on `U(d)`.

**Formalization Note.** The factor is the platform's `QAlgorithms.Schur.unitaryHaar d` (Haar probability on
the compact group with its Borel σ-algebra); the proof term only supplies its σ-finiteness to `Measure.pi`. -/
noncomputable def haarK (d K : ℕ) : Measure (Fin K → Matrix.unitaryGroup (Fin d) ℂ) :=
  haveI : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
    ⟨QAlgorithms.Schur.unitaryHaar.eq_1 d ▸ Measure.haarMeasure_self⟩
  Measure.pi fun _ : Fin K => QAlgorithms.Schur.unitaryHaar d

end SpectrumLB


