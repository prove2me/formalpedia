-- Prove2me | Definitions.Def_SpectrumLB_fA
-- name    : SpectrumLB_fA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:27.574203+00:00
-- url     : https://prove2.me/theorems/db3beaa8-f61f-40ca-a231-9b5d8be57c9e
-- title:
--   Rational function $f_a(z)=\prod_i(1+a_iz)/(1+z)$, Eq. (3.11)
-- statement:
--   For positive integers $a_1,\dots,a_K$ and real $z$,
--
--   $$
--   f_a(z)=\prod_{i=1}^K\frac{1+a_iz}{1+z}.
--   $$
--
--   The $n$-fold moments of $\mathrm{PRP}_d(a)$ are products of $f_a$ evaluated at the normalized Jucys–Murphy elements (Proposition 3.5), so comparing two ensembles $a,b$ reduces to comparing $f_a$ and $f_b$ near $0$ (Proposition 5.3).
--
--   **Formalization Note** The variable is real; the paper evaluates $f_a$ only at real numbers or Hermitian operators.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Proposition 3.5, Eq. (3.11), p. 14

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **The rational function `f_a(z) = ∏_i (1 + a_i z)/(1 + z)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Proposition 3.5, Eq. (3.11), p. 14.

**Formalization Note.** Real variable `z` (paper.md reading R6): every use evaluates `f_a` at real numbers
or, through `fAOp`, at the Hermitian operators `J̃_t`. -/
noncomputable def fA {K : ℕ} (a : Fin K → ℕ) (z : ℝ) : ℝ :=
  ∏ i, (1 + (a i : ℝ) * z) / (1 + z)

end SpectrumLB


