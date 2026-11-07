-- Prove2me | Definitions.Def_SpectrumLB_nuA
-- name    : SpectrumLB_nuA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:37.431215+00:00
-- url     : https://prove2.me/theorems/4f2067db-64e6-4e13-b910-597c0688ea09
-- title:
--   $\nu_a=1/(a_1a_2\cdots a_K)$, Eq. (3.10)
-- statement:
--   For positive integers $a_1,\dots,a_K$,
--
--   $$
--   \nu_a=\frac1{a_1a_2\cdots a_K}.
--   $$
--
--   It is the mean of the product of random projections, $\mathbf E[X]=\nu_a\mathbf 1$ for $X\sim\mathrm{PRP}_d(a)$, and the scale of its $n$-fold tensor moments (Proposition 3.5).
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 3.4, Eq. (3.10), p. 14

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **`ν_a = 1/(a_1 a_2 ⋯ a_K)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 3.4, Eq. (3.10), p. 14: "E[X] = ν_a · 1, ν_a := 1/(a_1 a_2 ⋯ a_K)". -/
noncomputable def nuA {K : ℕ} (a : Fin K → ℕ) : ℝ :=
  1 / ∏ i, (a i : ℝ)

end SpectrumLB


