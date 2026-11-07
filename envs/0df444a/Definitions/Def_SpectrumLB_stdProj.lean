-- Prove2me | Definitions.Def_SpectrumLB_stdProj
-- name    : SpectrumLB_stdProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:41.807645+00:00
-- url     : https://prove2.me/theorems/17677c98-7de8-4fc2-a939-56289b94009a
-- title:
--   Reference rank-$r$ projection $R=\mathrm{diag}(1,\dots,1,0,\dots,0)$
-- statement:
--   The diagonal $d\times d$ matrix with $r$ leading ones,
--
--   $$
--   R=\mathrm{diag}(\underbrace{1,\dots,1}_{r},0,\dots,0),
--   $$
--
--   the coordinate projection onto the first $r$ basis vectors (the identity when $r\ge d$). Conjugating it by a Haar-random unitary gives a Haar-random rank-$r$ projection (Eq. (3.1)).
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §3, Eq. (3.1), p. 13

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Reference rank-`r` projection `R = diag(1, …, 1, 0, …, 0)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §3, Eq. (3.1), p. 13: "write R = diag(1, …, 1, 0, …) (r times)".

**Formalization Note.** For `r ≥ d` this is the identity. -/
def stdProj (d r : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

end SpectrumLB


