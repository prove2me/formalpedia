-- Prove2me | Definitions.Def_SpectrumLB_ntCycles
-- name    : SpectrumLB_ntCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:23.448352+00:00
-- url     : https://prove2.me/theorems/e72063e5-72e1-48a5-9b8f-36380691e5c2
-- title:
--   Number of non-trivial cycles $c(\mu)$
-- statement:
--   For $\pi\in S_n$, $c(\pi)$ is the number of cycles of $\pi$ of length at least $2$, the length of its non-fixed cycle type. It is constant on conjugacy classes; the paper writes $c(\mu)$ for a class $\mu$ (§6.1). It enters the exponent $\delta(\mu)$ of Lemma 6.6 and the bounds of Lemma 6.7.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §6.1, p. 27

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Number of non-trivial cycles `c(μ)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §6.1, p. 27: "all permutations in C_μ have the same support size, number of non-trivial cycles, and
Cayley length; we will thus denote the first two by s(μ) and c(μ)".

`ntCycles π` is the number of cycles of `π` of length `≥ 2` (the length of its non-fixed cycle type). -/
def ntCycles {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  π.cycleType.card

end SpectrumLB


