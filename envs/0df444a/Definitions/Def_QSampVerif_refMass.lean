-- Prove2me | Definitions.Def_QSampVerif_refMass
-- name    : QSampVerif_refMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:06.245778+00:00
-- url     : https://prove2.me/theorems/b861d666-9aee-4af3-9ff1-3a139d8f5621
-- title:
--   The reference mass $\mu(A)=\mathrm{Tr}(A\Omega A^\dagger)$
-- statement:
--   For an operator $A$ and a reference operator $\Omega$ on its input space, the **reference mass** is
--
--   $$\mu(A)=\mathrm{Tr}(A\,\Omega\,A^\dagger).$$
--
--   **Formalization Note** It is taken as the real part of the trace; for positive semidefinite $\Omega$ the trace is real and nonnegative, so nothing is lost.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), p.175 and p.178 (PDF 176, 179)

import Mathlib

set_option autoImplicit false

namespace QSampVerif

open scoped Matrix

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), p.175
and p.178 (PDF 176, 179): the reference mass `µ(A) = Tr(A Ω A†)` of an operator `A` with respect
to the reference operator `Ω`.

**Formalization Note.** `µ(A)` is the real part of the trace; for positive semidefinite `Ω` the
trace is real and nonnegative, so nothing is lost. -/
noncomputable def refMass {ι κ : Type*} [Fintype ι] [Fintype κ] (Ω : Matrix ι ι ℂ)
    (A : Matrix κ ι ℂ) : ℝ :=
  (Matrix.trace (A * Ω * Aᴴ)).re

end QSampVerif


