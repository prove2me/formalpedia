-- Prove2me | Definitions.Def_WildeQIT_hsNorm
-- name    : WildeQIT_hsNorm
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:48:11.630752+00:00
-- url     : https://prove2.me/theorems/815248f1-79a5-4df4-b283-8f8459da7e11
-- title:
--   Hilbert–Schmidt norm $\|X\|_2 = \sqrt{\mathrm{Tr}\{X^\dagger X\}}$
-- statement:
--   **Hilbert–Schmidt norm (Wilde §9.6).** The Hilbert–Schmidt norm of an operator $X$ is
--
--   $$
--   \|X\|_2 \equiv \sqrt{\mathrm{Tr}\{X^\dagger X\}} ,
--   $$
--
--   and the Hilbert–Schmidt distance between $X$ and $Y$ is $\|X - Y\|_2$. Section 9.6 shows it is dominated by the trace norm up to the rank (Exercise 9.6.1) but is not monotone under channels (Exercise 9.6.2), so it is not a valid distinguishability measure.
--
--   **Formalization Note.** `WildeQIT.hsNorm X := Real.sqrt (Matrix.trace (Xᴴ * X)).re` for `X : Matrix m n ℂ`.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.6 "The Hilbert–Schmidt Distance Measure", eq. defining $\|X\|_2$.

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.6 (The Hilbert–Schmidt Distance Measure).

The Hilbert–Schmidt norm of an operator `X` is `‖X‖₂ ≡ √(Tr{X†X})`, and the Hilbert–Schmidt
distance between two operators is `‖X − Y‖₂`.
-/

open Matrix

namespace WildeQIT

/-- **Hilbert–Schmidt (Frobenius) norm** `‖X‖₂ = √(Tr{X†X})` of `X : Matrix m n ℂ`. -/
noncomputable def hsNorm {m n : Type} [Fintype m] [Fintype n] (X : Matrix m n ℂ) : ℝ :=
  Real.sqrt (Matrix.trace (Xᴴ * X)).re

end WildeQIT


