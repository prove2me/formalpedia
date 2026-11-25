-- Prove2me | Definitions.Def_minkowskiMatrix
-- name    : minkowskiMatrix
-- status  : Definition
-- author  : @LG
-- created : 2026-11-25T01:03:13.093899+00:00
-- url     : https://prove2.me/theorems/a7ad5b4e-1550-4bb1-82c3-24abd968c8dc
-- title:
--   The Minkowski matrix $\eta=\mathrm{diag}(1,-1,\dots,-1)$ in $d+1$ dimensions
-- statement:
--   The **Minkowski matrix** in $d+1$ dimensions is the real diagonal matrix
--   $$\eta=\mathrm{diag}(1,\underbrace{-1,\dots,-1}_{d})$$
--   whose rows and columns are indexed by $\mathrm{Fin}\,1\oplus\mathrm{Fin}\,d$: the left summand is the time direction and the right summand the $d$ spatial directions. It is the matrix of the Minkowski bilinear form of signature $(1,d)$ in the standard basis, in the mostly-minus convention; for $d=3$ it is $\mathrm{diag}(1,-1,-1,-1)$, the metric appearing in the Clifford relation of the Dirac algebra.
--
--   This is the metric against which the mission's Clifford families are defined, and it is reusable for any Lorentzian matrix computation in $d+1$ dimensions.
--
--   **Formalization Note.** The entries are real; the Clifford relation coerces them entrywise to $\mathbb{C}$. The dimension $d$ is an implicit argument. The definition is Mathlib's indefinite diagonal matrix `LieAlgebra.Orthogonal.indefiniteDiagonal`, exactly as in Physlib.
-- source:
--   Physlib, `Physlib/Relativity/MinkowskiMatrix.lean`, definition `minkowskiMatrix` (L69–L71). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/Relativity/MinkowskiMatrix.lean#L69-L71

import Mathlib

open Matrix

/-- The `d.succ`-dimensional real matrix of the form `diag(1, -1, -1, -1, ...)`. -/
def minkowskiMatrix {d : ℕ} : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin d) ℝ


