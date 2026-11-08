-- Prove2me | Definitions.Def_MaxCompForest_massInvSqrt
-- name    : MaxCompForest_massInvSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:03.869764+00:00
-- url     : https://prove2.me/theorems/e03cf593-cb2a-4b21-8d7f-79a81842fc87
-- title:
--   The diagonal matrix $W^{-1/2}$ of a mass vector
-- statement:
--   For a vector of positive vertex masses $W=(w_v)_{v\in V}$, the diagonal matrix
--   $$
--   W^{-1/2}=\mathrm{diag}(w_v^{-1/2}).
--   $$
--   It is the congruence that turns the Laplacian into the mass-normalized Laplacian.
--
--   **Formalization Note** On a non-positive mass the Lean entry is $0$; every statement that uses this matrix has positive masses.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1, p.7

import Mathlib

namespace MaxCompForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The diagonal matrix `W^{-1/2}`** of a mass vector `W`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1, p.7.

**Formalization Note.** `Real.sqrt` and the inverse are junk at a non-positive mass (the entry is
`0`); every statement using this matrix has positive masses, or degrees of a connected graph on at
least two vertices. -/
noncomputable def massInvSqrt (W : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal fun v => (Real.sqrt (W v))⁻¹

end MaxCompForest


