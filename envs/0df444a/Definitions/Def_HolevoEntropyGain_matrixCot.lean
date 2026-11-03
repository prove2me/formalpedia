-- Prove2me | Definitions.Def_HolevoEntropyGain_matrixCot
-- name    : HolevoEntropyGain_matrixCot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:49.300198+00:00
-- url     : https://prove2.me/theorems/0f33fa22-4961-4e72-a151-937492d64637
-- title:
--   Cotangent of a real square matrix
-- statement:
--   For a real square matrix $M$ with $\sin M$ invertible,
--
--   $$
--   \cot M = \cos M\,(\sin M)^{-1}.
--   $$
--
--   $\cos M$ and $\sin M$ commute, so the order is immaterial.
--
--   **Formalization Note** Lean's matrix inverse is $0$ for a singular matrix; Lemma 2 asserts the invertibility of $\sin(\beta\epsilon\Delta)$ as part of its conclusion.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (17), p.5

import Mathlib
import Definitions.Def_HolevoEntropyGain_matrixCos
import Definitions.Def_HolevoEntropyGain_matrixSin

namespace HolevoEntropyGain

/-- The cotangent `cot M = cos M (sin M)⁻¹` of a real square matrix
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (17), p.5, PDF p.5).

**Formalization Note** Lean's inverse is `0` on a singular matrix, so `lemma_2` also asserts that
`sin(βεΔ)` is invertible. -/
noncomputable def matrixCot {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Matrix n n ℝ :=
  matrixCos M * (matrixSin M)⁻¹

end HolevoEntropyGain


