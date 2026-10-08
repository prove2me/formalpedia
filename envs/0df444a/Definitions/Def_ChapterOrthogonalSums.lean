-- Prove2me | Definitions.Def_ChapterOrthogonalSums
-- name    : ChapterOrthogonalSums
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:38:50.854134+00:00
-- url     : https://prove2.me/theorems/6729abc5-cb18-4bd1-9894-58b87c8685ee
-- title:
--   Chapter OrthogonalSums
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterOrthogonalSums.lean`): generated def bundle for ChapterOrthogonalSums. See BookProof/ChapterOrthogonalSums.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterOrthogonalSums.lean

import Mathlib

/-!
# Unconditional sums of orthogonal families

Elementary Hilbert-space facts that the infinite-dimensional versions of Mackey's and
Wigner's theorems need, and which are stated here once for both.

* `norm_sum_sq_of_orthogonal` — Pythagoras over a `Finset`;
* `summable_of_orthogonal_of_summable_norm_sq` — a pairwise orthogonal family whose squared
  norms are summable is (unconditionally) summable in a complete space;
* `hasSum_norm_sq_of_hasSum` — Parseval: if an orthogonal family sums to `ψ` then its
  squared norms sum to `‖ψ‖²`;
* `hasSum_smul_of_hasSum_norm_sq` — the converse of Bessel's inequality: a vector whose
  Fourier coefficients with respect to an orthonormal family saturate Bessel's inequality is
  the sum of its Fourier series.

Everything is `sorry`-free and uses only the standard axioms.
-/
namespace BookProof.ChapterOrthogonalSums

end BookProof.ChapterOrthogonalSums


