-- Prove2me | Definitions.Def_ChapterTempleSeparationNecessary
-- name    : ChapterTempleSeparationNecessary
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:00:25.123872+00:00
-- url     : https://prove2.me/theorems/ef6a6114-8046-4535-b8c7-efcdf9fd759f
-- title:
--   Chapter TempleSeparationNecessary
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTempleSeparationNecessary.lean`): generated def bundle for ChapterTempleSeparationNecessary. See BookProof/ChapterTempleSeparationNecessary.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTempleSeparationNecessary.lean

import Definitions.Def_ChapterRitzCertificate
import Mathlib


/-!
# Chapter TempleSeparationNecessary — the spectral-separation input cannot be removed

`ChapterRitzCertificate` derives the per-order finite certificate from Temple's inequality,
whose one non-computational input is the spectral separation

  `SpectralSeparation A l b`  —  `l ≤ b` and every spectral point is `l` or `≥ b`.

`CONSOLIDATED_PLAN.md` records this as the remaining side condition of the certificate
route.  This chapter shows that it is a *genuine* side condition and not an artifact of the
proof: **no** bound on the spectral edge in terms of the Rayleigh quotient and residual of a
trial vector can hold without it.

`separation_necessary` exhibits, for every `M`, a bounded self-adjoint operator on a
two-dimensional Hilbert space and a unit trial vector whose Rayleigh quotient and residual
are both `0` — the best possible finite data — while the bottom of the spectrum is at most
`−M`.  So the residual alone controls nothing: a trial vector can be an *exact* eigenvector
and still say nothing about how far below the spectrum extends.  Some a priori information
about the rest of the spectrum, which is exactly what `SpectralSeparation` supplies, must be
provided from outside the finite computation.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.TempleSeparationNecessary

open BookProof.RitzCertificate

/-- The two-dimensional witness space. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- The rank-one orthogonal projection onto `ℂ ∙ x`, for a unit vector `x`. -/
def proj (x : E2) : E2 →L[ℂ] E2 := (innerSL ℂ x).smulRight x



/-- The witness operator: `−M` on the orthogonal complement of `x`, and `0` on `ℂ ∙ x`. -/
def witness (M : ℝ) (x : E2) : E2 →L[ℂ] E2 :=
  ((-M : ℝ) : ℂ) • ((1 : E2 →L[ℂ] E2) - proj x)





/-- The trial vector: the first basis vector, an exact eigenvector of `witness M x` for the
eigenvalue `0`. -/
def trial : E2 := EuclideanSpace.single 0 (1 : ℂ)

/-- The vector orthogonal to the trial vector, an exact eigenvector for `−M`. -/
def other : E2 := EuclideanSpace.single 1 (1 : ℂ)











/-! ## The finite data are perfect, and say nothing -/





/-! ## Yet the spectrum reaches down to `−M` -/







end BookProof.TempleSeparationNecessary

end


