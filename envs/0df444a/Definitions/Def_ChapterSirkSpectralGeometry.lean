-- Prove2me | Definitions.Def_ChapterSirkSpectralGeometry
-- name    : ChapterSirkSpectralGeometry
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:15:39.926608+00:00
-- url     : https://prove2.me/theorems/05ca3460-8d51-4c4c-98a8-ac500b56c328
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 2** asks for the finite-`m` quantitative constants of the SIRK bound *per system*, "f ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkSpectralGeometry`, source chapter `BookProof/ChapterSirkSpectralGeometry.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 2** asks for the finite-`m` quantitative constants of the SIRK bound *per system*, "from the actual spectral geometry". `ChapterSirkEndToEnd` closed the assembly (Gap 1) with abstract `C`, `Dmin`, `h` and showed (`crouzeix_domain_transfer`) that a *single* convex set `Σ ⊇ W(X)` serves both Crouzeix bounds. What was still missing is the identification of that `Σ` from the operator the algorithm actually iterates — the **shift-invert** `X = (A − γ)⁻¹`. This chapter supplies it, generically, in the two regimes the project uses:
--
--   * **the positive/Friedrichs regime** (real shift `γ > 0`): the shift-invert `R` of a positive symmetric operator is self-adjoint and positive with `‖R‖ ≤ γ⁻¹`, hence its numerical range is contained in the **real segment** `[0, γ⁻¹]` — `numRange_subset_realSegment_of_shiftInvert`. A segment is a degenerate (one-dimensional) convex set: this is the best possible Crouzeix domain, and it is inherited by every Krylov compression (`crouzeix_domain_shiftInvert`). * **the indefinite regime** (non-real shift `γ`, `Im γ ≠ 0`, no positivity): `‖X‖ ≤ |Im γ|⁻¹` gives the **closed disc** of radius `|Im γ|⁻¹` around the origin — `numRange_subset_closedBall_of_shiftInvertC` and `crouzeix_domain_shiftInvertC`.
--
--   The last theorem, `sirk_end_to_end_crouzeix_domain`, is the form of the end-to-end bound in which the *domain* is the hypothesis: one convex `Σ` containing `W(X)` is enough — the compression side is discharged by `ChapterH9.numRange_compress_subset`. Its two shift-invert instances `sirk_end_to_end_shiftInvert` and `sirk_end_to_end_shiftInvertC` are the system-independent statements that `ChapterSirkPerSystem` instantiates for QYM, NS (Eulerian and Lagrangian) and QG.
--
--   Crouzeix's inequality itself is still a named hypothesis, exactly as in `ChapterH4`: what is proved here is that *one explicit convex set* — determined by the shift alone — can be used for it, uniformly in the reduction order `m`. Nothing is claimed about floating-point arithmetic (§12.2 Gap 6).
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkSpectralGeometry.lean

import Definitions.Def_ChapterH9
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHashimotoComplexShifts
import Mathlib

import Mathlib

/-!
# Chapter SirkSpectralGeometry — the Crouzeix domain of the shift-invert operator

`CONSOLIDATED_PLAN.md` §12.2 **Gap 2** asks for the finite-`m` quantitative
constants of the SIRK bound *per system*, "from the actual spectral geometry".
`ChapterSirkEndToEnd` closed the assembly (Gap 1) with abstract `C`, `Dmin`, `h`
and showed (`crouzeix_domain_transfer`) that a *single* convex set `Σ ⊇ W(X)`
serves both Crouzeix bounds.  What was still missing is the identification of
that `Σ` from the operator the algorithm actually iterates — the **shift-invert**
`X = (A − γ)⁻¹`.  This chapter supplies it, generically, in the two regimes the
project uses:

* **the positive/Friedrichs regime** (real shift `γ > 0`): the shift-invert `R`
  of a positive symmetric operator is self-adjoint and positive with
  `‖R‖ ≤ γ⁻¹`, hence its numerical range is contained in the **real segment**
  `[0, γ⁻¹]` — `numRange_subset_realSegment_of_shiftInvert`.  A segment is a
  degenerate (one-dimensional) convex set: this is the best possible Crouzeix
  domain, and it is inherited by every Krylov compression
  (`crouzeix_domain_shiftInvert`).
* **the indefinite regime** (non-real shift `γ`, `Im γ ≠ 0`, no positivity):
  `‖X‖ ≤ |Im γ|⁻¹` gives the **closed disc** of radius `|Im γ|⁻¹` around the
  origin — `numRange_subset_closedBall_of_shiftInvertC` and
  `crouzeix_domain_shiftInvertC`.

The last theorem, `sirk_end_to_end_crouzeix_domain`, is the form of the
end-to-end bound in which the *domain* is the hypothesis: one convex `Σ`
containing `W(X)` is enough — the compression side is discharged by
`ChapterH9.numRange_compress_subset`.  Its two shift-invert instances
`sirk_end_to_end_shiftInvert` and `sirk_end_to_end_shiftInvertC` are the
system-independent statements that `ChapterSirkPerSystem` instantiates for
QYM, NS (Eulerian and Lagrangian) and QG.

## Honest boundary

Crouzeix's inequality itself is still a named hypothesis, exactly as in
`ChapterH4`: what is proved here is that *one explicit convex set* — determined
by the shift alone — can be used for it, uniformly in the reduction order `m`.
Nothing is claimed about floating-point arithmetic (§12.2 Gap 6).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterSirkSpectralGeometry

open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine

/-! ## 1. The real segment as a Crouzeix domain -/

/-- The segment `[a, b]` of the real axis, viewed inside `ℂ`. -/
def realSegment (a b : ℝ) : Set ℂ := {z : ℂ | z.im = 0 ∧ a ≤ z.re ∧ z.re ≤ b}





/-! ## 2. The positive (Friedrichs) regime: the numerical range is a segment -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}





/-! ## 3. The indefinite regime: the numerical range is a disc -/





/-! ## 4. The end-to-end bound with the Crouzeix domain as the hypothesis -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]





/-! ## 5. The two shift-invert instances -/





end BookProof.ChapterSirkSpectralGeometry


