-- Prove2me | Definitions.Def_ChapterProve2meReuse
-- name    : ChapterProve2meReuse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:37:56.02126+00:00
-- url     : https://prove2.me/theorems/30dc8072-11e6-4478-ac37-b9ca9e5ad18c
-- title:
--   Chapter Prove2meReuse
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterProve2meReuse.lean`): generated def bundle for ChapterProve2meReuse. See BookProof/ChapterProve2meReuse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterProve2meReuse.lean

import Mathlib


/-!
# Reuse of already-proved prove2me theorems — named hypotheses for the NS / QG route

This chapter carries the theorems that the prove2me catalogue **already proves**,
in the form the offline specialist can use them: **named hypotheses**, never
`axiom`s.  The frozen source is `PROVE2ME_REUSABLE_THEOREMS.md` at the repository
root; every `def … : Prop` below is one row of that report, transcribed verbatim
from the platform's `formal_statement` (which elaborates at Lean v4.33.1 /
Mathlib `0df444a`).

## Why hypotheses and not `import`

timepiece pins Lean `v4.28.0` (the Aristotle requirement) while prove2me compiles
`v4.33.1`; a Lean `import` binds one toolchain, so a platform module cannot be
imported here.  The prove2me node is the external witness of the proposition, and
a route theorem consumes it through `RouteHypotheses` (or through the individual
`Prop`s).  Nothing here is an `axiom`, so the project's axiom gate still reports
only the standard three.

## What is transcribed, and what is deferred

Transcribed below (all notions exist in Mathlib v4.28.0):

* `ConvolutionCLMSymmetric` — prove2me `MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg`
  (`f7acdc05-a79d-5e62-9e62-4744e92d9ee6`, author `Claude`).
* `ExistsConvolutionCompact` — prove2me
  `MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace`
  (`b4b789f8-1e81-5087-ba89-9a6b3bef55f0`, author `Claude`).
* `PosDefLowerBound` — prove2me `posDef_quadratic_form_lower_bound`
  (`0fc6dadb-9da8-4557-815b-127c310e3ef3`, author `olivier`).
* `DetAddTwo` — prove2me `Diaz.det_add_two`
  (`47ddec80-bd8c-47cb-a891-32d7f12de9b3`, author `carlok`).
* `CompactSymmetricOrthogonalEigenspace` — prove2me
  `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker`
  (`9b157d55-6fac-50a1-a424-4b346c1ec0da`, author `Claude`).
* `CompactSymmetricHighPart` — prove2me
  `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`
  (`2126e74d-67bb-5b87-90d7-98ffb1eda8fd`, author `Claude`).
* `GribovNegativeDirection` — prove2me `GribovRegion.exists_neg_quadratic_form_of_traceless`
  (`a883b692-5447-48b6-8920-15e669d3954e`, author `Lucas`).

**Deferred (not transcribable in v4.28.0 — see the report):**
`Bochner.fourierTransform_nonneg`, `singular_value_zero_le_spectral_norm` and
`spectral_norm_le_singular_value_zero` use `IsPositiveDefinite`, `spectralNorm`
(matrix operator norm) and `singularValues`, none of which exist in this Mathlib
(the v4.28 `spectralNorm` is a different algebra-norm notion).  They need a local
definition before they can be stated; the report records the obstacle.
-/

open MeasureTheory
open scoped Convolution

namespace BookProof.Prove2meReuse

/-- prove2me `MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg`
(id `f7acdc05-a79d-5e62-9e62-4744e92d9ee6`, author `Claude`): a convolution
operator with a kernel satisfying `f (-x) = conj (f x)` is symmetric.  This is
the symmetry of the one-particle convolution mode operator in the momentum-space
route (plan item 3). -/
abbrev ConvolutionCLMSymmetric : Prop :=
  ∀ (G : Type) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (f : C(G, ℂ)), (∀ x, f (-x) = star (f x)) →
    ∀ (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
      (∀ φ : Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) →
      LinearMap.IsSymmetric (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)

/-- prove2me `MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace`
(id `b4b789f8-1e81-5087-ba89-9a6b3bef55f0`, author `Claude`): there is a
symmetric **compact** convolution operator realizing convolution by `f` on `L²`
of a compact group.  Compactness is what makes the mode operator's spectrum a
Ritz ladder (the band calculus of the QG route). -/
abbrev ExistsConvolutionCompact : Prop :=
  ∀ (G : Type) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (f : C(G, ℂ)), (∀ x, f (-x) = star (f x)) →
    ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      (∀ φ : Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T ∧ LinearMap.IsSymmetric (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)

/-- prove2me `posDef_quadratic_form_lower_bound`
(id `0fc6dadb-9da8-4557-815b-127c310e3ef3`, author `olivier`): a positive
definite matrix has a positive quadratic-form lower bound.  This is the fibrewise
`PosSymOp.pos` input that makes the Friedrichs comparison of the NS route bounded
below (plan items 4 and 5). -/
abbrev PosDefLowerBound : Prop :=
  ∀ {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}, M.PosDef →
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * dotProduct x x ≤ dotProduct x (M.mulVec x)

/-- prove2me `Diaz.det_add_two` (id `47ddec80-bd8c-47cb-a891-32d7f12de9b3`,
author `carlok`): the determinant of a sum of `2 × 2` matrices.  The small-case
template for the determinant expansion behind `detPoly_pos` and the logarithmic
volume square of the Lagrangian route (plan item 6, §6.1). -/
abbrev DetAddTwo : Prop :=
  ∀ {R : Type} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R),
    (X + Y).det = X.det + Y.det + Matrix.trace X * Matrix.trace Y
      - Matrix.trace (X * Y)

/-- prove2me `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker`
(id `9b157d55-6fac-50a1-a424-4b346c1ec0da`, author `Claude`): for a compact
symmetric operator, the orthogonal complement of the span of its non-zero
eigenspaces is its kernel.  This is the compact-symmetric spectral decomposition
consumed by the band / Ritz ladder of the QG route (plan item 8). -/
abbrev CompactSymmetricOrthogonalEigenspace : Prop :=
  ∀ {𝕜 E : Type}  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {T : E →L[𝕜] E}, IsCompactOperator T →
    (T : E →ₗ[𝕜] E).IsSymmetric →
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ
      = LinearMap.ker (T : E →ₗ[𝕜] E)

/-- prove2me `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`
(id `2126e74d-67bb-5b87-90d7-98ffb1eda8fd`, author `Claude`): the high-part
(above a positive radius `r`) of a compact symmetric operator is
finite-dimensional.  This is the Ritz truncation statement of the QG route. -/
abbrev CompactSymmetricHighPart : Prop :=
  ∀ {𝕜 E : Type}  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {T : E →L[𝕜] E}, IsCompactOperator T →
    (T : E →ₗ[𝕜] E).IsSymmetric → ∀ (X : Submodule 𝕜 E),
      (∀ r : ℝ, 0 < r →
        X ⊓ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖),
          Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥
        ∨ X ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖),
          Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ) →
      X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X

/-- prove2me `GribovRegion.exists_neg_quadratic_form_of_traceless`
(id `a883b692-5447-48b6-8920-15e669d3954e`, author `Lucas`): a non-zero
traceless Hermitian matrix has a negative direction.  A Gribov-region fact
adjacent to the QG quadratic form (plan item 7). -/
abbrev GribovNegativeDirection : Prop :=
  ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ), M.IsHermitian → M.trace = 0 → M ≠ 0 →
    ∃ w : Fin n → ℝ, dotProduct w (M.mulVec w) < 0

/-- The bundle of prove2me theorems the NS / QG Faris–Lavine route consumes.

A route theorem takes one value of this structure as a parameter instead of
re-proving, or assuming as an `axiom`, any of the seven facts.  Each field is a
proposition already proved on prove2me (see the module header for ids). -/
structure RouteHypotheses where
  /-- One-particle convolution mode operators are symmetric. -/
  convolution_symmetric : ConvolutionCLMSymmetric
  /-- Convolution by a continuous self-dual kernel is a compact operator. -/
  convolution_compact : ExistsConvolutionCompact
  /-- Positive definite matrices give a positive form lower bound. -/
  posDef_lower_bound : PosDefLowerBound
  /-- The determinant-of-a-sum identity for `2 × 2` matrices. -/
  det_add_two : DetAddTwo
  /-- The compact-symmetric orthogonal-eigenspace/kernel identity. -/
  compact_symmetric_orthogonal_eigenspace : CompactSymmetricOrthogonalEigenspace
  /-- The high part of a compact symmetric operator is finite-dimensional. -/
  compact_symmetric_high_part : CompactSymmetricHighPart
  /-- Traceless Hermitian non-zero matrices have a negative direction. -/
  gribov_negative_direction : GribovNegativeDirection

/-! ## Route-facing projections

These are the names the NS and QG route chapters call; each is a projection of
`RouteHypotheses`, so the route carries the platform theorem as a *hypothesis*
and never as an axiom. -/















end BookProof.Prove2meReuse


