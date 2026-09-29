-- Prove2me | Definitions.Def_ChapterYangMillsFriedrichsLimit
-- name    : ChapterYangMillsFriedrichsLimit
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:49:24.929982+00:00
-- url     : https://prove2.me/theorems/a2fb1e8e-bbf1-4607-bdd7-0cffa16a6859
-- title:
--   This module continues `BookProof.ChapterYangMillsFriedrichs` (`PLAN_LEAN_SPECIALIST_QYM_FLOW.md`, Parts C and D) at the ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.YangMillsFriedrichsLimit`, source chapter `BookProof/ChapterYangMillsFriedrichsLimit.lean`).
--
--   This module continues `BookProof.ChapterYangMillsFriedrichs` (`PLAN_LEAN_SPECIALIST_QYM_FLOW.md`, Parts C and D) at the two places where that module stopped:
--
--   * **Part C was conditional.** There the Friedrichs theorem entered as a *named hypothesis*, shown consistent only in the degenerate case of an operator that is already defined on the whole space. Here the hypothesis is **discharged, by an explicit construction, for a genuinely non-degenerate class**: a symmetric positive operator on a *proper* dense domain whose quadratic form is bounded. `friedrichs_of_bounded` builds the extension (continuous extension by density) and proves all four clauses of `BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`; the class is non-empty and non-trivial by `friedrichs_bounded_nontrivial_example`.
--
--   * **Part D.4 was recorded as a conjecture only.** The obstruction named there was that the *limit operator of the Krylov flag* is not constructed. In the bounded regime it can be: `sirk_compression_tendsto` proves that the Hashimoto/SIRK compressions `Pₙ A Pₙ` converge to `A` strongly whenever the Krylov flag of a seed is dense, and `sirk_limit_unique` proves that this limit determines the operator. Combining these with Part C gives `sirk_limit_eq_positive_selfadjoint_extension`: *in the bounded regime the operator recovered in the infinite Hashimoto limit is the positive self-adjoint (Friedrichs) extension of the Weyl-gauge Hamiltonian.* This is the conjecture of `CONSOLIDATED_PLAN.md` §11.2, proved under the standing boundedness hypothesis; the unbounded continuum case remains open and is not claimed.
--
--   Nothing here claims self-adjointness of the *unbounded* continuum Yang–Mills operator, nor a mass gap. Everything below carries an explicit boundedness hypothesis on the operator, which is exactly the hypothesis that makes the Krylov limit an operator limit.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterH5

import Mathlib

/-!
# Quantum Yang–Mills, the Friedrichs route: the construction in the bounded regime
and the Hashimoto/SIRK limit

This module continues `BookProof.ChapterYangMillsFriedrichs`
(`PLAN_LEAN_SPECIALIST_QYM_FLOW.md`, Parts C and D) at the two places where that
module stopped:

* **Part C was conditional.**  There the Friedrichs theorem entered as a *named
  hypothesis*, shown consistent only in the degenerate case of an operator that
  is already defined on the whole space.  Here the hypothesis is **discharged,
  by an explicit construction, for a genuinely non-degenerate class**: a
  symmetric positive operator on a *proper* dense domain whose quadratic form is
  bounded.  `friedrichs_of_bounded` builds the extension (continuous extension
  by density) and proves all four clauses of
  `BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`; the class is
  non-empty and non-trivial by `friedrichs_bounded_nontrivial_example`.

* **Part D.4 was recorded as a conjecture only.**  The obstruction named there
  was that the *limit operator of the Krylov flag* is not constructed.  In the
  bounded regime it can be: `sirk_compression_tendsto` proves that the
  Hashimoto/SIRK compressions `Pₙ A Pₙ` converge to `A` strongly whenever the
  Krylov flag of a seed is dense, and `sirk_limit_unique` proves that this limit
  determines the operator.  Combining these with Part C gives
  `sirk_limit_eq_positive_selfadjoint_extension`: *in the bounded regime the
  operator recovered in the infinite Hashimoto limit is the positive
  self-adjoint (Friedrichs) extension of the Weyl-gauge Hamiltonian.*  This is
  the conjecture of `CONSOLIDATED_PLAN.md` §11.2, proved under the standing
  boundedness hypothesis; the unbounded continuum case remains open and is not
  claimed.

## Scope

Nothing here claims self-adjointness of the *unbounded* continuum Yang–Mills
operator, nor a mass gap.  Everything below carries an explicit boundedness
hypothesis on the operator, which is exactly the hypothesis that makes the
Krylov limit an operator limit.
-/

namespace BookProof.YangMillsFriedrichsLimit

open BookProof.ChapterH5


/-! ## Part C — the Friedrichs hypothesis discharged for bounded operators -/

section Bounded

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An everywhere-defined continuous operator, read as a linear map on the
submodule `⊤` — the shape in which
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension` expects an
extension. -/
noncomputable def topRestrict (A : F →L[ℂ] F) : (⊤ : Submodule ℂ F) →ₗ[ℂ] F :=
  A.toLinearMap.comp (⊤ : Submodule ℂ F).subtype











end Bounded

/-! ### A genuinely proper dense domain

The class of `friedrichs_of_bounded` really does contain operators whose domain
is a *proper* dense subspace: in `ℓ²(ℕ, ℂ)` the span of the canonical orthonormal
basis is dense but omits every vector of infinite support. -/

section ProperDomain

open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







end ProperDomain

/-! ## Part D — the Hashimoto/SIRK limit in the bounded regime -/

section Sirk


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The **Hashimoto/SIRK order-`n` compression** of a bounded operator with
respect to the Krylov flag of a seed `v`: `Pₙ A Pₙ`, where `Pₙ` is the
orthogonal projection onto the order-`n` Krylov subspace. -/
noncomputable def sirkCompression (A : F →L[ℂ] F) (v : F) (n : ℕ) (u : F) : F :=
  (krylovSpan A.toLinearMap v n).starProjection
    (A ((krylovSpan A.toLinearMap v n).starProjection u))









end Sirk

/-! ## The Weyl-gauge Hamiltonian: the two parts combined -/

section Weyl


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



end Weyl

end BookProof.YangMillsFriedrichsLimit


