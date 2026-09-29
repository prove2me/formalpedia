-- Prove2me | Definitions.Def_ChapterSirkWhitening
-- name    : ChapterSirkWhitening
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:11:17.219727+00:00
-- url     : https://prove2.me/theorems/e82bd13d-a664-4c75-b3ee-4c32ade84733
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**: "the numerical reduction computes `H_proj` from a whitened Gram matrix … Missi ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkWhitening`, source chapter `BookProof/ChapterSirkWhitening.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**: "the numerical reduction computes `H_proj` from a whitened Gram matrix … Missing: the identity of the whitened reduced operator with the compression `V∗XV` in the non-degenerate case."
--
--   The mathematical content of "whitening" is that *any* orthonormalization of the raw Krylov vectors may be used: Gram whitening, Gram–Schmidt/Arnoldi, or a Cholesky factor. What has to be true for the numerics to be well posed is that the answer does not depend on which one is taken. That is what is proved here, in the coordinate-free form: **two isometric embeddings with the same range give unitarily equivalent compressions, and literally the same SIRK approximant on the ambient space.**
--
--   * `rangeProj` — the reconstruction operator `V ∘ V∗` of an isometric embedding. * `rangeProj_comp_self` / `rangeProj_isSelfAdjoint` — it is the orthogonal projection onto the range. * `rangeProj_eq_of_range_eq` — **two isometries with the same range have the same projection**. * `whiteningEquiv` — the change-of-whitening map `W = V₂∗ ∘ V₁`, and `whiteningEquiv_isometry`, `whiteningEquiv_left_inverse`: it is unitary. * `compress_conj_whitening` — **headline (Gap 4c, non-degenerate case)**: the two reduced operators are conjugate, `V₁∗XV₁ = W∗ (V₂∗XV₂) W`; in particular they have the same spectrum, the same numerical range and the same Ritz values. * `sirkApprox_eq_of_range_eq` — and the reconstructed approximant on the ambient space is *identical*, so the SIRK output is independent of the whitening.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkWhitening.lean

import Definitions.Def_ChapterH4
import Mathlib

import Mathlib

/-!
# Chapter SirkWhitening — the reduced operator depends only on the retained subspace

`CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**: "the numerical reduction computes
`H_proj` from a whitened Gram matrix … Missing: the identity of the whitened
reduced operator with the compression `V∗XV` in the non-degenerate case."

The mathematical content of "whitening" is that *any* orthonormalization of the
raw Krylov vectors may be used: Gram whitening, Gram–Schmidt/Arnoldi, or a
Cholesky factor.  What has to be true for the numerics to be well posed is that
the answer does not depend on which one is taken.  That is what is proved here,
in the coordinate-free form: **two isometric embeddings with the same range give
unitarily equivalent compressions, and literally the same SIRK approximant on the
ambient space.**

## Deliverables

* `rangeProj` — the reconstruction operator `V ∘ V∗` of an isometric embedding.
* `rangeProj_comp_self` / `rangeProj_isSelfAdjoint` — it is the orthogonal
  projection onto the range.
* `rangeProj_eq_of_range_eq` — **two isometries with the same range have the same
  projection**.
* `whiteningEquiv` — the change-of-whitening map `W = V₂∗ ∘ V₁`, and
  `whiteningEquiv_isometry`, `whiteningEquiv_left_inverse`: it is unitary.
* `compress_conj_whitening` — **headline (Gap 4c, non-degenerate case)**: the two
  reduced operators are conjugate, `V₁∗XV₁ = W∗ (V₂∗XV₂) W`; in particular they
  have the same spectrum, the same numerical range and the same Ritz values.
* `sirkApprox_eq_of_range_eq` — and the reconstructed approximant on the ambient
  space is *identical*, so the SIRK output is independent of the whitening.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterSirkWhitening

open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-! ## 1. The range projection -/

/-- The reconstruction operator `V ∘ V∗` of an isometric embedding. -/
def rangeProj (V : F →L[ℂ] E) : E →L[ℂ] E := V.comp V.adjoint

















/-! ## 2. The change of whitening -/

/-- The **change-of-whitening map** `W = V₂∗ ∘ V₁` between the two coordinate
spaces of two embeddings of the same subspace. -/
def whiteningEquiv (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) : F →L[ℂ] G :=
  V₂.adjoint.comp V₁







/-! ## 3. Whitening independence of the reduced operator -/







end BookProof.ChapterSirkWhitening


