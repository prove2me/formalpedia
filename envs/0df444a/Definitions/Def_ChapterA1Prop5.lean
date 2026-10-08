-- Prove2me | Definitions.Def_ChapterA1Prop5
-- name    : ChapterA1Prop5
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:33:49.936566+00:00
-- url     : https://prove2.me/theorems/7ebd8880-b7ed-4eed-b90f-00146a7846f2
-- title:
--   Chapter A1Prop5
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA1Prop5.lean`): generated def bundle for ChapterA1Prop5. See BookProof/ChapterA1Prop5.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA1Prop5.lean

import Definitions.Def_ChapterA1
import Mathlib

/-!
# Chapter A, §A.1 — Proposition 5: (anti-)unitarity is a realification-invariant

This file formalizes `book.tex` **Proposition 5** (§"Systems on real and complex
Hilbert spaces", line ~4797) of the chapter *"Real representations, CPT theorem
and the relativistic position operator"*.

**Note 4** of the book defines: an (anti-)linear operator `U : H₁ → H₂` between
inner-product spaces is *(anti-)unitary* iff
1) it is surjective, and
2) for all `x`, `⟪U x, U x⟫ = ⟪x, x⟫`.

**Proposition 5** states that for complex Hilbert spaces `H₁, H₂` and their
realifications `H₁ʳ, H₂ʳ`, the operator `U` is (anti-)unitary **iff** the operator
`Uʳ : H₁ʳ → H₂ʳ`, `Uʳ(h) := U(h)`, is (anti-)unitary.  The book's one-line proof:
`⟪h, h⟫ = ⟪h, h⟫ʳ` and `Uʳ(h) = U(h)`, so the two isometry conditions coincide.

We take the realification `H^r` to be the *same carrier type* equipped with the
real inner product `⟪v, u⟫_ℝ = re ⟪v, u⟫_ℂ` (Mathlib's
`InnerProductSpace.rclikeToReal`, registered here as a **local** instance to avoid
the real/complex inner-product diamond).  Then `Uʳ` is literally the same
underlying function `U`, matching the book's `Uʳ(h) = U(h)`, so surjectivity is
shared verbatim.  The mathematical content is the pointwise equivalence of the
two isometry conditions, `inner_self_complex_iff_real`, which needs **no**
(anti-)linearity of `U` at all — it holds for an arbitrary function.  Hence the
statement covers the unitary (linear) and anti-unitary (conjugate-linear) cases
uniformly; the two `LinearMap`/semilinear corollaries record this.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
namespace BookProof.ChapterA

end BookProof.ChapterA


