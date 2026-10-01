-- Prove2me | Definitions.Def_ChapterPaFreeCompletion
-- name    : ChapterPaFreeCompletion
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:03:47.591313+00:00
-- url     : https://prove2.me/theorems/42b3df5e-1d03-4184-8d64-7db5ec13fa0b
-- title:
--   Chapter PaFreeCompletion
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPaFreeCompletion.lean`): generated def bundle for ChapterPaFreeCompletion. See BookProof/ChapterPaFreeCompletion.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPaFreeCompletion.lean

import Definitions.Def_ChapterRieszFischer
import Mathlib


/-!
# PA-Free Completion: The Riesz–Fischer Framework

We formalize the Riesz–Fischer characterization for the finitely-supported
core and its completion. The completion adds exactly the limit points
needed for Hilbert space completeness without introducing new "pathological"
vectors.

This is the mathematical foundation for the Solovay–Hilbert decidability
architecture: the completion of the finitely-supported core does not
leak PA / is a conservative extension.

**Update (August 2026).**  The Riesz–Fischer statement of this file used to be a
`True` placeholder.  It is now a genuine theorem: the analytic content lives in
`BookProof/ChapterRieszFischer.lean`, and this file records the identification of
the dense core `ℕ →₀ ℝ` with the finitely-supported vectors of `ℓ²(ℕ)`
(`range_ofCore`) together with the completeness / density / properness package
(`riesz_fischer`, `denseCore_dense`, `denseCore_proper`).
-/

open Set
open Filter
open BookProof.ChapterRieszFischer

/-- The dense core: finitely-supported vectors on ℕ.
    These represent the "definable" or "computable" vectors
    in the Riesz–Fischer framework. -/
abbrev DenseCore := ℕ →₀ ℝ

/-- The dense core is a real vector space. -/
noncomputable instance : AddCommGroup DenseCore :=
  Finsupp.instAddCommGroup (ι := ℕ) (G := ℝ)



/-- The canonical embedding of the dense core into its completion `ℓ²(ℕ)`:
a finitely-supported sequence is the (finite) sum of its coordinate atoms. -/
noncomputable def ofCore (v : DenseCore) : Ell2 :=
  ∑ i ∈ v.support, lp.single 2 i (v i)


