-- Prove2me | Definitions.Def_ChapterSirkDiffusiveDecay
-- name    : ChapterSirkDiffusiveDecay
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T11:50:29.80441+00:00
-- url     : https://prove2.me/theorems/2e20ab49-c0e8-455f-970e-1d0b007d46df
-- title:
--   SIRK diffusive decay
-- statement:
--   Formal definitions for the sirk diffusive decay of the timepiece Lean 4 formalization (module `BookProof.ChapterSirkDiffusiveDecay`, source chapter `BookProof/ChapterSirkDiffusiveDecay.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

import Mathlib











open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace BookProof.ChapterH4

/-- The **SIRK compression** `B := V∗ X V` of an operator `X` to the finite
subspace embedded by the isometry `V`.  With `V = Vₘ` the orthonormal Krylov
basis and `X = Xₘ` the shift-invert resolvent, this is exactly the paper's
`Hₘ Kₘ⁻¹` (eq. 10). -/
def compress (V : F →L[ℂ] E) (X : E →L[ℂ] E) : F →L[ℂ] F :=
  V.adjoint.comp (X.comp V)

end BookProof.ChapterH4











noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace BookProof.ChapterSirkDiffusiveDecay

/-- The parabolic (heat) semigroup `e^{−tA}` of a bounded generator. -/
def heatFlow (A : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := exp ((-t) • A)

/-- **Coercivity** of a generator with rate `μ`: `μ‖x‖² ≤ Re⟪x, A x⟫`.  For the
parabolic part of the Navier–Stokes Lagrangian generator this is the mode-wise
bound with `μ = νk²`. -/
def IsCoercive (A : E →L[ℂ] E) (mu : ℝ) : Prop :=
  ∀ x : E, mu * ‖x‖ ^ 2 ≤ (inner ℂ x (A x) : ℂ).re

end BookProof.ChapterSirkDiffusiveDecay


