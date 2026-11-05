-- Prove2me | Definitions.Def_Chi2QEC_IsNondegenerate
-- name    : Chi2QEC_IsNondegenerate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:47.651818+00:00
-- url     : https://prove2.me/theorems/4de8e8a4-dd2d-4d1c-b571-48f3f26bd1ef
-- title:
--   Nondegenerate code
-- statement:
--   A code $C$ is nondegenerate for a finite error family $(E_h)_h$ when, for every unit vector $\psi\in C$, the Gram matrix
--   $$
--   \big(\langle E_a\psi,E_b\psi\rangle\big)_{a,b}
--   $$
--   of the error images of $\psi$ is nonsingular, that is, the vectors $E_h\psi$ are linearly independent.
--
--   The paper uses the term in Theorems 2–4 and Section VI without defining it. This is the standard meaning, the one under which the error images of a code are independent copies of it.
--
--   **Formalization Note** For the zero code the condition is vacuous.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Theorems 2–4, p.16; Sec. VI, p.17

import Mathlib

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Theorems 2–4, p.16, and Sec. VI, p.17 ("nondegenerate codes"; the paper uses
the term without defining it): the code `C` is nondegenerate for the errors `E` when, for every
unit vector `ψ ∈ C`, the error images `E_h ψ` are linearly independent, i.e. their Gram matrix
`(⟨E_a ψ, E_b ψ⟩)_{a,b}` is nonsingular.

**Formalization Note.** This is the standard meaning of the term, and the convention of the
published Pauli-only `QAlgorithms.IsNondegenerate`. For `C = ⊥` it holds vacuously. -/
def IsNondegenerate {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (E : κ → Matrix ι ι ℂ) : Prop :=
  ∀ ψ ∈ C, ‖ψ‖ = 1 →
    (Matrix.of fun a b =>
      inner ℂ (Matrix.toEuclideanLin (E a) ψ) (Matrix.toEuclideanLin (E b) ψ) : Matrix κ κ ℂ).det ≠ 0

end Chi2QEC


