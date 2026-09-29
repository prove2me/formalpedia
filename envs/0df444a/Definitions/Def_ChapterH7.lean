-- Prove2me | Definitions.Def_ChapterH7
-- name    : ChapterH7
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:58:48.013302+00:00
-- url     : https://prove2.me/theorems/57201f1c-3abb-472e-9292-7c59a69d1b51
-- title:
--   `ChapterH6` proved that the Krylov compression `B = V∗ X V` transports the Rayleigh quotient and that generation is a *s ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H7`, source chapter `BookProof/ChapterH7.lean`).
--
--   `ChapterH6` proved that the Krylov compression `B = V∗ X V` transports the Rayleigh quotient and that generation is a *single* `m × m` matrix exponential. Two structural facts that the QFM online stage relies on were left open there, and are supplied here.
--
--   **1. The reduction is physical.** If the full generator `X` is self-adjoint, so is its compression (`compress_isSelfAdjoint`), and the explicit reduced matrix is Hermitian (`reduceGenerator_isHermitian`). Consequently every eigenvalue of the reduced generator is *real* and lies between any two bounds of the numerical range of `X` (`compression_eigenvalue_mem_numericalRange`): the low-pass filter can only keep frequencies the full generator already has — it never manufactures a new one, above *or* below the original band.
--
--   **2. The online step conserves probability.** For a Hermitian reduced generator `A` and a real time `t`, the propagator `e^{−i t A}` is a unitary matrix (`generationOperator_mem_unitaryGroup`), so the generated state has the same `ℓ²` mass as the input (`generation_preserves_l2`) — the four-phase online generate of `QFM.tex` §10 is norm-preserving, and its Born weights remain a probability distribution.
--
--   * `compress_isSelfAdjoint`, `reduceGenerator_isHermitian`; * `compression_rayleigh_real` — the Rayleigh quotient of a self-adjoint generator is real; * `compression_eigenvalue_mem_numericalRange` — **headline**: an eigenvalue of the reduced generator is real and inside the numerical range of `X`; * `generationOperator`, `generationOperator_conjTranspose_mul`, `generationOperator_mem_unitaryGroup`; * `generation_preserves_l2` — **headline**: online generation preserves the `ℓ²` mass of the state.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH7.lean

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib

import Mathlib

/-!
# Chapter H7 — the reduced generator is Hermitian, its spectrum is contained,
and online generation is unitary (roadmap §9.2 / §10, continuing `ChapterH6`)

`ChapterH6` proved that the Krylov compression `B = V∗ X V` transports the
Rayleigh quotient and that generation is a *single* `m × m` matrix exponential.
Two structural facts that the QFM online stage relies on were left open there,
and are supplied here.

**1. The reduction is physical.**  If the full generator `X` is self-adjoint,
so is its compression (`compress_isSelfAdjoint`), and the explicit reduced
matrix is Hermitian (`reduceGenerator_isHermitian`).  Consequently every
eigenvalue of the reduced generator is *real* and lies between any two bounds
of the numerical range of `X` (`compression_eigenvalue_mem_numericalRange`):
the low-pass filter can only keep frequencies the full generator already has —
it never manufactures a new one, above *or* below the original band.

**2. The online step conserves probability.**  For a Hermitian reduced
generator `A` and a real time `t`, the propagator `e^{−i t A}` is a unitary
matrix (`generationOperator_mem_unitaryGroup`), so the generated state has the
same `ℓ²` mass as the input (`generation_preserves_l2`) — the four-phase online
generate of `QFM.tex` §10 is norm-preserving, and its Born weights remain a
probability distribution.

## Deliverables

* `compress_isSelfAdjoint`, `reduceGenerator_isHermitian`;
* `compression_rayleigh_real` — the Rayleigh quotient of a self-adjoint
  generator is real;
* `compression_eigenvalue_mem_numericalRange` — **headline**: an eigenvalue of
  the reduced generator is real and inside the numerical range of `X`;
* `generationOperator`, `generationOperator_conjTranspose_mul`,
  `generationOperator_mem_unitaryGroup`;
* `generation_preserves_l2` — **headline**: online generation preserves the
  `ℓ²` mass of the state.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

namespace BookProof.ChapterH7

/-! ## The compression of a self-adjoint generator -/

section SelfAdjoint

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]









end SelfAdjoint

/-! ## The reduced matrix is Hermitian -/

section Reduced

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]



end Reduced

/-! ## Online generation is unitary -/

section Unitary

open Matrix

variable {m : ℕ}

/-- The **generation propagator** `e^{−i t A}` of the reduced generator `A` at
real time `t`. -/
def generationOperator (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • A)











end Unitary

end BookProof.ChapterH7

end


