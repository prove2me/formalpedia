-- Prove2me | Definitions.Def_ChapterH6
-- name    : ChapterH6
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:50:36.826423+00:00
-- url     : https://prove2.me/theorems/48aa2731-e985-409f-b8da-6ed3932e2c62
-- title:
--   `QFM.tex` §9.2 reads the Krylov projection of the Hashimoto generator as an *exact spectral low-pass filter*: the reduce ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H6`, source chapter `BookProof/ChapterH6.lean`).
--
--   `QFM.tex` §9.2 reads the Krylov projection of the Hashimoto generator as an *exact spectral low-pass filter*: the reduced `m × m` generator keeps the dominant part of the spectrum, the discarded high-frequency content costs only the `e^{−hm}` term already carried by `ChapterH4.sirk_error_bound_decay`, and generation is then a single `O(m²)` matrix exponential.
--
--   * `sirk_error_decay_exponential` — the SIRK error bound of `ChapterH4.sirk_error_bound_decay` really decays: as the Krylov dimension `m` grows the bound tends to `0` (for `h > 0`), and `sirk_error_bound_antitone` records that it is non-increasing in `m`; * `sirk_error_tendsto_zero` — consequently the SIRK approximants converge: the errors are eventually below any `ε > 0`; * `krylov_rayleigh_transfer` — the Rayleigh–Ritz identity `⟪y, (V∗XV) y⟫ = ⟪Vy, X (Vy)⟫`: the reduced generator's quadratic form is a *restriction* of the full one; * `krylovRetainsDominantSpectrum` — hence every eigenvalue of the reduced generator is a Rayleigh quotient of `X` and is bounded by `‖X‖`: the compression retains spectrum, it never manufactures new frequencies; * `reduceGenerator`, `reduceGenerator_eq_compress_entry`, `reduce_generator_mul_m` — the reduced generator `H̄_reduced = Vᴴ H̄ V` is an explicit `m × m` matrix, i.e. exactly `m²` scalars; * `generation_at_zero`, `generation_semigroup`, `generation_single_exponential` — **headline**: generation is a *single* matrix exponential `Ψ_{t=1} = e^{−i H̄_reduced} Ψ₀` of the reduced generator, with the semigroup law making the whole trajectory that one exponential.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Mathlib

import Mathlib

/-!
# Chapter H6 — Krylov projection as a spectral low-pass filter (plan Part F.2,
roadmap §9.2)

`QFM.tex` §9.2 reads the Krylov projection of the Hashimoto generator as an
*exact spectral low-pass filter*: the reduced `m × m` generator keeps the
dominant part of the spectrum, the discarded high-frequency content costs only
the `e^{−hm}` term already carried by `ChapterH4.sirk_error_bound_decay`, and
generation is then a single `O(m²)` matrix exponential.

## Deliverables

* `sirk_error_decay_exponential` — the SIRK error bound of
  `ChapterH4.sirk_error_bound_decay` really decays: as the Krylov dimension `m`
  grows the bound tends to `0` (for `h > 0`), and `sirk_error_bound_antitone`
  records that it is non-increasing in `m`;
* `sirk_error_tendsto_zero` — consequently the SIRK approximants converge:
  the errors are eventually below any `ε > 0`;
* `krylov_rayleigh_transfer` — the Rayleigh–Ritz identity
  `⟪y, (V∗XV) y⟫ = ⟪Vy, X (Vy)⟫`: the reduced generator's quadratic form is a
  *restriction* of the full one;
* `krylovRetainsDominantSpectrum` — hence every eigenvalue of the reduced
  generator is a Rayleigh quotient of `X` and is bounded by `‖X‖`: the
  compression retains spectrum, it never manufactures new frequencies;
* `reduceGenerator`, `reduceGenerator_eq_compress_entry`,
  `reduce_generator_mul_m` — the reduced generator `H̄_reduced = Vᴴ H̄ V` is an
  explicit `m × m` matrix, i.e. exactly `m²` scalars;
* `generation_at_zero`, `generation_semigroup`,
  `generation_single_exponential` — **headline**: generation is a *single*
  matrix exponential `Ψ_{t=1} = e^{−i H̄_reduced} Ψ₀` of the reduced generator,
  with the semigroup law making the whole trajectory that one exponential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open Filter Topology

namespace BookProof.ChapterH6

/-! ## The exponential decay of the SIRK bound -/

/-- The eq.-(12) SIRK error bound of `ChapterH4.sirk_error_bound_decay`, as an
explicit function of the Krylov dimension `m`. -/
def sirkBound (C Dmin h nv : ℝ) (m : ℕ) : ℝ :=
  2 * C * Real.exp (-(h * m)) * Dmin * nv







/-! ## Rayleigh–Ritz: the compression retains spectrum -/

section RayleighRitz

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open BookProof.ChapterH4





end RayleighRitz

/-! ## The reduced generator is an explicit `m × m` matrix -/

section Reduced

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open BookProof.ChapterH4

/-- The **reduced generator** `H̄_reduced = Vᴴ H̄ V` as an explicit `m × m`
matrix of inner products. -/
def reduceGenerator (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] E) (X : E →L[ℂ] E) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j =>
    inner ℂ (V (EuclideanSpace.single i (1 : ℂ))) (X (V (EuclideanSpace.single j (1 : ℂ))))





end Reduced

/-! ## Generation as a single matrix exponential -/

section Generation

variable {m : ℕ}

/-- The generated state at time `t`: a *single* exponential of the reduced
generator, `Ψ(t) = e^{−i t H̄_reduced} Ψ₀`. -/
def generatedState (A : Matrix (Fin m) (Fin m) ℂ) (t : ℂ)
    (psi0 : Fin m → ℂ) : Fin m → ℂ :=
  (NormedSpace.exp ((-Complex.I * t) • A)).mulVec psi0







end Generation

end BookProof.ChapterH6

end


