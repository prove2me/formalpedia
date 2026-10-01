-- Prove2me | Definitions.Def_ChapterE
-- name    : ChapterE
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:53:12.534576+00:00
-- url     : https://prove2.me/theorems/10f9c49a-8cd5-4ecb-afe5-4325662a834d
-- title:
--   Chapter E
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterE.lean`): generated def bundle for ChapterE. See BookProof/ChapterE.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterE.lean

import Mathlib


/-!
# Chapter E — Wave-function collapse versus Euler's formula

Formalization of the theorem-rich Chapter E of `book.tex`
(see `FORMALIZATION_ROADMAP.md` §E): the wave-function as a "multi-dimensional
Euler formula" parametrizing any probability distribution, with collapse =
"taking the real part."
-/

open scoped Matrix BigOperators
open Filter
open scoped Topology

namespace BookProof.ChapterE

/-! ## E.1 — The 2-state probability clock -/

/-- The 2-state wave function `Ψ t = (cos t, sin t)`. -/
noncomputable def Ψ (t : ℝ) : Fin 2 → ℝ := ![Real.cos t, Real.sin t]

/-- The rotation generator `J = [[0,-1],[1,0]]`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-
**E.1a (surjectivity of the Born map).** Every probability `p ∈ [0,1]` is
realized as `cos² t` for some angle `t`.
-/


/-
**E.1b (Euler rotation).** The matrix exponential of `t • J` is the rotation
matrix `[[cos t, -sin t],[sin t, cos t]]`.
-/


/-
**E.1b (rotation acts on the clock).** The rotation by `t` sends the initial
state `(1,0)` to `Ψ t`.
-/


/-
**E.1c (collapse = diagonal / real part).** The collapsed (diagonal) density
matrix of `Ψ t` is `½·I + ½cos(2t)·diag(1,-1)`.
-/


/-! ## E.2 — Probability-preserving linear maps -/

/-
**E.2b (uniform → vertex forces singularity).** A column-stochastic `2×2`
matrix that maps the uniform distribution `(½,½)` to the vertex `(1,0)` is
singular (`det = 0`); hence it is not an invertible symmetry.
-/


/-! ## E.3 — A unitary that uniformizes every basis state -/

/-
**E.3 (Hadamard, `n = 2`).** The normalized Hadamard matrix is unitary and
maps every basis state to the uniform Born distribution `|·|² = 1/2`.
-/


/-
**E.3 (general `n`).** For every `n ≥ 1` there is a unitary `n × n` matrix
that maps every computational basis state to the uniform Born distribution
`|·|² = 1/n` (the DFT / "black hole" uniformizer).
-/


/-! ## E.4 — Hyperspherical Born recursion onto the simplex -/

/-- The stick-breaking / hyperspherical Born map:
`Θ(θ)ₙ = (∏_{k<n} sin²θ_k)·cos²θ_n`. -/
noncomputable def stickBreaking {N : ℕ} (θ : Fin N → ℝ) (n : Fin N) : ℝ :=
    (∏ k ∈ Finset.Iio n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2

/-
**E.4 (surjectivity onto the simplex).** Every probability distribution `P`
on `Fin N` is realized by the hyperspherical Born recursion of a real unit
vector, i.e. the stick-breaking map is surjective onto the probability simplex.
-/


end BookProof.ChapterE


