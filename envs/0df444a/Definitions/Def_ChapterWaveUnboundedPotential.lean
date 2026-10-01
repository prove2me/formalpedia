-- Prove2me | Definitions.Def_ChapterWaveUnboundedPotential
-- name    : ChapterWaveUnboundedPotential
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:49:54.508004+00:00
-- url     : https://prove2.me/theorems/05659434-08f2-48a9-b42b-a5fba5c26cb7
-- title:
--   Chapter WaveUnboundedPotential
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWaveUnboundedPotential.lean`): generated def bundle for ChapterWaveUnboundedPotential. See BookProof/ChapterWaveUnboundedPotential.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWaveUnboundedPotential.lean

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveBoundedPotential
import Mathlib


/-!
# Unbounded (polynomial) potentials: what is proved, and where the obstruction lies

`BookProof.ChapterWaveBoundedPotential` proves `□ + V` essentially self-adjoint on the
Schwartz core of `L²(ℝ^{1+n})` for a real **essentially bounded** `V`.  The next target
recorded in `CONSOLIDATED_PLAN.md` §9.5 is the unbounded case: a potential which is a
polynomial (hence unbounded) but bounded below, via the three steps

> (a) localize with `exists_smooth_cutoff`, so that on each ball the truncated potential is
> essentially bounded; (b) apply `wave_add_potential_essentiallySelfAdjoint` to each
> truncation; (c) pass to the limit `R → ∞`.

This module carries out (a) and (b) unconditionally, adds the unbounded-potential theorem
that the *potential alone* is essentially self-adjoint, and states precisely what (c) needs.

## Contents

* **Multiplication by an unbounded potential.**  `potentialOp W` is multiplication by a real
  function `W` of temperate growth — every polynomial qualifies, so the operator is
  genuinely unbounded.  `potentialOp_symmetric` and `potentialOp_essentiallySelfAdjoint`
  show that it is symmetric and essentially self-adjoint on the Schwartz core, with **no**
  boundedness and **no** semiboundedness hypothesis.  The proof is the position-space twin
  of the Fourier-multiplier argument of `ChapterStrichartzWave`: a deficiency vector `u`
  satisfies `∫ conj ψ · (W - z) · u = 0` for every Schwartz `ψ`, and dividing a smooth
  compactly supported `χ` by the nowhere-vanishing smooth function `W - z̄` produces such a
  `ψ` with `conj ψ · (W - z) = χ`, whence `u = 0`.
  `polynomialPotential_essentiallySelfAdjoint` is the special case `W x = ‖x‖^(2k)`, an
  unbounded polynomial potential which is bounded below.

* **The operator `□ + W` for an unbounded `W`.**  It is well defined on the Schwartz core
  (Schwartz space is invariant under multiplication by a temperate function) and symmetric:
  `wave_add_potentialOp_symmetric`.  This is the precise Lean statement of the target
  operator of §9.5.

* **Steps (a)+(b): localization.**  `opL2_potentialOp_eq_mulL2` identifies the
  multiplication operator of this module with the bounded `mulL2` of
  `ChapterWaveBoundedPotential` whenever the potential is essentially bounded, so the
  bounded theorem applies verbatim to the truncations:
  `wave_add_boundedPotentialOp_essentiallySelfAdjoint` and, for a potential of temperate
  growth cut off at radius `R`, `wave_add_truncatedPotential_essentiallySelfAdjoint` —
  for every `R` there is a `W_R` of temperate growth, agreeing with `W` on the ball of
  radius `R`, with `□ + W_R` essentially self-adjoint on the Schwartz core.

* **Step (c): the residue, and a sign warning.**  Passing from the truncations to `□ + W`
  is not a formal limit, and the failure is not merely technical.  With the sign convention
  of this project (`□ = -∂_t² + Δ_x`), a Fourier transform in the time variable turns
  `□ + W` (for `W` a function of the space variables) into the fibre operators
  `4π²τ² - (-Δ_x - W)`.  A potential **bounded below** therefore makes the fibre Schrödinger
  operator `-Δ_x - W` unbounded **below**, which is exactly the limit-circle regime where
  essential self-adjointness fails (`-d²/dx² - x⁴` has deficiency indices `(2,2)`).  The
  sign under which the localization argument can close is the opposite one: `W` bounded
  *above* for `□ = -∂_t² + Δ_x`, equivalently `W` bounded below for the opposite-signature
  convention `□ = ∂_t² - Δ_x` used in the physics literature.  Nothing here claims the
  unbounded case; the theorems below are exactly the unconditional part.
-/

namespace BookProof.StrichartzWave

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ## Multiplication by an unbounded real potential -/

/-- Multiplication by a real potential `W`, as an operator on Schwartz space.  The operator
is well defined (Schwartz space is invariant) as soon as `W` has temperate growth, which
holds for every polynomial; no boundedness is required. -/
noncomputable def potentialOp (W : V → ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (W x : ℂ))















/-! ## The operator `□ + W` for an unbounded potential -/





/-! ## The dual statement: arbitrary real Fourier multipliers

The potential theorem above is the position-space half of the picture.  Conjugating it with
the Fourier transform gives the momentum-space half: *every* real symbol of temperate growth
— not just the quadratic symbols of `constCoeffOp` — defines an essentially self-adjoint
operator on the Schwartz core.  This covers all constant-coefficient differential operators
with real symbol of any order, for instance `□²` and the polyharmonic operators `(-Δ)^k`. -/

/-- The Fourier multiplier with symbol `m`, as an operator on Schwartz space. -/
noncomputable def multiplierOp (m : V → ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).symm.toContinuousLinearMap ∘L potentialOp m ∘L
    (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).toContinuousLinearMap













section ConstCoeff

variable {ι : Type*} [Fintype ι]





end ConstCoeff



/-! ## Localization: the truncated potential -/











end BookProof.StrichartzWave


