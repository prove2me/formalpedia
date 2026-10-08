-- Prove2me | Definitions.Def_ChapterHarmonicOscillatorEsa
-- name    : ChapterHarmonicOscillatorEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T17:33:27.699875+00:00
-- url     : https://prove2.me/theorems/a9d3363a-0182-4be8-aac8-2fa557f8c450
-- title:
--   Chapter HarmonicOscillatorEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHarmonicOscillatorEsa.lean`): generated def bundle for ChapterHarmonicOscillatorEsa. See BookProof/ChapterHarmonicOscillatorEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHarmonicOscillatorEsa.lean

import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterA4
import Mathlib


/-!
# The harmonic oscillator: a differential operator with an unbounded polynomial potential

`BookProof.ChapterWaveUnboundedPotential` settles the two *commuting* halves of the
"unbounded potential" problem on the Schwartz core of `L²`: an arbitrary real potential of
temperate growth is essentially self-adjoint, and so is an arbitrary real Fourier multiplier.
What those results do not reach is the genuine mixture — a differential kinetic term *plus* a
non-constant unbounded potential, which do not commute.

This module proves the prototypical mixed case, where an explicit joint eigenbasis exists:

> the harmonic oscillator `H = -d²/dx² + x²/4` is essentially self-adjoint on the Hermite
> core of `L²(ℝ)`,

with `x²/4` an unbounded polynomial potential.  The ingredients are already in the project:

* `BookProof.ChapterHermiteFunctions` constructs the Hermite orthonormal basis `hermiteLp` of
  `L²(ℝ)` and proves the eigenvalue equation `hermiteFun_oscillator`,
  `-ψ_n'' + (x²/4) ψ_n = (n + ½) ψ_n`, for the *real* Hermite functions;
* `BookProof.ChapterStrichartzHermiteQG` proves that a diagonal operator with an arbitrary
  real symbol on the Hermite core is symmetric, has trivial deficiency at every non-real
  point, and hence is essentially self-adjoint (`hermiteCoreOp_essentiallySelfAdjoint`).

What is added here is the *identification*: the diagonal operator with symbol `n + ½` really
is the differential operator `-d²/dx² + x²/4` — `harmonicOscOp_apply_eq_differential` states
that its value on the `n`-th basis vector is the `L²` class of
`x ↦ -(ψ_n)''(x) + (x²/4) ψ_n(x)`, computed with Mathlib's `deriv`.  The conclusions are
`harmonicOsc_essentiallySelfAdjoint` and `harmonicOscOp_not_bounded`: the operator is
essentially self-adjoint on the core, and genuinely unbounded.

This is the elliptic (Sears-class) prototype of the target of `CONSOLIDATED_PLAN.md` §9.5;
the hyperbolic case still needs the fibrewise argument recorded there.
-/

namespace BookProof.HarmonicOscillator

open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

/-! ## Derivatives of the complexified Hermite functions -/

/-- The complexification of "polynomial times half Gaussian". -/
noncomputable def polyGaussC (p : Polynomial ℝ) : ℝ → ℂ :=
  fun x => ((p.eval x * gaussH x : ℝ) : ℂ)













/-! ## The harmonic oscillator on the Hermite core -/

/-- The symbol of the harmonic oscillator: the eigenvalues `n + ½`. -/
noncomputable def harmonicSymbol : ℕ → ℝ := fun n => (n : ℝ) + 1 / 2

/-- **The harmonic oscillator `-d²/dx² + x²/4` on the Hermite core of `L²(ℝ)`**, defined as
the diagonal operator with the eigenvalues `n + ½`; the identification with the differential
expression is `harmonicOscOp_apply_eq_differential`. -/
noncomputable def harmonicOscOp : hermiteCore →ₗ[ℂ] L2R := hermiteCoreOp harmonicSymbol













end BookProof.HarmonicOscillator


