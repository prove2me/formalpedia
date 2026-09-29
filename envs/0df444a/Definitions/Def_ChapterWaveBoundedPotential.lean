-- Prove2me | Definitions.Def_ChapterWaveBoundedPotential
-- name    : ChapterWaveBoundedPotential
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:47:19.993374+00:00
-- url     : https://prove2.me/theorems/9f6b647e-532d-41ec-b2d8-92064995a096
-- title:
--   Combining
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.WaveBoundedPotential`, source chapter `BookProof/ChapterWaveBoundedPotential.lean`).
--
--   Combining
--
--   * `BookProof.StrichartzWave.wave_essentiallySelfAdjoint` — essential self-adjointness of the free wave operator `□` on the Schwartz core of `L²(ℝ^{1+n})`, proved by the Fourier-multiplier argument, and * `BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded` — the Kato–Rellich theorem for bounded symmetric perturbations, proved by an explicit Neumann series,
--
--   we obtain the Strichartz-type statement for the wave operator with a **potential**:
--
--   > For every real-valued, essentially bounded `V` on spacetime, the operator `□ + V` is > essentially self-adjoint on the Schwartz core of `L²(ℝ^{1+n})`.
--
--   The potential enters as the multiplication operator `mulL2`, which is bounded on `L²` by Hölder's inequality (`ContinuousLinearMap.holderL` with the exponent triple `(∞, 2, 2)`) and symmetric exactly when the multiplier is real almost everywhere.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWaveBoundedPotential.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib

import Mathlib

/-!
# The wave operator with a bounded potential

Combining

* `BookProof.StrichartzWave.wave_essentiallySelfAdjoint` — essential self-adjointness of the
  free wave operator `□` on the Schwartz core of `L²(ℝ^{1+n})`, proved by the
  Fourier-multiplier argument, and
* `BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded` — the Kato–Rellich theorem for
  bounded symmetric perturbations, proved by an explicit Neumann series,

we obtain the Strichartz-type statement for the wave operator with a **potential**:

> For every real-valued, essentially bounded `V` on spacetime, the operator `□ + V` is
> essentially self-adjoint on the Schwartz core of `L²(ℝ^{1+n})`.

The potential enters as the multiplication operator `mulL2`, which is bounded on `L²` by
Hölder's inequality (`ContinuousLinearMap.holderL` with the exponent triple `(∞, 2, 2)`) and
symmetric exactly when the multiplier is real almost everywhere.
-/

namespace BookProof.StrichartzWave

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Multiplication by an essentially bounded function, as a bounded operator on `L²`. -/
noncomputable def mulL2 (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) :
    Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure V) (⊤ : ℝ≥0∞) 2 2 W









end BookProof.StrichartzWave


