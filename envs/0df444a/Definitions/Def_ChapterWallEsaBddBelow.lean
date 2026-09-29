-- Prove2me | Definitions.Def_ChapterWallEsaBddBelow
-- name    : ChapterWallEsaBddBelow
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-18T12:19:51.199415+00:00
-- url     : https://prove2.me/theorems/9fbbdf52-ed8f-4df9-af70-c851176b80a8

import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterKatoRellichDeficiency
import Mathlib


/-!
# `−d²/dx² + V` for every smooth potential that is bounded below

`BookProof/ChapterScalaronWallEsa.lean` proves that `−d²/dx² + V` is essentially
self-adjoint on the compactly supported smooth core of `L²(ℝ)` for every smooth
**non-negative** potential — with no growth restriction, so in particular for the
exponentially growing Einstein-frame scalaron wall.

The non-negativity in that statement is not a real restriction: a *constant* is a bounded
symmetric perturbation, and bounded symmetric perturbations preserve essential
self-adjointness (`BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded`).  This
module performs the shift and records the consequences:

* `wallHam_add_const` — the operator identity `wallHam (V + c) = wallHam V + c`;
* **`wallHam_essentiallySelfAdjoint_of_bddBelow`** — `−d²/dx² + V` is essentially
  self-adjoint on the compactly supported smooth core for every smooth `V` bounded below,
  again with no growth restriction above;
* `wallHam_stone_flow_of_bddBelow` — the resulting unitary group `e^{−itH}`;
* the semiboundedness the Hashimoto/SIRK shift-invert scheme needs is carried by the
  shift itself: the quadratic form of `wallHam V hV` is bounded below by `-c` whenever
  `V ≥ -c`, so the closed operator selected by the closure is the semibounded one the
  scheme works with; the packaging lemma `wallHamBddBelow_semibounded` that makes this
  precise is proved in `BookProof/ChapterWallEsaSemibounded.lean`;
* the physical instances: the scalaron wall plus an arbitrary bounded-below smooth
  addition (`scalaronPlus_esa`), and the harmonic-oscillator sum
  `−d²/dx² + x²/4 + V` (`oscillatorPlus_esa`).
-/

namespace BookProof.WallEsaBddBelow

open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

noncomputable section

/-- Multiplication by a real constant, as a bounded operator on `L²(ℝ)`. -/
def constOp (c : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ((c : ℂ)) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))









/-! ## Instances -/





end

end BookProof.WallEsaBddBelow


