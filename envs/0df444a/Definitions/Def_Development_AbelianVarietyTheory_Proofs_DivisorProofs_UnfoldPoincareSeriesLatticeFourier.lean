-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldPoincareSeriesLatticeFourier
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldPoincareSeriesLatticeFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:01.28118+00:00
-- url     : https://prove2.me/theorems/277bf5d9-3e07-43f4-bc37-7b9a3dccd52a
-- title:
--   Unfold Poincare Series Lattice Fourier
-- statement:
--   Definitions and structural lemmas for Unfold Poincare Series Lattice Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnfoldPoincareSeriesLatticeFourier.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.PoincareUnfold
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]
end GlobalTheory.PoincareUnfold


