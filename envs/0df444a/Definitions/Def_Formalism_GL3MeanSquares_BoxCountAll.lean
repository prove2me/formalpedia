-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_BoxCountAll
-- name    : Formalism_GL3MeanSquares_BoxCountAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:41.885579+00:00
-- url     : https://prove2.me/theorems/609c59b9-541d-4a91-8d5e-04368a422ad2
-- title:
--   Box Count All
-- statement:
--   Definitions and structural lemmas for Box Count All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/BoxCountAll.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.BoxCountUnconditional
def BoxCountAll : Prop :=
  ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C
end Formalism.HermitianLattices.BoxCountUnconditional


