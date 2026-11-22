-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
-- name    : Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:00.999281+00:00
-- url     : https://prove2.me/theorems/7619b97e-7117-40fe-b8d3-f5d0af7ae1a0
-- title:
--   Succ Min
-- statement:
--   Definitions and structural lemmas for Succ Min, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
namespace Formalism.FN.SuccessiveMinima
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] {K : Set E}
end Formalism.FN.SuccessiveMinima


