-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono
-- name    : Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:57.198267+00:00
-- url     : https://prove2.me/theorems/48d37d14-c9f5-404e-aec4-6fce0745f6ee
-- title:
--   Dominance Mono
-- statement:
--   Definitions and structural lemmas for Dominance Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/DominanceMono.lean

import Definitions.Def_Formalism_ThetaSupremumBounds_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.DimensionVariation
def ext0 {r : ℕ} (f : Fin r → ℝ) (i : ℕ) : ℝ := if h : i < r then f ⟨i, h⟩ else 0
end Formalism.DimensionVariation


