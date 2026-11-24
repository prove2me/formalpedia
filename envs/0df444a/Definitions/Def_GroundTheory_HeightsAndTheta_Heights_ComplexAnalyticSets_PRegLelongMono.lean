-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongMono
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:30.021809+00:00
-- url     : https://prove2.me/theorems/cdd607cc-6b8c-46a7-9593-420b00bb5522
-- title:
--   PReg Lelong Mono
-- statement:
--   Definitions and structural lemmas for PReg Lelong Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongMono.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace RegLelongMono
variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}
end RegLelongMono
end
end GroundTheory.Heights₂.Heights


