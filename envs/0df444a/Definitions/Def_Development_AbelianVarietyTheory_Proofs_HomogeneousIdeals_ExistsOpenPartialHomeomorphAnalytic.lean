-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:39.765832+00:00
-- url     : https://prove2.me/theorems/cfe55e4a-c66d-442a-8c77-a71794c6d774
-- title:
--   Exists Open Partial Homeomorph Analytic
-- statement:
--   Definitions and structural lemmas for Exists Open Partial Homeomorph Analytic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
end GlobalTheory.AffinePoints


