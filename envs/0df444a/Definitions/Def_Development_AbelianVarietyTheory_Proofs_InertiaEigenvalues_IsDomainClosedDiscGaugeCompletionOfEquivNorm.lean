-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsDomainClosedDiscGaugeCompletionOfEquivNorm
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsDomainClosedDiscGaugeCompletionOfEquivNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:55.559704+00:00
-- url     : https://prove2.me/theorems/106b93ff-15ee-400e-9431-9b665bd14dd9
-- title:
--   Is Domain Closed Disc Gauge Completion Of Equiv Norm
-- statement:
--   Definitions and structural lemmas for Is Domain Closed Disc Gauge Completion Of Equiv Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
namespace GlobalTheory.BSP.DiscDomain
variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}
end GlobalTheory.BSP.DiscDomain


