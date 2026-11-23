-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_ExistsAvg
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_ExistsAvg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:43.969795+00:00
-- url     : https://prove2.me/theorems/1829b803-158e-4961-993c-f3a365ebfacd
-- title:
--   Exists Avg
-- statement:
--   Definitions and structural lemmas for Exists Avg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/ExistsAvg.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.D.gk.admitted
section
variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}
end
end CompanionTheory.D.gk.admitted


