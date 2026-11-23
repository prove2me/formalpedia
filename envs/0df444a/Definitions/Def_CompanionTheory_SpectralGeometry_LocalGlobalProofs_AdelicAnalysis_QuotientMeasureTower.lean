-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:52.674407+00:00
-- url     : https://prove2.me/theorems/28ae7f83-0496-4339-98af-e2fee3daf7ea
-- title:
--   Quotient Measure Tower
-- statement:
--   Definitions and structural lemmas for Quotient Measure Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasureStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.Averaging
section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
end
end GlobalTheory.CompanionTheory.SW.Averaging


