-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:14.604448+00:00
-- url     : https://prove2.me/theorems/bab0c9d2-cc45-4dc3-9f24-2c29a65d9e77
-- title:
--   Integrable Mul Bc
-- statement:
--   Definitions and structural lemmas for Integrable Mul Bc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/IntegrableMulBc.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal
noncomputable section
namespace CompanionTheory.D.gk.RF
section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
def eI (r : ℝ) : ℂ := Complex.exp ((r : ℂ) * Complex.I)
end
end CompanionTheory.D.gk.RF


