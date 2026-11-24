-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:55.221854+00:00
-- url     : https://prove2.me/theorems/30ab1246-6cd1-4f5d-a469-6e2878073269
-- title:
--   PProper Holomorphic Surjective
-- statement:
--   Definitions and structural lemmas for PProper Holomorphic Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperHolomorphicSurjective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric MeasureTheory
open scoped ENNReal NNReal
namespace ProperHolomorphicSurjective
noncomputable def jac {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) : ℂ :=
  LinearMap.det (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
end ProperHolomorphicSurjective
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


