-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicZeroSetDimH
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicZeroSetDimH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:57.475808+00:00
-- url     : https://prove2.me/theorems/ea96828e-d84a-4636-8cd5-b49f7f4ce78c
-- title:
--   PHolomorphic Zero Set Dim H
-- statement:
--   Definitions and structural lemmas for PHolomorphic Zero Set Dim H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
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
open Topology Metric Filter
open scoped ENNReal NNReal
noncomputable section
namespace HolomorphicZeroSetDimH
def partialDeriv {k : ℕ} (h : (Fin k → ℂ) → ℂ) (n : ℕ) (m : Fin n → Fin k) (v : Fin k → ℂ) : ℂ :=
  iteratedFDeriv ℂ n h v (fun j => Pi.basisFun ℂ (Fin k) (m j))
end HolomorphicZeroSetDimH
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


