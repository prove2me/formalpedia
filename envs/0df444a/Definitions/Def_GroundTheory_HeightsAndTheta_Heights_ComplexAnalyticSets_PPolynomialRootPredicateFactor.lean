-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.1088+00:00
-- url     : https://prove2.me/theorems/c7c0c1c0-1bfb-47e0-96c7-f5ddc7c68a5d
-- title:
--   PPolynomial Root Predicate Factor
-- statement:
--   Definitions and structural lemmas for PPolynomial Root Predicate Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
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
open Polynomial Filter Topology Classical
namespace PolynomialRootPredicateFactor
noncomputable def fiberPoly {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) : ℂ[X] :=
  X ^ N + ∑ j, C (a j t) * X ^ (j : ℕ)
noncomputable def rootFactor (p : ℂ[X]) (Q : ℂ → Prop) : ℂ[X] :=
  ((p.roots.filter Q).map fun τ => X - C τ).prod
end PolynomialRootPredicateFactor
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


