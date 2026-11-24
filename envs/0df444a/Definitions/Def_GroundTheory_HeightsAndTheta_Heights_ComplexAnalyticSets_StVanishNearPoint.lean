-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:00.98812+00:00
-- url     : https://prove2.me/theorems/e9a7f850-cdab-4671-bd12-6077853dcf1e
-- title:
--   St Vanish Near Point
-- statement:
--   Definitions and structural lemmas for St Vanish Near Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVanishNearPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
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
open MvPolynomial Filter Topology
noncomputable section
def VanishNearPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    J.IsPrime → x ∈ zeroLocus J → (∀ᶠ y in 𝓝 x, y ∈ zeroLocus J → eval y f = 0) → f ∈ J
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


