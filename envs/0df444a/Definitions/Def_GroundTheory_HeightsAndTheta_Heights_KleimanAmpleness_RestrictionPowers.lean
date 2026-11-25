-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:05.787563+00:00
-- url     : https://prove2.me/theorems/19b4ee61-a261-489e-a2d5-ba76c8647d1f
-- title:
--   Restriction Powers
-- statement:
--   Definitions and structural lemmas for Restriction Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
section AmpleChart
variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}
end AmpleChart
variable (x) in

def resUnionChart (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
end
end GroundTheory.Heights₂.Heights.Kleiman


