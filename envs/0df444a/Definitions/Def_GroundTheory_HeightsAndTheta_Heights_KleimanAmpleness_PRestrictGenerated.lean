-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:59.726344+00:00
-- url     : https://prove2.me/theorems/d057d940-a985-5eb6-92ec-d48adfc62608
-- title:
--   PRestrict Generated
-- statement:
--   Definitions and structural lemmas for PRestrict Generated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
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
namespace RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
variable (y) in

def toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) : Chart y :=
  ⟨I.1, I.2.1, fun i hi => (mem_support y).mpr (h i hi)⟩
end RestrictGenerated
end
end GroundTheory.Heights₂.Heights.Kleiman


