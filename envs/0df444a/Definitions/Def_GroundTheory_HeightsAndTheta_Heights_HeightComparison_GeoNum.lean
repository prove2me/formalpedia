-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:46.508014+00:00
-- url     : https://prove2.me/theorems/ec8a9d68-b5b7-59af-b6fe-cb2537529122
-- title:
--   Geo Num
-- statement:
--   Definitions and structural lemmas for Geo Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace GeoNum
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]
abbrev red : MRing ι ℤ →+* MRing ι (ZMod p) := MvPolynomial.map (Int.castRingHom (ZMod p))
theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ ZMod.intCast_surjective
def quotEquiv (J' : Ideal (MRing ι (ZMod p))) :
    (MRing ι ℤ ⧸ J'.comap (red p)) ≃+* (MRing ι (ZMod p) ⧸ J') :=
  (Ideal.quotEquivOfEq (by rw [← RingHom.comap_ker, Ideal.mk_ker])).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk J').comp (red p))
      (Ideal.Quotient.mk_surjective.comp (red_surjective p)))
end GeoNum
end
end GroundTheory.Heights₂.Heights.Bridge


