-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularSequence
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularSequence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:48.332177+00:00
-- url     : https://prove2.me/theorems/e3625a6b-f1b3-4748-8610-7fa0ff60b7c8
-- title:
--   PFlat Local Regular Sequence
-- statement:
--   Definitions and structural lemmas for PFlat Local Regular Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularSequence.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
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
open IsLocalRing RingTheory.Sequence Pointwise
def quotSMulTopQuotIdealSMulTopEquiv {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (I : Ideal B) (y : B) :
    QuotSMulTop y (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B]
      (QuotSMulTop y M ⧸ (I • ⊤ : Submodule B (QuotSMulTop y M))) :=
  (Submodule.quotEquivOfEq ((y • (⊤ : Submodule B M)).map (I • (⊤ : Submodule B M)).mkQ) (y • ⊤)
      (by rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).symm ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup (I • ⊤) (y • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm _ _) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup (y • ⊤) (I • ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


