-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:14.713204+00:00
-- url     : https://prove2.me/theorems/50ad588f-c706-45be-a76b-b0cadafaee3c
-- title:
--   St Flat Local Regular Element
-- statement:
--   Definitions and structural lemmas for St Flat Local Regular Element, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFlatLocalRegularElement.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatDimFormula
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
open IsLocalRing
def FlatLocalRegularElement.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M],
      Module.Finite B M → Module.Flat A M →
      ∀ y ∈ maximalIdeal B,
        IsSMulRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) y →
        IsSMulRegular M y ∧ Module.Flat A (QuotSMulTop y M)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


