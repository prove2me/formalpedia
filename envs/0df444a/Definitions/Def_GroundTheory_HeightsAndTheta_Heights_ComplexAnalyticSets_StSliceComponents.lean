-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:54.546187+00:00
-- url     : https://prove2.me/theorems/7bdb51bb-da03-4dcd-ae12-e20ed8047f6e
-- title:
--   St Slice Components
-- statement:
--   Definitions and structural lemmas for St Slice Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def SliceComponents.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u ℓ : Fin n → ℂ),
    IsProjPrime J → (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      Set.InjOn (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) ((divCycle J u).support : Set _) ∧
        (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) '' ((divCycle J u).support : Set _) =
          (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes ∧
        ∀ W ∈ (divCycle J u).support,
          localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
              (W ⊔ Ideal.span {linForm ℓ - 1}) = divCycle J u W
end
end GroundTheory.Heights₂.Heights


