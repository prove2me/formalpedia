-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:01.350398+00:00
-- url     : https://prove2.me/theorems/6dc8341f-b912-428b-9aad-334ba12b0cdc
-- title:
--   Imports More Further
-- statement:
--   Definitions and structural lemmas for Imports More Further, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsMoreFurther.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
def VerticalDivisorCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (ϖ : O)
    (b : K → ℤ) (f g : MRing ι O), Irreducible ϖ → IsMultiProjPrime P →
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g ↔ IsVerticalDivisor P ϖ b f g)
end GroundTheory.Heights₂.Heights.NumbersDVR


