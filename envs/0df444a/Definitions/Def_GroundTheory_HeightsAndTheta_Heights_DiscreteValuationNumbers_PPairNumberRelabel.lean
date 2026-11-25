-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:26:26.607414+00:00
-- url     : https://prove2.me/theorems/f55104d3-1771-59db-b6cf-35b486c0f45c
-- title:
--   PPair Number Relabel
-- statement:
--   Definitions and structural lemmas for PPair Number Relabel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
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
noncomputable section
namespace PairNumberRelabel
section Ring
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
abbrev ren : MRing ι₁ R ≃+* MRing ι₂ R := (renameEquiv R σ).toRingEquiv
def idealEquiv : Ideal (MRing ι₁ R) ≃ Ideal (MRing ι₂ R) where
  toFun W := W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)
  invFun W := W.map ((ren (R := R) σ).symm : MRing ι₂ R →+* MRing ι₁ R)
  left_inv W := Ideal.map_of_equiv (I := W) (ren (R := R) σ)
  right_inv W := by
    have := Ideal.map_of_equiv (I := W) (ren (R := R) σ).symm
    rwa [RingEquiv.symm_symm] at this
variable (e : K₁ ≃ K₂)
end Ring
section Numbers
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Numbers
section DVR
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
end DVR
end PairNumberRelabel
end
end GroundTheory.Heights₂.Heights.NumbersDVR


