-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PExactSequence
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PExactSequence
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:49.496848+00:00
-- url     : https://prove2.me/theorems/8cd6b295-3cbe-5cad-b729-c45c542dd3fc
-- title:
--   PExact Sequence
-- statement:
--   Definitions and structural lemmas for PExact Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PExactSequence.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
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
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
theorem quotFibreMap_mkQ_of_orthogonal (σ : K →+* ℂ) (x : Fibre σ M.carrier)
    (hx : FibreSpace.equiv M.metric σ x ∈ (subFibre M.metric σ F)ᗮ) :
    quotFibreMap M F hF σ (fibreMap σ F.mkQ x) = FibreSpace.equiv M.metric σ x := by
  have := quot_projective hF
  set V := subFibre M.metric σ F
  set z := fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x) - x with hzdef
  have hex := lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F) F.mkQ_surjective
  have h0 : F.mkQ.lTensor (ComplexAt σ) z = 0 := by
    change fibreMap σ F.mkQ z = 0
    rw [hzdef, map_sub, fibreMap_fibreMap, fibreMap_fibreMap,
      mkQ_comp_quotSection, LinearMap.id_comp, sub_self]
  obtain ⟨y, hy⟩ := (hex z).mp h0
  have hz : FibreSpace.equiv M.metric σ z ∈ V := ⟨y, congrArg (FibreSpace.equiv M.metric σ) hy⟩
  have hsplit : FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x)) =
      FibreSpace.equiv M.metric σ x + FibreSpace.equiv M.metric σ z := by
    rw [hzdef, map_sub]
    abel
  change Vᗮ.starProjection
      (FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x))) = _
  rw [hsplit, map_add, Submodule.starProjection_orthogonal_apply_eq_zero hz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hx]
def subQuotExtension : HermitianExtension (M.sub F) M (M.quot F hF) where
  incl := F.subtype
  proj := F.mkQ
  incl_injective := F.injective_subtype
  proj_surjective := F.mkQ_surjective
  exact := LinearMap.exact_subtype_mkQ F
  incl_isometric _ _ _ := rfl
  proj_coisometric σ x y hx hy := by
    have hmem : ∀ z : Fibre σ M.carrier,
        (∀ w, (M.metric.form σ).inner (F.subtype.lTensor (ComplexAt σ) w) z = 0) →
          FibreSpace.equiv M.metric σ z ∈ (subFibre M.metric σ F)ᗮ := by
      intro z hz
      rw [Submodule.mem_orthogonal]
      rintro u ⟨w, rfl⟩
      exact hz w
    change inner ℂ (quotFibreMap M F hF σ (fibreMap σ F.mkQ x))
      (quotFibreMap M F hF σ (fibreMap σ F.mkQ y)) = _
    rw [quotFibreMap_mkQ_of_orthogonal M F hF σ x (hmem x hx),
      quotFibreMap_mkQ_of_orthogonal M F hF σ y (hmem y hy)]
    rfl
end HermitianBundle
namespace LatticeLemmas
end LatticeLemmas
end
end GroundTheory.Heights₂.Heights


