-- Prove2me | solution 1 for AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c5fa362d-2680-5616-837e-a5b9a7af7a3c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {σ : Type u} (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsSeparated (f i)) : IsSeparated (Sigma.desc f) := by

  constructor
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover X) (sigmaOpenCover X) (Sigma.desc f) (Sigma.desc f)) ?_
  rintro ⟨i, j⟩
  have H := pullback_map_diagonal_isPullback (Sigma.ι X i) (Sigma.ι X j) (Sigma.desc f)
  show IsClosedImmersion (pullback.snd (pullback.diagonal (Sigma.desc f))
    (pullback.map (Sigma.ι X i ≫ Sigma.desc f) (Sigma.ι X j ≫ Sigma.desc f) (Sigma.desc f) (Sigma.desc f)
      (Sigma.ι X i) (Sigma.ι X j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  by_cases hij : i = j
  · subst hij
    have hfi : Sigma.ι X i ≫ Sigma.desc f = f i := Sigma.ι_desc _ _
    haveI : IsSeparated (Sigma.ι X i ≫ Sigma.desc f) := by rw [hfi]; exact hf i
    haveI : IsClosedImmersion
        (pullback.fst (Sigma.ι X i) (Sigma.ι X i) ≫ pullback.diagonal (Sigma.ι X i ≫ Sigma.desc f)) :=
      inferInstance
    convert this using 2
    apply pullback.hom_ext <;> simp [fst_eq_snd_of_mono_eq]
  · haveI : IsEmpty ↑(pullback (Sigma.ι X i) (Sigma.ι X j)) := isEmpty_pullback_sigmaι_of_ne X hij
    infer_instance

end S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated (solution)
