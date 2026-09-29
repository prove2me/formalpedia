-- Prove2me | solution 1 for AlgebraicGeometry.isPullback_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4e482553-30ca-5326-97ee-0fbc9a8a36f3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPullback_of_iSup_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace SIGMA2

theorem isPullback_of_iSup_eq_top {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
    IsPullback fst snd f g := by
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U hU
  refine Scheme.isPullback_of_openCover fst snd f g 𝒰 fun i => ?_

  refine (h i).of_iso' (pullbackRestrictIsoRestrict fst (U i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    exact pullbackRestrictIsoRestrict_hom_morphismRestrict fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact pullbackRestrictIsoRestrict_hom_ι fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end SIGMA2

theorem solution
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
    IsPullback fst snd f g :=
  SIGMA2.isPullback_of_iSup_eq_top fst snd f g U hU h

end S_AlgebraicGeometry_isPullback_of_iSup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_isPullback_of_iSup_eq_top (solution)
