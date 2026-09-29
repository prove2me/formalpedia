-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0a794216-cb0f-5b70-bca4-a4a67a92ee56

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (K : Type u) [Field K] [Algebra k K]
    (hK : ∀ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      Subsingleton (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
        (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) M)).H1) :
    ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by
  intro 𝒲
  obtain ⟨𝒲', -, hiff⟩ :=
    AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff c t M hM s 𝒲 K
  exact hiff.mp (hK 𝒲')

end S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension (solution)
