-- Prove2me | solution 1 for AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7cb0eac3-8c24-56b3-bea6-d240ae61e4c3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {S R : Type} [CommRing S] [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by
  have hg : IsPullback (pullback.fst f σ) (pullback.snd f σ) f σ := IsPullback.of_hasPullback f σ
  have s₁ : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ)) (pullback.fst (pullback.snd f σ) (pullback.snd f σ))
      (pullback.snd f σ) (pullback.snd f σ) := (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rw [hg.w]
    exact s₁.paste_horiz hg
  have s' : IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]) ≫ pullback.snd f f)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rwa [pullback.lift_snd]
  have step1 := IsPullback.of_right s' (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip
  exact step1.paste_vert hg

end S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
end P2MW
export P2MW.S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr (solution)
