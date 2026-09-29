-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/48bf1edd-ec0b-5d56-a680-f6c5a2198f4b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (F : (pullback c t).Modules)
    (hF : Scheme.Modules.IsInvertible F)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (K : Type u) [Field K] [Algebra k K] :
    ∃ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s)) (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H0 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 ∧
      (Subsingleton (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s)) (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H1 ↔
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1) := by

  have hM : Scheme.Modules.IsInvertible (fibreModule c t s F) := hF.pullback _
  obtain ⟨h0, h1⟩ := Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
    (fibreAt c t s) 𝒲 (fibreModule c t s F) hM.1 K

  let ψ : pullback (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) ≅ pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) :=
    pullbackLeftPullbackSndIso (pullback.snd c t) s (Scheme.TwoAffineOpenCover.specMap k K)
  let φ : pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≅ pullback (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) := ψ.symm
  have hφx : φ.hom ≫ pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) = fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) := by
    change ψ.inv ≫ pullback.snd (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.snd (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  have hφfst : φ.hom ≫ pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) := by
    change ψ.inv ≫ pullback.fst (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm
  let e : fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F ≅ (Scheme.Modules.pullback φ.hom).obj
      ((Scheme.Modules.pullback (pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K))).obj (fibreModule c t s F)) :=
    ((Scheme.Modules.pullbackCongr hφfst).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp (φ.hom ≫ pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K)) (pullback.fst (pullback.snd c t) s)).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp φ.hom (pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K))).app _).symm
  obtain ⟨𝒲', -, -, ⟨f0⟩, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s)) (pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K)) φ hφx
    (𝒲.pullback (fibreAt c t s) K) _ _ e
  exact ⟨𝒲', f0.finrank_eq.trans h0, f1.toEquiv.subsingleton_congr.trans h1⟩

end S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff (solution)
