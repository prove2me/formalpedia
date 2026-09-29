-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5846da66-5d67-561e-a6c6-2ee5d54b5490

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "fibreAt fibreModule"
namespace TransportGen
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
  (hcart : IsPullback g' y (pullback.snd c t) s)

def φ : pullback (pullback.snd c t) s ≅ Y := hcart.isoPullback.symm

theorem φ_hom_y : (φ c t s y g' hcart).hom ≫ y = fibreAt c t s := by
  rw [φ, Iso.symm_hom, IsPullback.isoPullback_inv_snd]
  rfl

def modIso : fibreModule c t s M ≅ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).obj ((Scheme.Modules.pullback g').obj M) :=
  (Scheme.Modules.pullbackCongr (hcart.isoPullback_inv_fst).symm).app M ≪≫
    (Scheme.Modules.pullbackComp (φ c t s y g' hcart).hom g').symm.app M

include hcart in
theorem main (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) := by
  obtain ⟨𝒲, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) y (φ c t s y g' hcart) (φ_hom_y c t s y g' hcart)
    𝒱 F (fibreModule c t s M)
    (modIso c t M s y g' hcart ≪≫ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).mapIso e.symm)
  exact ⟨𝒲, ⟨eH0.symm⟩, ⟨eH1.symm⟩⟩

end AlgebraicGeometry.RelPicard.TransportGen

end

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
    (hcart : IsPullback g' y (pullback.snd c t) s)
    (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) :=
  AlgebraicGeometry.RelPicard.TransportGen.main c t M s y g' hcart F e 𝒱

end S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback (solution)
