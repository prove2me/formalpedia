-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d9d46c89-11a8-59c9-aa87-d485d194fcaf

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

universe u

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε h h'))).L ≅
      Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)) := by

  have hM : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong a) :=
    (algEquivZeroCut c ε).pullback_mem _ _ a _ h.poincare_mem
  have ha : a = h.classify t _ hM := h.classify_unique t _ hM a ⟨Iso.refl _⟩

  have key := RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' t _ hM
  have hspec := h'.classify_spec t ((h.poincare.pullbackAlong a).pullbackCurve f hf hε)
    (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM)
  rw [← key, ← ha] at hspec

  obtain ⟨e₁⟩ := hspec
  obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
    (rigSection c' t ε') (pullback.snd c' t) _ ((h.poincare.pullbackAlong a).pullbackCurve f hf hε).rigidified
  exact ⟨e₁ ≪≫ e₂.symm⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify (solution)
