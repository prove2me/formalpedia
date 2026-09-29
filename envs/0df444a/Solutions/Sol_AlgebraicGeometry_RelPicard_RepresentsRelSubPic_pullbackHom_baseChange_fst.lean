-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_baseChange_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/161ca2a3-a3fb-5177-88f3-7217d7c4e106

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "curveChange rigSection_curveChange curveChange_snd RepresentsRelSubPic.pullbackHom postComp RigidifiedLineBundle RepresentsRelSubPic algEquivZeroCut BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.overR BaseChange.toR BaseChange.ofR BaseChange.toR_ofR_iso BaseChange.toR_pullbackAlong_iso"
namespace BCAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (f : C' ⟶ C) (hf : f ≫ c = c') (R' : Type u) [CommRing R'] [Algebra R R']
  (hf' : curveChange f hf (specMap R R') ≫ baseChange R c R' = baseChange R c' R')

include hf' in

theorem κ_hom_curveChange {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ c' R' t').hom ≫ curveChange f hf (t' ≫ specMap R R') =
      curveChange (curveChange f hf (specMap R R')) hf' t' ≫ (BaseChange.κ c R' t').hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_fst]
    simp only [curveChange, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, BaseChange.κ_hom_fst, Category.assoc]
    simp only [Category.assoc, pullback.map, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_snd]
    simp only [curveChange, pullback.lift_snd, Category.comp_id]
    rw [BaseChange.κ_hom_snd]

include hf' in
theorem curveChange_κ_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    curveChange f hf (t' ≫ specMap R R') ≫ (BaseChange.κ c R' t').inv =
      (BaseChange.κ c' R' t').inv ≫ curveChange (curveChange f hf (specMap R R')) hf' t' := by
  rw [Iso.eq_inv_comp, ← Category.assoc, κ_hom_curveChange f hf R' hf', Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

noncomputable def toR_pullbackCurve_iso
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (hε : ε'.1 ≫ f = ε.1)
    (hεbc : (sectionBaseChange R' ε').1 ≫ curveChange f hf (specMap R R') = (sectionBaseChange R' ε).1)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (N : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    (BaseChange.toR c' ε' R' (N.pullbackCurve (curveChange f hf (specMap R R')) hf' hεbc)).L ≅
      ((BaseChange.toR c ε R' N).pullbackCurve f hf hε).L :=
  (Scheme.Modules.pullbackComp _ _).app N.L ≪≫
    (Scheme.Modules.pullbackCongr (curveChange_κ_inv f hf R' hf' t').symm).app N.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N.L).symm

end AlgebraicGeometry.RelPicard.BCAux

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (hR' : RepresentsRelSubPic (baseChange R c' R') (sectionBaseChange R' ε')
      (algEquivZeroCut (baseChange R c' R') (sectionBaseChange R' ε')) (D'.baseChange R'))
    (hPR' : Nonempty (hR'.poincare.L ≅ (BaseChange.ofR c' ε' R'
      (h'.poincare.pullbackAlong ⟨pullback.fst D'.toBase (specMap R R'), pullback.condition⟩)).L))
    (hf' : curveChange f hf (specMap R R') ≫ baseChange R c R' = baseChange R c' R')
    (hεbc : (sectionBaseChange R' ε').1 ≫ curveChange f hf (specMap R R') = (sectionBaseChange R' ε).1) :
    (RepresentsRelSubPic.pullbackHom (curveChange f hf (specMap R R')) hf' hεbc hR hR').1 ≫
        pullback.fst D'.toBase (specMap R R') =
      pullback.fst D.toBase (specMap R R') ≫ (RepresentsRelSubPic.pullbackHom f hf hε h h').1 := by

  let ψD : SchemeHomOver (pullback.snd D.toBase (specMap R R') ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let ψD' : SchemeHomOver (pullback.snd D'.toBase (specMap R R') ≫ specMap R R') D'.toBase :=
    ⟨pullback.fst D'.toBase (specMap R R'), pullback.condition⟩
  set fbc := RepresentsRelSubPic.pullbackHom (curveChange f hf (specMap R R')) hf' hεbc hR hR' with hfbc

  let x : SchemeHomOver (pullback.snd D.toBase (specMap R R') ≫ specMap R R') D'.toBase :=
    postComp ψD' (BaseChange.overR R' fbc)
  let y : SchemeHomOver (pullback.snd D.toBase (specMap R R') ≫ specMap R R') D'.toBase :=
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') ψD
  suffices hxy : x = y by
    have := congrArg Subtype.val hxy
    exact this
  refine h'.ext_of_iso _ x y ⟨?_⟩

  have eD' : (h'.poincare.pullbackAlong ψD').L ≅ (BaseChange.toR c' ε' R' hR'.poincare).L :=
    ((Scheme.Modules.pullback (BaseChange.κ c' R' _).inv).mapIso hPR'.some ≪≫ BaseChange.toR_ofR_iso c' ε' R' _).symm
  have eD : (BaseChange.toR c ε R' hR.poincare).L ≅ (h.poincare.pullbackAlong ψD).L :=
    (Scheme.Modules.pullback (BaseChange.κ c R' _).inv).mapIso hPR.some ≪≫ BaseChange.toR_ofR_iso c ε R' _

  have Lx : (h'.poincare.pullbackAlong x).L ≅ ((h.poincare.pullbackAlong ψD).pullbackCurve f hf hε).L :=
    (h'.poincare.pullbackAlongPullbackAlongIso' ψD' (BaseChange.overR R' fbc)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso eD' ≪≫
      BaseChange.toR_pullbackAlong_iso c' ε' R' fbc hR'.poincare ≪≫
      (Scheme.Modules.pullback _).mapIso (hR'.classify_spec _ _ _).some ≪≫
      AlgebraicGeometry.RelPicard.BCAux.toR_pullbackCurve_iso f hf R' hf' hε hεbc hR.poincare ≪≫
      (Scheme.Modules.pullback _).mapIso eD

  have Ly : (h'.poincare.pullbackAlong y).L ≅ ((h.poincare.pullbackAlong ψD).pullbackCurve f hf hε).L :=
    (h'.poincare.pullbackAlongPullbackAlongIso' (RepresentsRelSubPic.pullbackHom f hf hε h h') ψD).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (h'.classify_spec _ _ _).some ≪≫
      h.poincare.pullbackCurvePullbackAlongIso f hf hε ψD
  exact Lx ≪≫ Ly.symm

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst (solution)
