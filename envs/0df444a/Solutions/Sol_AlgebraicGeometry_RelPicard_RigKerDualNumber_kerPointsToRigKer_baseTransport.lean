-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c388e8a1-69e7-5386-ae55-a36af970af04

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp RelPicard.RigKerDualNumber Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigKerDualNumber.tower_dualNumber RigidifiedLineBundle.pullbackAlong_congr_hom RigKerDualNumber.baseTransport BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.baseChangeSnd_fst' BaseChange.baseChangeSnd_snd' BaseChange.ofR baseChangeSnd postComp RigidifiedLineBundle RepresentsRelSubPic algEquivZeroCut RepresentsRelSubPic.relativeGroupLaw dualNumberReduction RigKerDualNumber algEquivZeroGroupCut"
namespace BaseTransport
p2m_export "AlgebraicGeometry.RelPicard.BaseTransport" "idOver RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso BaseChange.ofR_mapIso"
p2m_open "AlgebraicGeometry.RelPicard.BaseTransport AlgebraicGeometry.RelPicard AlgebraicGeometry"

def castBase {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s') (a : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨a.1, a.2.trans e⟩

@[scoped simp] theorem castBase_coe {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s')
    (a : SchemeHomOver s f) : (castBase e a).1 = a.1 := rfl

theorem mul_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (a b : SchemeHomOver s f) :
    G.mul s' (castBase e a) (castBase e b) = castBase e (G.mul s a b) := by
  subst e; rfl

def liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

@[scoped simp] theorem liftPt_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    (liftPt D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

theorem eq_liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (z : SchemeHomOver t (D.baseChange R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = liftPt D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (liftPt_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

theorem poincare_liftPt_iso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (liftPt D R' t a)).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj (h.poincare.pullbackAlong a).L) := by
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  have E : baseChangeSnd (baseChange R c R') (liftPt D R' t a) ≫
      (BaseChange.κ c R' (D.baseChange R').toBase).hom ≫ baseChangeSnd c ψ₀ =
      (BaseChange.κ c R' t).hom ≫ baseChangeSnd c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst',
        BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc ((BaseChange.κ c R' _).hom),
        BaseChange.κ_hom_snd, ← Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, liftPt_fst,
        Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  refine ⟨(Scheme.Modules.pullback _).mapIso hP.some ≪≫ ?_⟩
  change (Scheme.Modules.pullback (baseChangeSnd _ (liftPt D R' t a))).obj
      ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).hom).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj h.poincare.L)) ≅
    (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c a)).obj h.poincare.L)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

end AlgebraicGeometry.RelPicard.BaseTransport
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp RelPicard.RigKerDualNumber Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigKerDualNumber.tower_dualNumber RigidifiedLineBundle.pullbackAlong_congr_hom RigKerDualNumber.baseTransport BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.baseChangeSnd_fst' BaseChange.baseChangeSnd_snd' BaseChange.ofR baseChangeSnd postComp RigidifiedLineBundle RepresentsRelSubPic algEquivZeroCut RepresentsRelSubPic.relativeGroupLaw dualNumberReduction RigKerDualNumber algEquivZeroGroupCut"
namespace RigKerDualNumber
p2m_export "AlgebraicGeometry.RelPicard.RigKerDualNumber" "tower_dualNumber baseTransport mul one"
p2m_open "AlgebraicGeometry.RelPicard.RigKerDualNumber AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "AlgebraicGeometry.RelPicard.BaseTransport P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport"

theorem kerPointsToRigKer_baseTransport_liftPt
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (x : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber B)) D.toBase //
      dualNumberReduction R B ≫ x.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R B)).1 })
    (hx' : dualNumberReduction R' B ≫
        (liftPt D R' (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B))
          (castBase (tower_dualNumber R' B) x.1)).1 =
      ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
        (Scheme.TwoAffineOpenCover.specMap R' B)).1) :
    baseTransport R' c ε B (h.kerPointsToRigKer B x) =
      h'.kerPointsToRigKer B
        ⟨liftPt D R' (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (castBase (tower_dualNumber R' B) x.1),
          hx'⟩ := by
  obtain ⟨e⟩ := poincare_liftPt_iso c ε D h R' h' hP (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B))
    (castBase (tower_dualNumber R' B) x.1)
  refine Quotient.sound (?_ : Nonempty (_ ≅ _))
  exact ⟨BaseChange.ofR_mapIso c ε R'
      (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso _ _ _ ≪≫
        RigidifiedLineBundle.pullbackAlong_congr_hom h.poincare (postComp x.1 (idOver (tower_dualNumber R' B)))
          (castBase (tower_dualNumber R' B) x.1) (by simp [postComp, idOver, castBase])) ≪≫
    e.symm⟩

end AlgebraicGeometry.RelPicard.RigKerDualNumber
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport"

open _root_.AlgebraicGeometry.RelPicard.BaseTransport _root_.P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.AlgebraicGeometry.RelPicard.BaseTransport in

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (x : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber B)) D.toBase //
      dualNumberReduction R B ≫ x.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R B)).1 })
    (x' : { x' : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (D.baseChange R').toBase //
      dualNumberReduction R' B ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
          (Scheme.TwoAffineOpenCover.specMap R' B)).1 })
    (hxx' : x'.1.1 ≫ pullback.fst D.toBase (specMap R R') = x.1.1) :
    RigKerDualNumber.baseTransport R' c ε B (h.kerPointsToRigKer B x) = h'.kerPointsToRigKer B x' := by
  obtain ⟨x'v, hx'⟩ := x'
  have hv : x'v = liftPt D R' _ (castBase (RigKerDualNumber.tower_dualNumber R' B) x.1) :=
    eq_liftPt D R' _ x'v _ hxx'
  subst hv
  exact RigKerDualNumber.kerPointsToRigKer_baseTransport_liftPt c ε D h R' h' hP B x hx'

end S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport (solution)
