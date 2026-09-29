-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fb2611be-e1ad-5378-9976-269f5315e285

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme RelPicard.RigKerDualNumber Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.baseChange_relativeGroupLaw_mul_compat RelativeGroupLaw.eq_one_of_mul_self"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigKerDualNumber.tower_dualNumber BaseChange.ofR RepresentsRelSubPic algEquivZeroCut RepresentsRelSubPic.relativeGroupLaw dualNumberReduction dualNumberReduction_comp_specMap RigKerDualNumber algEquivZeroGroupCut baseChange_relativeGroupLaw_mul_compat"
namespace BaseTransport
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

theorem liftPt_mul {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a b : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    liftPt D R' t ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
        (t ≫ specMap R R') a b) =
      (RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t
        (liftPt D R' t a) (liftPt D R' t b) := by
  symm
  apply eq_liftPt
  exact AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP t _ _ a b
    (liftPt_fst D R' t a).symm (liftPt_fst D R' t b).symm

theorem one_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') :
    castBase e (G.one s) = G.one s' := by
  subst e; rfl

private theorem _root_.AlgebraicGeometry.RelativeGroupLaw.eq_one_of_mul_self {R : Type u} [CommRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (t : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver t f) (hu : G.mul t u u = u) : u = G.one t := by
  calc u = G.mul t (G.one t) u := (G.one_mul t u).symm
    _ = G.mul t (G.mul t (G.inv t u) u) u := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t u) (G.mul t u u) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t u) u := by rw [hu]
    _ = G.one t := G.inv_mul_cancel t u

p2m_alias "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelativeGroupLaw.eq_one_of_mul_self" "AlgebraicGeometry.RelativeGroupLaw.eq_one_of_mul_self"

theorem liftPt_one {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    liftPt D R' t ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
        (t ≫ specMap R R')) =
      (RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one t := by
  apply RelativeGroupLaw.eq_one_of_mul_self
  rw [← liftPt_mul c ε D h R' h' hP, RelativeGroupLaw.mul_one]

theorem comp_liftPt_coe {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T T₀ : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (t₀ : T₀ ⟶ Spec (CommRingCat.of R'))
    (g : T₀ ⟶ T) (hg : g ≫ t = t₀) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    g ≫ (liftPt D R' t a).1 =
      (liftPt D R' t₀ ⟨g ≫ a.1, by rw [Category.assoc, a.2, ← Category.assoc, hg]⟩).1 := by
  have := eq_liftPt D R' t₀ ⟨g ≫ (liftPt D R' t a).1, by rw [Category.assoc, (liftPt D R' t a).2, hg]⟩
    ⟨g ≫ a.1, by rw [Category.assoc, a.2, ← Category.assoc, hg]⟩
    (by rw [Category.assoc, liftPt_fst])
  exact congrArg Subtype.val this

end AlgebraicGeometry.RelPicard.BaseTransport
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme RelPicard.RigKerDualNumber Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.baseChange_relativeGroupLaw_mul_compat RelativeGroupLaw.eq_one_of_mul_self"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigKerDualNumber.tower_dualNumber BaseChange.ofR RepresentsRelSubPic algEquivZeroCut RepresentsRelSubPic.relativeGroupLaw dualNumberReduction dualNumberReduction_comp_specMap RigKerDualNumber algEquivZeroGroupCut baseChange_relativeGroupLaw_mul_compat"
namespace RigKerDualNumber
p2m_export "AlgebraicGeometry.RelPicard.RigKerDualNumber" "tower_dualNumber tower_base mul one"
p2m_open "AlgebraicGeometry.RelPicard.RigKerDualNumber AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "AlgebraicGeometry.RelPicard.BaseTransport P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport"

theorem dualNumberReduction_comp_liftPt_eq_one
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
    : dualNumberReduction R' B ≫
        (liftPt D R' (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B))
          (castBase (tower_dualNumber R' B) x.1)).1 =
      ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
        (Scheme.TwoAffineOpenCover.specMap R' B)).1 := by
  rw [comp_liftPt_coe D R' _ (Scheme.TwoAffineOpenCover.specMap R' B) (dualNumberReduction R' B)
    (dualNumberReduction_comp_specMap R' B), ← liftPt_one c ε D h R' h' hP]
  congr 2
  apply Subtype.ext
  change dualNumberReduction R B ≫ x.1.1 = _
  rw [x.2, ← one_castBase _ (tower_base R' B)]
  rfl

end AlgebraicGeometry.RelPicard.RigKerDualNumber
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport"

open _root_.AlgebraicGeometry.RelPicard.BaseTransport _root_.P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.AlgebraicGeometry.RelPicard.BaseTransport in

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
    : ∃! x' : { x' : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (D.baseChange R').toBase //
      dualNumberReduction R' B ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
          (Scheme.TwoAffineOpenCover.specMap R' B)).1 },
      x'.1.1 ≫ pullback.fst D.toBase (specMap R R') = x.1.1 := by
  refine ⟨⟨liftPt D R' _ (castBase (RigKerDualNumber.tower_dualNumber R' B) x.1),
      RigKerDualNumber.dualNumberReduction_comp_liftPt_eq_one c ε D h R' h' hP B x⟩, liftPt_fst D R' _ _, ?_⟩
  rintro ⟨y, hy⟩ hyx
  exact Subtype.ext (eq_liftPt D R' _ y _ hyx)

end S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq (solution)
