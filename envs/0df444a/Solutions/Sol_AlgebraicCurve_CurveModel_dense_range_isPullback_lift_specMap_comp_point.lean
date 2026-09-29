-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.dense_range_isPullback_lift_specMap_comp_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f4517f96-740b-5304-a455-c1192cddeb05

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_dense_range_isPullback_lift_specMap_comp_point

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    (C : Type u) [Field C] (cK : K →+* C)
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ M.C) (t : Y ⟶ Spec (CommRingCat.of C))
    (hY : IsPullback g t M.toBase (Spec.map (CommRingCat.ofHom cK))) :
    Dense (Set.range fun p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} =>
      (hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p.1) (𝟙 _)
        (by rw [Category.assoc, p.2, Category.comp_id, Category.id_comp])).base (IsLocalRing.closedPoint C)) := by

  classical
  rw [dense_iff_inter_open]
  rintro V hVo ⟨y₀, hy₀⟩

  haveI : UniversallyOpen (Spec.map (CommRingCat.ofHom cK)) := inferInstance
  haveI : UniversallyOpen g := MorphismProperty.of_isPullback hY.flip inferInstance
  have hgV : IsOpen (g.base '' V) := g.isOpenMap _ hVo

  haveI : JacobsonSpace ↥M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  have hdense : Dense (closedPoints ↥M.C) := by
    rw [dense_iff_closure_eq]; exact closure_closedPoints
  obtain ⟨_, ⟨y, hyV, rfl⟩, hx⟩ := hdense.inter_open_nonempty _ hgV ⟨g.base y₀, y₀, hy₀, rfl⟩

  set p : Spec (CommRingCat.of K) ⟶ M.C := pointOfClosedPoint M.toBase (g.base y) hx with hp
  have hpb : p ≫ M.toBase = 𝟙 _ := pointOfClosedPoint_comp M.toBase (g.base y) hx

  have key : ∀ hw, (hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p) (𝟙 _) hw).base (IsLocalRing.closedPoint C) = y := by
    intro hw
    have hee : Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).inv ≫ Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).hom = 𝟙 _ := by
      rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
    have hfac : Y.fromSpecResidueField y ≫ g = (Spec.map (g.residueFieldMap y) ≫ Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).inv) ≫ p := by
      rw [hp, pointOfClosedPoint, Category.assoc, ← Category.assoc (Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).inv), hee, Category.id_comp,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    have hιz : Y.fromSpecResidueField y =
        (Y.fromSpecResidueField y ≫ t) ≫ hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p) (𝟙 _) hw := by
      apply hY.hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc]
        have : (Y.fromSpecResidueField y ≫ t) ≫ Spec.map (CommRingCat.ofHom cK) =
            Spec.map (g.residueFieldMap y) ≫ Spec.map (residueFieldIsoBase M.toBase (g.base y) hx).inv := by
          rw [Category.assoc, ← hY.w, ← Category.assoc, hfac, Category.assoc, hpb, Category.comp_id]
        rw [this, hfac]
      · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
    have h1 : (Y.fromSpecResidueField y).base (IsLocalRing.closedPoint (Y.residueField y)) = y := by simp
    conv_rhs => rw [← h1, hιz]
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨_, ?_, ⟨⟨p, hpb⟩, rfl⟩⟩
  dsimp only
  rw [key]
  exact hyV

end S_AlgebraicCurve_CurveModel_dense_range_isPullback_lift_specMap_comp_point
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_dense_range_isPullback_lift_specMap_comp_point (solution)
