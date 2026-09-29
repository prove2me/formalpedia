-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3e207a27-4b08-5620-9997-7bcafe54b929

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {ι : Type v} [Finite ι] {X₁ X₂ : ι → Scheme.{u}}
    (f₁ : ∀ i, X₁ i ⟶ Spec (CommRingCat.of A₀)) (f₂ : ∀ i, X₂ i ⟶ Spec (CommRingCat.of A₀))
    [∀ i, QuasiCompact (f₁ i)] [∀ i, QuasiSeparated (f₁ i)] [∀ i, LocallyOfFinitePresentation (f₂ i)]
    (g : ∀ i, pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (hg : ∀ i, g i ≫ pullback.snd (f₂ i) _ = pullback.snd (f₁ i) _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ g₀ : ∀ i, pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        (∀ i, g₀ i ≫ pullback.snd (f₂ i) _ = pullback.snd (f₁ i) _) ∧
        ∀ (i : ι)
          (q₁ : pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst (f₁ i) _ = pullback.fst (f₁ i) _ →
          q₁ ≫ pullback.snd (f₁ i) _ = pullback.snd (f₁ i) _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₂ ≫ pullback.fst (f₂ i) _ = pullback.fst (f₂ i) _ →
          q₂ ≫ pullback.snd (f₂ i) _ = pullback.snd (f₂ i) _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₁ ≫ g₀ i = g i ≫ q₂ := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  choose Tf hTfg hsT g₀ hg₀ hcompat using fun i =>
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (f₁ i) (f₂ i) (g i) (hg i) s
  choose G hG using hTfg
  let T : Subalgebra A₀ A := Algebra.adjoin A₀ (((Finset.univ.biUnion G) ∪ s : Finset A) : Set A)
  have hTfg : T.FG := ⟨(Finset.univ.biUnion G) ∪ s, rfl⟩
  have hsT' : (↑s : Set A) ⊆ T := fun x hx => Algebra.subset_adjoin (by
    rw [Finset.coe_union]; exact Or.inr hx)
  have hle : ∀ i, Tf i ≤ T := by
    intro i; rw [← hG i]
    apply Algebra.adjoin_mono
    intro x hx
    rw [Finset.coe_union, Finset.coe_biUnion]
    exact Or.inl (Set.mem_iUnion₂.2 ⟨i, Finset.mem_coe.2 (Finset.mem_univ i), hx⟩)
  have hcomp : ∀ i, CommRingCat.ofHom (algebraMap A₀ ↥(Tf i)) ≫ CommRingCat.ofHom (Subalgebra.inclusion (hle i)).toRingHom =
      CommRingCat.ofHom (algebraMap A₀ ↥T) := by
    intro i; rw [← CommRingCat.ofHom_comp]; congr 1
  have hval : ∀ i, CommRingCat.ofHom (Subalgebra.inclusion (hle i)).toRingHom ≫ CommRingCat.ofHom T.val.toRingHom =
      CommRingCat.ofHom (Tf i).val.toRingHom := by
    intro i; rw [← CommRingCat.ofHom_comp]; rfl

  let r₁ : ∀ i, pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
      pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(Tf i)))) := fun i =>
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hle i)).toRingHom)) (by
      rw [Category.assoc, ← Spec.map_comp, hcomp]; exact pullback.condition)

  let gT : ∀ i, pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
      pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) := fun i =>
    pullback.lift (r₁ i ≫ g₀ i ≫ pullback.fst _ _) (pullback.snd _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (g₀ i), hg₀ i]
      show r₁ i ≫ pullback.snd (f₁ i) _ ≫ _ = _
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, ← Spec.map_comp, hcomp])
  refine ⟨T, hTfg, hsT', gT, fun i => pullback.lift_snd _ _ _, ?_⟩
  intro i q₁ q₂ hq₁f hq₁s hq₂f hq₂s

  let q₂' : pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(Tf i)))) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Tf i).val.toRingHom)) (by
      rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact pullback.condition)
  have h1 : (q₁ ≫ r₁ i) ≫ pullback.fst (f₁ i) _ = pullback.fst (f₁ i) _ := by
    rw [Category.assoc, pullback.lift_fst, hq₁f]
  have h2 : (q₁ ≫ r₁ i) ≫ pullback.snd (f₁ i) _ = pullback.snd (f₁ i) _ ≫ Spec.map (CommRingCat.ofHom (Tf i).val.toRingHom) := by
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hq₁s, Category.assoc, ← Spec.map_comp, hval]
  have h3 : q₂' ≫ pullback.fst (f₂ i) _ = pullback.fst (f₂ i) _ := pullback.lift_fst _ _ _
  have h4 : q₂' ≫ pullback.snd (f₂ i) _ = pullback.snd (f₂ i) _ ≫ Spec.map (CommRingCat.ofHom (Tf i).val.toRingHom) :=
    pullback.lift_snd _ _ _
  have key := hcompat i (q₁ ≫ r₁ i) q₂' h1 h2 h3 h4
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    show q₁ ≫ gT i ≫ pullback.fst (f₂ i) _ = g i ≫ q₂ ≫ pullback.fst (f₂ i) _
    rw [pullback.lift_fst, hq₂f]
    have := congrArg (fun k => k ≫ pullback.fst (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(Tf i))))) key
    simp only [Category.assoc, h3] at this
    exact this
  · rw [Category.assoc, Category.assoc]
    show q₁ ≫ gT i ≫ pullback.snd (f₂ i) _ = g i ≫ q₂ ≫ pullback.snd (f₂ i) _
    rw [pullback.lift_snd, hq₁s, hq₂s, ← Category.assoc, hg i]

end S_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation (solution)
