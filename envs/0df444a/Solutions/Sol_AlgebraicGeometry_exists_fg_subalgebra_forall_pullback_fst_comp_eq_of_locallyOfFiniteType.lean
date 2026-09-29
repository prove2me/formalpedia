-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/516f687c-1369-569c-9b01-0dcba14f55b0

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {ι : Type v} [Finite ι] {X₁ X₂ : ι → Scheme.{u}}
    (f₁ : ∀ i, X₁ i ⟶ Spec (CommRingCat.of A₀)) (f₂ : ∀ i, X₂ i ⟶ Spec (CommRingCat.of A₀))
    [∀ i, QuasiCompact (f₁ i)] [∀ i, LocallyOfFiniteType (f₂ i)]
    (a b : ∀ i, X₁ i ⟶ X₂ i) (ha : ∀ i, a i ≫ f₂ i = f₁ i) (hb : ∀ i, b i ≫ f₂ i = f₁ i)
    (hab : ∀ i, pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ a i =
      pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ b i) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ i, pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ a i =
        pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ b i := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  choose Tf hTfg hsT hEq using fun i =>
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      (f₁ i) (f₂ i) (a i) (b i) (ha i) (hb i) (hab i) s
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
  refine ⟨T, hTfg, hsT', fun i => ?_⟩

  have hcomp : CommRingCat.ofHom (algebraMap A₀ ↥(Tf i)) ≫ CommRingCat.ofHom (Subalgebra.inclusion (hle i)).toRingHom =
      CommRingCat.ofHom (algebraMap A₀ ↥T) := by
    rw [← CommRingCat.ofHom_comp]; congr 1
  let r : pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
      pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(Tf i)))) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hle i)).toRingHom)) (by
      rw [Category.assoc, ← Spec.map_comp, hcomp]; exact pullback.condition)
  have hr : r ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  rw [← hr, Category.assoc, Category.assoc, hEq i]

end S_AlgebraicGeometry_exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType (solution)
