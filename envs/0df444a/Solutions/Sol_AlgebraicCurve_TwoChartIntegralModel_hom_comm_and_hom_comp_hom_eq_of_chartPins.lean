-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.hom_comm_and_hom_comp_hom_eq_of_chartPins
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c72179bf-30b8-5861-a768-8dd84689bf30

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace PinsBody

theorem isDominant_ιFin (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsDominant (ιFin R F j) := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  exact ⟨(ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem hom_ext (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  haveI := isDominant_ιFin R F j
  exact ext_of_isDominant_of_isSeparated q h (ιFin R F j) hFin

end PinsBody

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsSeparated (toBase R F j)]
    (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hw : w.hom ≫ toBase R F j = toBase R F j)
    (θw : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F j))
    (hpw : ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom θw.toRingHom) ≫ ιFin R F j)
    (δ : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hδ : δ.hom ≫ toBase R F j = toBase R F j)
    (θδ : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F j))
    (hpδ : Spec.map (CommRingCat.ofHom θδ.toRingHom) ≫ ιFin R F j = ιFin R F j ≫ δ.inv) :
    ((∀ x, θw (θδ x) = θδ (θw x)) → w.hom ≫ δ.hom = δ.hom ≫ w.hom) ∧
    ((∀ x, θδ (θw (θw x)) = x) → w.hom ≫ w.hom = δ.hom) := by
  have hδinv : δ.inv ≫ toBase R F j = toBase R F j := by rw [Iso.inv_comp_eq, hδ]

  have hpwδ : ιFin R F j ≫ w.hom ≫ δ.inv = Spec.map (CommRingCat.ofHom (θw.comp θδ).toRingHom) ≫ ιFin R F j := by
    rw [← Category.assoc, hpw, Category.assoc, ← hpδ, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hpδw : ιFin R F j ≫ δ.inv ≫ w.hom = Spec.map (CommRingCat.ofHom (θδ.comp θw).toRingHom) ≫ ιFin R F j := by
    rw [← Category.assoc, ← hpδ, Category.assoc, hpw, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨fun hcomm => ?_, fun hsq => ?_⟩
  ·
    have hθ : θδ.comp θw = θw.comp θδ := AlgHom.ext fun x => (hcomm x).symm
    have key : δ.inv ≫ w.hom = w.hom ≫ δ.inv := by
      refine PinsBody.hom_ext R F j _ _ (toBase R F j) (by rw [Category.assoc, hw, hδinv, Category.assoc, hδinv, hw]) ?_
      rw [hpδw, hpwδ, hθ]
    calc w.hom ≫ δ.hom = δ.hom ≫ (δ.inv ≫ w.hom) ≫ δ.hom := by simp
      _ = δ.hom ≫ (w.hom ≫ δ.inv) ≫ δ.hom := by rw [key]
      _ = δ.hom ≫ w.hom := by simp
  ·
    have hθ : (θδ.comp θw).comp θw = AlgHom.id R _ := AlgHom.ext fun x => hsq x
    have hpin : ιFin R F j ≫ δ.inv ≫ w.hom ≫ w.hom = Spec.map (CommRingCat.ofHom ((θδ.comp θw).comp θw).toRingHom) ≫ ιFin R F j := by
      rw [← Category.assoc, ← hpδ, Category.assoc, ← Category.assoc (Spec.map _), ← Category.assoc, Category.assoc _ (ιFin R F j),
        hpw, ← Category.assoc, ← Spec.map_comp, Category.assoc, hpw, ← Category.assoc, ← Spec.map_comp]
      rfl
    have key : δ.inv ≫ w.hom ≫ w.hom = 𝟙 _ := by
      refine PinsBody.hom_ext R F j _ _ (toBase R F j) (by rw [Category.assoc, Category.assoc, hw, hw, hδinv, Category.id_comp]) ?_
      rw [hpin, hθ, Category.comp_id]
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ ιFin R F j = ιFin R F j
      rw [CommRingCat.ofHom_id]
      erw [Spec.map_id]
      rw [Category.id_comp]
    calc w.hom ≫ w.hom = δ.hom ≫ (δ.inv ≫ w.hom ≫ w.hom) := by simp
      _ = δ.hom := by rw [key, Category.comp_id]

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins (solution)
