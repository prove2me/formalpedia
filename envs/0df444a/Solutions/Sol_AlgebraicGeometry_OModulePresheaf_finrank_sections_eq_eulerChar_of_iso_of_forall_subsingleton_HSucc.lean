-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4de82a76-5eb8-5720-8fa5-781a03ef2017

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [Nontrivial R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (𝓟 𝓝 : V.Modules) (e : 𝓝 ≅ 𝓟) (𝒦 : V.OrderedAffineCover)
    (hvan : ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules π 𝓟).HSucc 𝒦 i)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π 𝓝 ⊤
    ((Module.finrank R Γ(𝓝, ⊤) : ℕ) : ℤ) = (OModulePresheaf.ofModules π 𝓟).eulerChar 𝒦 := by
  letI iA : Algebra R Γ(V, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  letI i𝓝 : Module R Γ(𝓝, ⊤) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π 𝓝 ⊤
  letI i𝓟 : Module R Γ(𝓟, ⊤) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π 𝓟 ⊤

  let eT : Γ(𝓝, ⊤) ≃ₗ[R] Γ(𝓟, ⊤) :=
    { toFun := fun x => e.hom.app ⊤ x
      invFun := fun y => e.inv.app ⊤ y
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change e.hom.app ⊤ ((algebraMap R Γ(V, ⊤) r) • x) = (algebraMap R Γ(V, ⊤) r) • e.hom.app ⊤ x
        exact Scheme.Modules.Hom.app_smul _ _ _
      left_inv := fun x => by
        change (e.hom.app ⊤ ≫ e.inv.app ⊤) x = x
        rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        change (e.inv.app ⊤ ≫ e.hom.app ⊤) y = y
        rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

  obtain ⟨eH⟩ := AlgebraicGeometry.OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules π 𝓟 𝒦
  have h0 : Module.finrank R Γ(𝓝, ⊤) = Module.finrank R ((OModulePresheaf.ofModules π 𝓟).H0 𝒦) :=
    (eT.trans eH).finrank_eq

  have hc0 : (OModulePresheaf.ofModules π 𝓟).cechFinrank 𝒦 0 = Module.finrank R Γ(𝓝, ⊤) := by
    rw [OModulePresheaf.cechFinrank_zero, h0]
  have hcs : ∀ i : ℕ, (OModulePresheaf.ofModules π 𝓟).cechFinrank 𝒦 (i + 1) = 0 := fun i => by
    rw [OModulePresheaf.cechFinrank_succ]
    haveI := hvan i
    exact Module.finrank_zero_of_subsingleton
  rw [OModulePresheaf.eulerChar_def]
  rcases Nat.eq_zero_or_pos (Fintype.card 𝒦.ι) with hz | hpos
  ·
    haveI : IsEmpty 𝒦.ι := Fintype.card_eq_zero_iff.mp hz
    haveI : IsEmpty (𝒦.Idx 0) := ⟨fun s => IsEmpty.false (s.1 0)⟩
    haveI : Subsingleton ((OModulePresheaf.ofModules π 𝓟).cochain 𝒦 0) := by
      unfold OModulePresheaf.cochain; infer_instance
    haveI : Subsingleton ((OModulePresheaf.ofModules π 𝓟).H0 𝒦) := inferInstance
    rw [hz, Finset.range_zero, Finset.sum_empty, h0, Module.finrank_zero_of_subsingleton]
    rfl
  · obtain ⟨m, hm⟩ : ∃ m, Fintype.card 𝒦.ι = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hm, Finset.sum_range_succ']
    simp only [hcs, Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, one_mul, hc0]

end S_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc (solution)
