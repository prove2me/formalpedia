-- Prove2me | solution 1 for AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0062313b-ccbb-5912-874e-fac9fa9da1c0

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
import Theorems.Thm_AlgebraicGeometry_isIso_pullbackMap_fromSpecResidueField_of_isIso_pullbackMap_opens
import Theorems.Thm_AlgebraicGeometry_isIso_pullbackMap_opens_of_forall_exists_le_isIso_pullbackMap_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q] :
    ∃ U : Y.Opens,
      (∀ y : Y, y ∈ (U : Set Y) ↔
        IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) ∧
      IsIso (pullback.map p U.ι q U.ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
  classical

  let U : Y.Opens := ⨆ V : {V : Y.Opens // IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))}, V.1
  have hmem : ∀ y : Y, y ∈ U ↔ ∃ V : Y.Opens, y ∈ V ∧
      IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
    intro y
    simp only [U, TopologicalSpace.Opens.mem_iSup, Subtype.exists, exists_prop]
    exact ⟨fun ⟨V, hV, hyV⟩ => ⟨V, hyV, hV⟩, fun ⟨V, hyV, hV⟩ => ⟨V, hV, hyV⟩⟩
  have hle : ∀ V : Y.Opens, IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) → V ≤ U := by
    intro V hV
    exact le_iSup (fun V : {V : Y.Opens // IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))} => V.1) ⟨V, hV⟩
  refine ⟨U, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_⟩
  · obtain ⟨V, hyV, hV⟩ := (hmem y).mp hy
    exact AlgebraicGeometry.isIso_pullbackMap_fromSpecResidueField_of_isIso_pullbackMap_opens p q h w V y hyV hV
  · obtain ⟨V, hyV, hV⟩ :=
      AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField p q h w y hy
    exact (hmem y).mpr ⟨V, hyV, hV⟩
  · refine AlgebraicGeometry.isIso_pullbackMap_opens_of_forall_exists_le_isIso_pullbackMap_opens p q h w U ?_
    intro y hy
    obtain ⟨V, hyV, hV⟩ := (hmem y).mp hy
    exact ⟨V, hyV, hle V hV, hV⟩

end S_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat (solution)
