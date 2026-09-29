-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.inPicZero_pullback_of_forall_comp_mem_kernelPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/511c034a-2f25-5c22-a8a9-b63f6f081820

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_inPicZero_pullback_of_forall_comp_mem_kernelPts

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) [IsClosedImmersion j] (hjf : j ≫ f = fY)
    (LY : RelativeGroupLaw k fY)
    (hj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t fY),
      (LY.mul t P Q).1 ≫ j =
        (L.mul t ⟨P.1 ≫ j, by rw [Category.assoc, hjf, P.2]⟩ ⟨Q.1 ≫ j, by rw [Category.assoc, hjf, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hstab : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY,
      (⟨y.1 ≫ j, by rw [Category.assoc, hjf, y.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) ∈ kernelPts f L 𝓛) :
    InPicZero fY LY ((Scheme.Modules.pullback j).obj 𝓛) := by
  refine ⟨h𝓛.pullback j, fun y => ?_⟩

  let jy : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := ⟨y.1 ≫ j, by rw [Category.assoc, hjf, y.2]⟩
  obtain ⟨e⟩ := (mem_kernelPts_iff_nonempty_pullback_translate_iso k f L 𝓛 jy).mp (hstab y)

  have hcomm : LY.translate y ≫ j = j ≫ L.translate jy := by

    have h1 := hj fY (RelativeGroupLaw.idPoint) ⟨fY ≫ y.1, by rw [Category.assoc, y.2, Category.comp_id]⟩

    have h2 := L.mul_natural f fY j hjf RelativeGroupLaw.idPoint
      ⟨f ≫ jy.1, by rw [Category.assoc, jy.2, Category.comp_id]⟩
    have h2' := congrArg Subtype.val h2
    rw [schemeHomOverComp_coe] at h2'
    unfold RelativeGroupLaw.translate
    rw [h1, h2']
    congr 2
    all_goals
      apply Subtype.ext
      simp only [schemeHomOverComp_coe, Category.assoc]
      first
        | rfl
        | (rw [← Category.assoc j f, hjf]; rfl)
        | (erw [Category.id_comp, Category.comp_id])
        | (rw [← Category.assoc j f, hjf])

  refine ⟨(Scheme.Modules.pullbackComp (LY.translate y) j).app 𝓛 ≪≫
    (Scheme.Modules.pullbackCongr hcomm).app 𝓛 ≪≫
    ((Scheme.Modules.pullbackComp j (L.translate jy)).app 𝓛).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e⟩

end S_AlgebraicGeometry_Polarisation_inPicZero_pullback_of_forall_comp_mem_kernelPts
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_inPicZero_pullback_of_forall_comp_mem_kernelPts (solution)
