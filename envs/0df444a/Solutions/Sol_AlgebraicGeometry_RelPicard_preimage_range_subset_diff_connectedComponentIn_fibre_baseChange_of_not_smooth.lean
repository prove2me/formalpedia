-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a1d57c6f-8375-5b1c-9a98-25768a54726b

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.homeoOfIso Spec Scheme Smooth Scheme.Hom.comp_preimage Scheme.Hom.comp_apply"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "sectionFibrePoint exists_fibreIso_hom_comp_eq"
namespace TZETransport
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem exists_fibreIso_baseChange {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (baseChange R c A) x' ≅ pullback c (x' ≫ specMap R A),
      φ.hom ≫ pullback.snd c (x' ≫ specMap R A) = pullback.snd (baseChange R c A) x' ∧
      φ.hom ≫ pullback.fst c (x' ≫ specMap R A) = pullback.fst (baseChange R c A) x' ≫ pullback.fst c (specMap R A) := by
  obtain ⟨φ, h1, h2, -⟩ := exists_fibreIso_hom_comp_eq c (specMap R A) x' (x' ≫ specMap R A) rfl
  exact ⟨φ, h1, h2⟩

end AlgebraicGeometry.RelPicard.TZETransport

open AlgebraicGeometry.RelPicard.TZETransport in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    {Z ZA : Scheme.{u}} (z : Z ⟶ C) (zA : ZA ⟶ pullback c (specMap R A))
    (hzA : Set.range (zA ≫ pullback.fst c (specMap R A)).base ⊆ Set.range z.base)
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range z.base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      ¬ Smooth (pullback.snd (baseChange R c A) s') →
      (pullback.fst (baseChange R c A) s').base ⁻¹' Set.range zA.base ⊆
        ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
            (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) \
          connectedComponentIn
            ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
                (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
            (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) := by
  intro k _ _ s' hns
  obtain ⟨φ, hφ2, hφ1⟩ := exists_fibreIso_baseChange c A s'

  let e : ↥(pullback (baseChange R c A) s') ≃ₜ ↥(pullback c (s' ≫ specMap R A)) := Scheme.homeoOfIso φ
  have hesymm : ∀ x : ↥(pullback c (s' ≫ specMap R A)), e.symm x = φ.inv.base x := fun _ => rfl
  have hV' : pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      = φ.hom ⁻¹ᵁ (pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ1]
  have hV'set : ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
      (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
      e ⁻¹' ((pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s' ≫ specMap R A)).Opens) :
        Set ↥(pullback c (s' ≫ specMap R A))) := by
    rw [hV']; rfl

  have hsec : (sectionFibrePoint (sectionBaseChange A ε) s').1 ≫ φ.hom = (sectionFibrePoint ε (s' ≫ specMap R A)).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ1]
      show (sectionFibrePoint (sectionBaseChange A ε) s').1 ≫ pullback.fst (baseChange R c A) s' ≫
          pullback.fst c (specMap R A) = (sectionFibrePoint ε (s' ≫ specMap R A)).1 ≫ pullback.fst c (s' ≫ specMap R A)
      simp only [sectionFibrePoint, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, sectionBaseChange_coe_fst]
    · rw [Category.assoc, hφ2]
      simp only [sectionFibrePoint, pullback.lift_snd]
  have hsecpt : φ.inv.base (((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k))
      = ((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k) := by
    rw [← hsec]
    exact e.symm_apply_apply _

  set V : Set ↥(pullback c (s' ≫ specMap R A)) :=
    ((pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s' ≫ specMap R A)).Opens) : Set ↥(pullback c (s' ≫ specMap R A)))
    with hVdef
  set pt := ((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k) with hptdef
  have hcc : e ⁻¹' connectedComponentIn V pt =
      connectedComponentIn (e ⁻¹' V) (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) := by
    rw [← hsecpt, ← hesymm]
    by_cases hx : pt ∈ V
    · rw [← Homeomorph.image_symm]
      exact Homeomorph.image_connectedComponentIn _ hx
    · rw [connectedComponentIn_eq_empty hx, Set.preimage_empty, connectedComponentIn_eq_empty]
      intro h
      apply hx
      have : e (e.symm pt) ∈ V := h
      rwa [e.apply_symm_apply] at this

  have hmove : ∀ p : ↥(pullback (baseChange R c A) s'),
      (pullback.fst (baseChange R c A) s').base p ∈ Set.range zA.base →
        e p ∈ (pullback.fst c (s' ≫ specMap R A)).base ⁻¹' Set.range z.base := by
    rintro p ⟨q, hq⟩
    show (pullback.fst c (s' ≫ specMap R A)).base (φ.hom.base p) ∈ Set.range z.base
    rw [← Scheme.Hom.comp_apply, hφ1, Scheme.Hom.comp_apply, ← hq]
    exact hzA ⟨q, rfl⟩

  have hns0 : ¬ Smooth (pullback.snd c (s' ≫ specMap R A)) := by
    intro h
    apply hns
    rw [← hφ2]
    infer_instance
  intro p hp
  have h1 := hz'ε k (s' ≫ specMap R A) hns0 (hmove p hp)
  have h2 : p ∈ e ⁻¹' (V \ connectedComponentIn V pt) := h1
  rw [Set.preimage_diff, hcc] at h2
  rw [hV'set]
  exact h2

end S_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth (solution)
