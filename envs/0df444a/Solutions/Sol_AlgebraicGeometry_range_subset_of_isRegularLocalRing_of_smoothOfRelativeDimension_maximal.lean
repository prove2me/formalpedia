-- Prove2me | solution 1 for AlgebraicGeometry.range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/36dbc8cb-bff3-5e57-8cf3-746a76faaede

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
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

import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

theorem solution
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c] [Flat c]
    (hreg : ∀ x : C, IsRegularLocalRing (C.presheaf.stalk x))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hUmax : ∀ W : C.Opens, SmoothOfRelativeDimension 1 (W.ι ≫ c) → W ≤ U) (hUne : (U : Set C).Nonempty)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c) :
    Set.range ε.1.base ⊆ (U : Set C) := by
  classical
  rintro _ ⟨t, rfl⟩

  have hspec : ε.1.base t ⤳ ε.1.base (IsLocalRing.closedPoint A) :=
    (IsLocalRing.specializes_closedPoint t).map ε.1.continuous
  suffices h0 : ε.1.base (IsLocalRing.closedPoint A) ∈ (U : Set C) from hspec.mem_open U.isOpen h0

  haveI : LocallyOfFinitePresentation c := inferInstance
  have hx0 : ε.1.base (IsLocalRing.closedPoint A) ∈ c.smoothLocus :=
    AlgebraicGeometry.SchemeHomOver.apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk A c ε (hreg _)

  have hWsm : Smooth (c.smoothLocus.ι ≫ c) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact c.smoothLocus.ι_preimage_self
  have hUW : U ≤ c.smoothLocus := by
    intro y hy
    haveI : Smooth (U.ι ≫ c) := SmoothOfRelativeDimension.smooth 1 _
    have h := (U.ι ≫ c).smoothLocus_eq_top
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
    have hmem : (⟨y, hy⟩ : ↥U) ∈ U.ι ⁻¹ᵁ c.smoothLocus := by rw [h]; trivial
    exact hmem
  haveI : Nonempty (c.smoothLocus : Scheme.{0}) := ⟨⟨_, hx0⟩⟩
  haveI : IsIntegral (c.smoothLocus : Scheme.{0}) := inferInstance
  haveI := hWsm
  have hV : ((c.smoothLocus.ι ⁻¹ᵁ U : (c.smoothLocus : Scheme.{0}).Opens) : Set (c.smoothLocus : Scheme.{0})).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    exact ⟨⟨x, hUW hx⟩, hx⟩
  haveI : SmoothOfRelativeDimension 1 ((c.smoothLocus.ι ⁻¹ᵁ U).ι ≫ c.smoothLocus.ι ≫ c) := by
    rw [show (c.smoothLocus.ι ⁻¹ᵁ U).ι ≫ c.smoothLocus.ι ≫ c = (c.smoothLocus.ι ∣_ U) ≫ U.ι ≫ c from by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]]
    have h : SmoothOfRelativeDimension (0 + 1) ((c.smoothLocus.ι ∣_ U) ≫ U.ι ≫ c) := inferInstance
    rwa [Nat.zero_add] at h
  exact hUmax c.smoothLocus
    (AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace 1 (c.smoothLocus.ι ≫ c) (c.smoothLocus.ι ⁻¹ᵁ U) hV) hx0

end S_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal
end P2MW
export P2MW.S_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal (solution)
