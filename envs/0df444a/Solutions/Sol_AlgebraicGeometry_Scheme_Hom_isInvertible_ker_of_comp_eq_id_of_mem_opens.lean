-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3dfa259a-7268-5e35-aa8c-ea0f6997a44f

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsOpenImmersion.lift SmoothOfRelativeDimension Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.support_ker Spec Scheme IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Hom.opensRange_of_isIso Scheme.Opens IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.IdealSheafData.IsInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso Opens.range_ι Hom Hom.support_ker IdealSheafData.ker_fst_of_isClosedImmersion Hom.opensRange_of_isIso Opens Opens.opensRange_ι IdealSheafData IdealSheafData.IsInvertible Hom.isInvertible_ker_of_comp_eq_id IdealSheafData.IsInvertible.of_comap_of_support_subset_range" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map subscheme ker_fst_of_isClosedImmersion ideal comap IsInvertible IsInvertible.of_comap_of_support_subset_range" end Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

theorem Scheme.IdealSheafData.ker_eq_comap_of_isPullback' {P X' Y Z : Scheme.{u}} {fst : P ⟶ X'} {snd : P ⟶ Y}
    {f : X' ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsClosedImmersion g] : fst.ker = g.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso Opens.range_ι Hom Hom.support_ker IdealSheafData.ker_fst_of_isClosedImmersion Hom.opensRange_of_isIso Opens Opens.opensRange_ι IdealSheafData IdealSheafData.IsInvertible Hom.isInvertible_ker_of_comp_eq_id IdealSheafData.IsInvertible.of_comap_of_support_subset_range" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "ker_comp_of_isIso support_ker opensRange_of_isIso continuous opensRange ker isClosedEmbedding isInvertible_ker_of_comp_eq_id" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens_aux
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of O)) [IsSeparated πY]
    (W : Y.Opens) [SmoothOfRelativeDimension 1 (W.ι ≫ πY)]
    (σ : Spec (CommRingCat.of O) ⟶ Y) (hσ : σ ≫ πY = 𝟙 _) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    σ.ker.IsInvertible := by

  have hrange : Set.range σ.base ⊆ (W : Set Y) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW
  let σ' : Spec (CommRingCat.of O) ⟶ W := IsOpenImmersion.lift W.ι σ (by rwa [Scheme.Opens.range_ι])
  have hσ' : σ' ≫ W.ι = σ := IsOpenImmersion.lift_fac _ _ _
  have hsec : σ' ≫ (W.ι ≫ πY) = 𝟙 _ := by rw [← Category.assoc, hσ', hσ]
  have h1 : σ'.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ' hsec
  haveI : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ πY) := by rw [hσ]; infer_instance
    exact .of_comp σ πY
  have hpre : σ ⁻¹ᵁ W.ι.opensRange = ⊤ := by
    rw [Scheme.Opens.opensRange_ι]
    exact top_le_iff.mp fun x _ => hrange ⟨x, rfl⟩
  have H : IsPullback σ' (𝟙 _) W.ι σ :=
    IsOpenImmersion.isPullback _ _ _ _ (by rw [Category.id_comp, hσ']) (by rw [hpre, Scheme.Hom.opensRange_of_isIso])
  have h2 : σ'.ker = σ.ker.comap W.ι := Scheme.IdealSheafData.ker_eq_comap_of_isPullback' H
  apply Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range W.ι σ.ker
  · rw [Scheme.Hom.support_ker, σ.isClosedEmbedding.isClosed_range.closure_eq, Scheme.Opens.range_ι]
    exact hrange
  · rw [← h2]; exact h1

end AlgebraicGeometry

theorem solution
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of O)) [IsSeparated πY]
    (W : Y.Opens) [SmoothOfRelativeDimension 1 (W.ι ≫ πY)]
    (σ : Spec (CommRingCat.of O) ⟶ Y) (hσ : σ ≫ πY = 𝟙 _) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    σ.ker.IsInvertible :=
  AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens_aux πY W σ hσ hW

end S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens (solution)
