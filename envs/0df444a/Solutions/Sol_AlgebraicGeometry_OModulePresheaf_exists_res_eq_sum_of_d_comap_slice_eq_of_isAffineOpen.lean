-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/eff9dc15-5652-5f08-88f5-ec04d4381993

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by
  classical
  have h1 : ∀ U' : X.affineOpens, _ := fun U' =>
    AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen fX fY p₁ p₂ hP 𝒲 (𝒲.comap iY) c hc U'.1 U'.2
  choose γ e hV hH hZ using h1
  have h5 := AlgebraicGeometry.OModulePresheaf.exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
    fX fY hX x₀ hx₀ p₁ p₂ hP iY hiY₁ hiY₂ (𝒲.comap iY) e hZ
    (fun U₁ U₂ hle => AlgebraicGeometry.OModulePresheaf.exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
      fX fY p₁ p₂ hP 𝒲 (𝒲.comap iY) c U₁.1 U₁.2 (γ U₁) (e U₁) (hV U₁) (hH U₁)
      U₂.1 U₂.2 hle (γ U₂) (e U₂) (hV U₂) (hH U₂))
    (fun U₁ hU₁ => AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
      fX fY x₀ p₁ p₂ iY hiY₁ hiY₂ 𝒲 c hcY U₁.1 hU₁ (γ U₁) (e U₁) (hV U₁) (hH U₁))
  have hg := h5 ⟨U, hU⟩
  exact AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
    fX fY p₁ p₂ hP 𝒲 (𝒲.comap iY) c U hU (γ ⟨U, hU⟩) (e ⟨U, hU⟩) (hV ⟨U, hU⟩) (hH ⟨U, hU⟩) hg

end S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen (solution)
