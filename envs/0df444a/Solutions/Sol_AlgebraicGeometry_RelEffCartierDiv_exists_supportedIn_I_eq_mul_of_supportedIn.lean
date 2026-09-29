-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ea574dfe-2f06-5b50-93ca-c68955f3bab1

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒳 S : Scheme.{u}} {f : 𝒳 ⟶ S} [IsSeparated f] (U : 𝒳.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    {r s : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) (E : RelEffCartierDiv f s g) (hD : D.SupportedIn U) (hE : E.SupportedIn U) :
    ∃ F : RelEffCartierDiv f (r + s) g, F.I = D.I * E.I ∧ F.SupportedIn U := by
  set j := pullback.map (U.ι ≫ f) g f g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst f g) ⁻¹' (U : Set 𝒳) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]

  have key : ∀ K : (pullback f g).IdealSheafData, (K.support : Set ↥(pullback f g)) ⊆ (pullback.fst f g) ⁻¹' (U : Set 𝒳) →
      (K.comap j).map j = K := by
    intro K hK
    have hZU : ∀ z : K.subscheme, K.subschemeι z ∈ Set.range ⇑j := by
      intro z
      rw [hrange]
      apply hK
      change K.subschemeι z ∈ (K.support : Set ↥(pullback f g))
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    haveI : IsIso (pullback.snd j K.subschemeι) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      ext z
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Scheme.Pullback.range_snd]
      exact hZU z
    change ((K.comap j).subschemeι ≫ j).ker = K
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition, ← Category.assoc,
      Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

  obtain ⟨DU, hDU⟩ := RelEffCartierDiv.exists_comap_eq_of_supportedIn U D hD
  obtain ⟨EU, hEU⟩ := RelEffCartierDiv.exists_comap_eq_of_supportedIn U E hE
  obtain ⟨FU, hFU⟩ := RelEffCartierDiv.exists_I_eq_mul DU EU
  obtain ⟨F, hFsupp, -, hFmap⟩ := RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated U FU
  refine ⟨F, ?_, hFsupp⟩
  have hsuppDE : ((D.I * E.I).support : Set ↥(pullback f g)) ⊆ (pullback.fst f g) ⁻¹' (U : Set 𝒳) := by
    intro x hx
    rw [Scheme.IdealSheafData.support_mul] at hx
    rcases hx with hx | hx
    · exact hD hx
    · exact hE hx
  calc F.I = FU.I.map j := hFmap
    _ = ((D.I * E.I).comap j).map j := by
        rw [hFU, hDU, hEU, Scheme.IdealSheafData.comap_mul]
    _ = D.I * E.I := key _ hsuppDE

end S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn (solution)
