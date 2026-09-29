-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/21e5a2ad-1690-587c-abc5-c58577501d05

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.ideal_mul Scheme.Modules.pullback Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app IsOpenImmersion Scheme.IdealSheafData.ext_of_iSup_eq_top Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2 Scheme.Modules.tensorHom_app_tensorSections_monoidalV2 Scheme.Modules.leftUnitor_hom_app_tensorSections_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.ideal_mul Modules.pullback Hom Γ Hom.app Modules.Hom topIso Modules.Hom.app IdealSheafData.ext_of_iSup_eq_top affineOpens Modules.pullbackPushforwardAdjunction isBasis_affineOpens Modules Opens homOfLE_ι restrict PresheafOfModules IdealSheafData Modules.zeroSchemeIdeal Modules.IsInvertible Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 Modules.IsInvertible.tensor_monoidalV2 Modules.tensorHom_app_tensorSections_monoidalV2 Modules.leftUnitor_hom_app_tensorSections_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom Hom.app restrictFunctorIsoPullback restrictAdjunction pullbackCongr pullbackPushforwardAdjunction restrict pullbackComp ofUnitSection restrictSection coeff zeroSchemeIdeal tensor IsInvertible pullbackTensorObjIso pullbackTensorUnitObjIso tensorSections map_tensorSections unitSection pullbackLocalSection pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 IsInvertible.tensor_monoidalV2 tensorHom_app_tensorSections_monoidalV2 leftUnitor_hom_app_tensorSections_monoidalV2" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
alias AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection := AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.ideal_mul Scheme.Modules.pullback Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app IsOpenImmersion Scheme.IdealSheafData.ext_of_iSup_eq_top Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2 Scheme.Modules.tensorHom_app_tensorSections_monoidalV2 Scheme.Modules.leftUnitor_hom_app_tensorSections_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.ideal_mul Modules.pullback Hom Γ Hom.app Modules.Hom topIso Modules.Hom.app IdealSheafData.ext_of_iSup_eq_top affineOpens Modules.pullbackPushforwardAdjunction isBasis_affineOpens Modules Opens homOfLE_ι restrict PresheafOfModules IdealSheafData Modules.zeroSchemeIdeal Modules.IsInvertible Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 Modules.IsInvertible.tensor_monoidalV2 Modules.tensorHom_app_tensorSections_monoidalV2 Modules.leftUnitor_hom_app_tensorSections_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom Hom.app restrictFunctorIsoPullback restrictAdjunction pullbackCongr pullbackPushforwardAdjunction restrict pullbackComp ofUnitSection restrictSection coeff zeroSchemeIdeal tensor IsInvertible pullbackTensorObjIso pullbackTensorUnitObjIso tensorSections map_tensorSections unitSection pullbackLocalSection pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 IsInvertible.tensor_monoidalV2 tensorHom_app_tensorSections_monoidalV2 leftUnitor_hom_app_tensorSections_monoidalV2" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback exists_trivialization coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 tensor_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsInvertible
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq := AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor := AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2
end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor"
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
alias AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections := AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections_monoidalV2
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
alias AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections := AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections_monoidalV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2.AlgebraicGeometry Opposite TopologicalSpace"

namespace Ws31C4

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2.AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (k : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map k.op m) = N.presheaf.map k.op (φ.app U m) :=
  PresheafOfModules.naturality_apply φ.val k.op m

theorem restrictFunctorIsoPullback_hom_app_app {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (W : Y.Opens) (m : Γ(M, j ''ᵁ W)) :
    ((restrictFunctorIsoPullback j).hom.app M).app W (show Γ(M.restrict j, W) from m)
      = ((Scheme.Modules.pullback j).obj M).presheaf.map (eqToHom (j.preimage_image_eq W).symm).op
          (pullbackLocalSection j m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) M
  have h' := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun k => Scheme.Modules.Hom.app k (j ''ᵁ W)) h) m

  change ((restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ j ''ᵁ W)
      ((M.restrict j).presheaf.map (eqToHom (j.preimage_image_eq W)).op (show Γ(M.restrict j, W) from m))
    = pullbackLocalSection j m at h'
  rw [app_naturality] at h'
  rw [← h', ← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
    op_id, CategoryTheory.Functor.map_id]
  rfl

section local_computation

variable {L M : X.Modules} (U : X.affineOpens)
  (eL : (Scheme.Modules.pullback U.1.ι).obj L ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
  (eM : (Scheme.Modules.pullback U.1.ι).obj M ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
  (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M)

noncomputable def τL : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback U.1.ι).app L ≪≫ eL

noncomputable def τT : (L ⊗ M).restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback U.1.ι).app (L ⊗ M) ≪≫ pullbackTensorObjIso U.1.ι L M ≪≫ (eL ⊗ᵢ eM) ≪≫ λ_ _

noncomputable abbrev tens : 𝟙_ X.Modules ⟶ L ⊗ M := (λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')

omit U eL eM in
theorem tens_app_one (V : X.Opens) :
    (tens s s').app V (unitSection V) = tensorSections (s.app V (unitSection V)) (s'.app V (unitSection V)) := by
  have h1 : (λ_ (𝟙_ X.Modules)).inv.app V (unitSection V)
      = tensorSections (L := 𝟙_ X.Modules) (M := 𝟙_ X.Modules) (unitSection V) (unitSection V) := by
    have h := leftUnitor_hom_app_tensorSections (N := 𝟙_ X.Modules) (U := V) (1 : Γ(X, V)) (unitSection V)
    rw [one_smul] at h
    have hid : ∀ z : Γ(𝟙_ X.Modules ⊗ 𝟙_ X.Modules, V),
        (λ_ (𝟙_ X.Modules)).inv.app V ((λ_ (𝟙_ X.Modules)).hom.app V z) = z := fun z =>
      CategoryTheory.ConcreteCategory.congr_hom
        (congrArg (fun k => Scheme.Modules.Hom.app k V) ((λ_ (𝟙_ X.Modules)).hom_inv_id)) z
    conv_lhs => rw [← h]
    exact hid _
  change (s ⊗ₘ s').app V ((λ_ (𝟙_ X.Modules)).inv.app V (unitSection V)) = _
  rw [h1, tensorHom_app_tensorSections]

theorem τL_app_restrictSection :
    (τL U eL).hom.app ⊤ (restrictSection s U.1)
      = eL.hom.app ⊤ (((Scheme.Modules.pullback U.1.ι).obj L).presheaf.map
          (eqToHom (U.1.ι.preimage_image_eq ⊤).symm).op (pullbackLocalSection U.1.ι (s.app (U.1.ι ''ᵁ ⊤) (unitSection _)))) := by
  change eL.hom.app ⊤ (((restrictFunctorIsoPullback U.1.ι).hom.app L).app ⊤ (restrictSection s U.1)) = _
  exact congrArg _ (restrictFunctorIsoPullback_hom_app_app U.1.ι L ⊤ _)

theorem τT_app_restrictSection :
    (τT U eL eM).hom.app ⊤ (restrictSection (tens s s') U.1)
      = (show Γ((U.1 : Scheme.{u}), (⊤ : (U.1 : Scheme.{u}).Opens)) from
            eL.hom.app ⊤ (((Scheme.Modules.pullback U.1.ι).obj L).presheaf.map
              (eqToHom (U.1.ι.preimage_image_eq ⊤).symm).op (pullbackLocalSection U.1.ι (s.app (U.1.ι ''ᵁ ⊤) (unitSection _))))) •
        eM.hom.app ⊤ (((Scheme.Modules.pullback U.1.ι).obj M).presheaf.map
              (eqToHom (U.1.ι.preimage_image_eq ⊤).symm).op (pullbackLocalSection U.1.ι (s'.app (U.1.ι ''ᵁ ⊤) (unitSection _)))) := by
  change (λ_ (𝟙_ (U.1 : Scheme.{u}).Modules)).hom.app ⊤ ((eL.hom ⊗ₘ eM.hom).app ⊤ ((pullbackTensorObjIso U.1.ι L M).hom.app ⊤
    (((restrictFunctorIsoPullback U.1.ι).hom.app (L ⊗ M)).app ⊤ (restrictSection (tens s s') U.1)))) = _
  have h0 : restrictSection (tens s s') U.1
      = (show Γ((L ⊗ M).restrict U.1.ι, ⊤) from
          tensorSections (s.app (U.1.ι ''ᵁ ⊤) (unitSection _)) (s'.app (U.1.ι ''ᵁ ⊤) (unitSection _))) :=
    tens_app_one s s' _
  rw [h0]
  erw [restrictFunctorIsoPullback_hom_app_app U.1.ι (L ⊗ M) ⊤]
  rw [app_naturality, pullbackTensorObjIso_hom_app_pullbackLocalSection, map_tensorSections,
    tensorHom_app_tensorSections, leftUnitor_hom_app_tensorSections]

theorem coeff_tens :
    coeff (tens s s') U.1 (τT U eL eM).hom = coeff s U.1 (τL U eL).hom * coeff s' U.1 (τL U eM).hom := by
  simp only [coeff]
  rw [τT_app_restrictSection, τL_app_restrictSection, τL_app_restrictSection]
  rw [← map_mul]
  rfl

include eL eM in
theorem ideal_eq (hL : IsInvertible L) (hM : IsInvertible M) :
    (zeroSchemeIdeal (tens s s')).ideal U = (zeroSchemeIdeal s).ideal U * (zeroSchemeIdeal s').ideal U := by
  obtain ⟨h1, -⟩ := ((hL.tensor hM).coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq (tens s s')).2 U (τT U eL eM)
  obtain ⟨h2, -⟩ := (hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U (τL U eL)
  obtain ⟨h3, -⟩ := (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s').2 U (τL U eM)
  rw [h1, h2, h3, Ideal.span_singleton_mul_span_singleton, coeff_tens]

end local_computation

noncomputable def restrictTriv {L : X.Modules} {U₀ : X.Opens} {U : X.Opens} (h : U ≤ U₀)
    (e : (Scheme.Modules.pullback U₀.ι).obj L ≅ 𝟙_ (U₀ : Scheme.{u}).Modules) :
    (Scheme.Modules.pullback U.ι).obj L ≅ 𝟙_ (U : Scheme.{u}).Modules :=
  (pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((pullbackComp (X.homOfLE h) U₀.ι).app L).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    pullbackTensorUnitObjIso (X.homOfLE h)

theorem main {L M : X.Modules} (hL : IsInvertible L) (hM : IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M) :
    zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')) = zeroSchemeIdeal s * zeroSchemeIdeal s' := by
  have key : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      (zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s'))).ideal U
        = (zeroSchemeIdeal s).ideal U * (zeroSchemeIdeal s').ideal U := by
    intro x
    obtain ⟨UL, hxL, ⟨eL0⟩⟩ := hL.exists_trivialization x
    obtain ⟨UM, hxM, ⟨eM0⟩⟩ := hM.exists_trivialization x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ UL ⊓ UM from ⟨hxL, hxM⟩) (UL ⊓ UM).isOpen
    refine ⟨⟨U, hU⟩, hxU, ?_⟩
    exact ideal_eq ⟨U, hU⟩ (restrictTriv (fun y hy => (hUle hy).1) eL0)
      (restrictTriv (fun y hy => (hUle hy).2) eM0) s s' hL hM
  choose U hxU hU using key
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ (fun x => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · rw [hU, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]

end Ws31C4

theorem solution
    {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M) :
    Scheme.Modules.zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')) =
      Scheme.Modules.zeroSchemeIdeal s * Scheme.Modules.zeroSchemeIdeal s' :=
  Ws31C4.main hL hM s s'

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2 (solution)
