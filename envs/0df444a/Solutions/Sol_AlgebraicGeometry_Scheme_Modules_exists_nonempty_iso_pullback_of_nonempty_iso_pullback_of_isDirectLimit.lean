-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3fcceecd-591c-5bd6-bf48-08eeb90deab6

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
import Theorems.Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry TopologicalSpace Opposite TensorProduct"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom QuasiCompact Spec Spec.map Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Modules.pullbackCongr IsAffineOpen isCompact_iff_finite_and_eq_biUnion_affineOpens Scheme.Modules QuasiSeparated Scheme.Modules.map_smul quasiSeparated_iff_quasiSeparatedSpace Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.restrictAlgHom exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen Scheme.Hom.appInf Scheme.Hom.appInf_apply Scheme.Hom.appInf_map_left Scheme.Hom.appInf_map_right Scheme.Hom.preimage_mono_inf"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom.id_app Hom Γ affineOpens Hom.comp_app Modules.pullbackCongr isBasis_affineOpens Modules Opens Modules.map_smul restrict Modules.pullbackComp Modules.IsInvertible Modules.pullbackLocalSection TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom TwoAffineOpenCover.restrictAlgHom Hom.appInf Hom.appInf_apply Hom.appInf_map_left Hom.appInf_map_right Hom.preimage_mono_inf"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul Hom.mapPresheaf pullback presheaf Hom.comp_app Hom Hom.id_app pullbackCongr restrict map_smul pullbackComp IsInvertible IsFrameOn tensor pullbackLocalSection pullbackLocalSection_smul map_homOfLE_pullbackLocalSection exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq exists_isFrameOn_of_pullback_iso_unit"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma presheaf_map_homOfLE_refl' {U : X.Opens} (s : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : homOfLE (le_refl U) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]; rfl

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "app_smul mapPresheaf comp_app id_app app" end Hom
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

lemma Hom.app_map_homOfLE {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    φ.app W (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app U s) := by
  have := (Hom.mapPresheaf φ).naturality (homOfLE h).op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, W))) this) s)

private def _root_.AlgebraicGeometry.Scheme.Hom.appInf {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) :
    Γ(X, V ⊓ W) ⟶ Γ(Y, π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W) :=
  π.app (V ⊓ W)

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.appInf" "AlgebraicGeometry.Scheme.Hom.appInf"
private lemma _root_.AlgebraicGeometry.Scheme.Hom.appInf_apply {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) (t : Γ(X, V ⊓ W)) :
    π.appInf V W t = π.app (V ⊓ W) t := rfl

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.appInf_apply" "AlgebraicGeometry.Scheme.Hom.appInf_apply"

private lemma _root_.AlgebraicGeometry.Scheme.Hom.appInf_map_left {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) (y : Γ(X, V)) :
    π.appInf V W (X.presheaf.map (homOfLE inf_le_left).op y) =
      Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V)).op (π.app V y) := by
  have h := congrArg (fun k => (ConcreteCategory.hom k) y) (π.naturality (homOfLE (inf_le_left : V ⊓ W ≤ V)).op)
  simp only [CategoryTheory.comp_apply] at h
  exact h

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.appInf_map_left" "AlgebraicGeometry.Scheme.Hom.appInf_map_left"

private lemma _root_.AlgebraicGeometry.Scheme.Hom.appInf_map_right {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) (y : Γ(X, W)) :
    π.appInf V W (X.presheaf.map (homOfLE inf_le_right).op y) =
      Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ W)).op (π.app W y) := by
  have h := congrArg (fun k => (ConcreteCategory.hom k) y) (π.naturality (homOfLE (inf_le_right : V ⊓ W ≤ W)).op)
  simp only [CategoryTheory.comp_apply] at h
  exact h

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.appInf_map_right" "AlgebraicGeometry.Scheme.Hom.appInf_map_right"
namespace IsFrameOn p2m_export "AlgebraicGeometry.Scheme.Modules.IsFrameOn" "mono map existsUnique pullbackLocalSection" end IsFrameOn
namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.unit_smul {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V)
    {v : Γ(X, U)} (hv : IsUnit v) : IsFrameOn (v • s) V := by
  intro W hWU hWV
  have e : (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op (v • s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘
        (fun g : Γ(X, W) => g * X.presheaf.map (homOfLE hWU).op v) := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.map_smul, mul_smul]
  rw [e]
  exact (hs hWU hWV).comp (Units.mulRight_bijective (hv.map (X.presheaf.map (homOfLE hWU).op).hom).unit)

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.unit_smul"
lemma presheaf_map_homOfLE_refl {M : X.Modules} {U : X.Opens} (s : Γ(M, U)) :
    M.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : homOfLE (le_refl U) = 𝟙 U := rfl
  rw [this, op_id, M.presheaf.map_id]; rfl

namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_self {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    (x : Γ(M, U)) : ∃! g : Γ(X, U), g • s = x := by
  have := hs.existsUnique le_rfl le_rfl x
  simpa only [presheaf_map_homOfLE_refl] using this

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.existsUnique_self"
namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in
private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.smul_left_cancel {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    {g g' : Γ(X, U)} (h : g • s = g' • s) : g = g' :=
  (hs.existsUnique_self (g' • s)).unique h rfl

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.smul_left_cancel"
namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.smul_left_cancel' {M : X.Modules} {U V W : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) {g g' : Γ(X, W)}
    (h : g • M.presheaf.map (homOfLE hWU).op s = g' • M.presheaf.map (homOfLE hWU).op s) : g = g' :=
  (hs.existsUnique hWU hWV _).unique h rfl

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.smul_left_cancel'"
section Trans

variable {L : X.Modules} {ι : Type*} {U : ι → X.Opens} {s : ∀ k, Γ(L, U k)}

namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private def _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.trans (hs : ∀ k, IsFrameOn (s k) (U k)) (i j : ι) : Γ(X, U i ⊓ U j) :=
  ((hs i).existsUnique (inf_le_left : U i ⊓ U j ≤ U i) inf_le_left
    (L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j))).exists.choose

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.trans"
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in
lemma IsFrameOn.trans_spec (hs : ∀ k, IsFrameOn (s k) (U k)) (i j : ι) :
    IsFrameOn.trans hs i j • L.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) =
      L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j) :=
  ((hs i).existsUnique (inf_le_left : U i ⊓ U j ≤ U i) inf_le_left
    (L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j))).exists.choose_spec

p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

lemma IsFrameOn.app_trans_smul_pullbackLocalSection {Y : Scheme.{u}} (π : Y ⟶ X)
    (hs : ∀ k, IsFrameOn (s k) (U k)) (i j : ι) :
    π.appInf (U i) (U j) (IsFrameOn.trans hs i j) •
        ((Scheme.Modules.pullback π).obj L).presheaf.map
          (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (Modules.pullbackLocalSection π (s i)) =
      ((Scheme.Modules.pullback π).obj L).presheaf.map
          (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (Modules.pullbackLocalSection π (s j)) := by
  have h₁ := map_homOfLE_pullbackLocalSection π (inf_le_left : U i ⊓ U j ≤ U i) (s i)
  have h₂ := map_homOfLE_pullbackLocalSection π (inf_le_right : U i ⊓ U j ≤ U j) (s j)
  change π.app (U i ⊓ U j) (IsFrameOn.trans hs i j) •
      ((Scheme.Modules.pullback π).obj L).presheaf.map
        (homOfLE (π.preimage_mono (inf_le_left : U i ⊓ U j ≤ U i))).op (Modules.pullbackLocalSection π (s i)) =
    ((Scheme.Modules.pullback π).obj L).presheaf.map
        (homOfLE (π.preimage_mono (inf_le_right : U i ⊓ U j ≤ U j))).op (Modules.pullbackLocalSection π (s j))
  rw [h₁, h₂, ← pullbackLocalSection_smul, IsFrameOn.trans_spec]

end Trans

lemma exists_units_of_iso {Y : Scheme.{u}} (π : Y ⟶ X) {L₁ L₂ : X.Modules} {ι : Type*} {U : ι → X.Opens}
    {a : ∀ k, Γ(L₁, U k)} {b : ∀ k, Γ(L₂, U k)}
    (ha : ∀ k, IsFrameOn (a k) (U k)) (hb : ∀ k, IsFrameOn (b k) (U k))
    (e : (Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂) :
    ∃ u : ∀ k, Γ(Y, π ⁻¹ᵁ U k), (∀ k, IsUnit (u k)) ∧
      ∀ i j, π.appInf (U i) (U j) (IsFrameOn.trans ha i j) *
          Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (u i) =
        Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (u j) *
          π.appInf (U i) (U j) (IsFrameOn.trans hb i j) := by
  classical
  have hA : ∀ k, IsFrameOn (Modules.pullbackLocalSection π (a k)) (π ⁻¹ᵁ U k) :=
    fun k => (ha k).pullbackLocalSection π
  have hB : ∀ k, IsFrameOn (Modules.pullbackLocalSection π (b k)) (π ⁻¹ᵁ U k) :=
    fun k => (hb k).pullbackLocalSection π
  have hu := fun k => (hB k).existsUnique_self (e.hom.app _ (Modules.pullbackLocalSection π (a k)))
  choose u hu₁ _hu₂ using hu
  have hw := fun k => (hA k).existsUnique_self (e.inv.app _ (Modules.pullbackLocalSection π (b k)))
  choose w hw₁ _hw₂ using hw
  refine ⟨u, fun k => ?_, fun i j => ?_⟩
  · refine IsUnit.of_mul_eq_one (w k) ?_
    apply (hA k).smul_left_cancel
    rw [one_smul, mul_smul, hw₁ k, ← Hom.app_smul, hu₁ k, ← CategoryTheory.comp_apply, ← Hom.comp_app,
      e.hom_inv_id, Hom.id_app]
    rfl
  · apply (hB i).smul_left_cancel' inf_le_left inf_le_left
    rw [mul_smul, mul_smul, IsFrameOn.app_trans_smul_pullbackLocalSection π hb i j,
      ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul, hu₁ i, hu₁ j,
      ← Hom.app_map_homOfLE, ← Hom.app_map_homOfLE, ← Hom.app_smul]
    erw [IsFrameOn.app_trans_smul_pullbackLocalSection π ha i j]

lemma nonempty_iso_of_units {Y : Scheme.{u}} (π : Y ⟶ X) {L₁ L₂ : X.Modules} {ι : Type u} [LinearOrder ι]
    {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    {a : ∀ k, Γ(L₁, U k)} {b : ∀ k, Γ(L₂, U k)}
    (ha : ∀ k, IsFrameOn (a k) (U k)) (hb : ∀ k, IsFrameOn (b k) (U k))
    (v : ∀ k, Γ(Y, π ⁻¹ᵁ U k)) (hv : ∀ k, IsUnit (v k))
    (hcoc : ∀ i j, π.appInf (U i) (U j) (IsFrameOn.trans ha i j) *
          Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (v i) =
        Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (v j) *
          π.appInf (U i) (U j) (IsFrameOn.trans hb i j)) :
    Nonempty ((Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂) := by
  have hA : ∀ k, IsFrameOn (Modules.pullbackLocalSection π (a k)) (π ⁻¹ᵁ U k) :=
    fun k => (ha k).pullbackLocalSection π
  have hB : ∀ k, IsFrameOn (v k • Modules.pullbackLocalSection π (b k)) (π ⁻¹ᵁ U k) :=
    fun k => ((hb k).pullbackLocalSection π).unit_smul (hv k)
  obtain ⟨e, -⟩ := exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq (fun k => π ⁻¹ᵁ U k)
    (π.iSup_preimage_eq_top hU) _ _ hA hB (fun i j _ g hg => by
      have hg' : g = π.appInf (U i) (U j) (IsFrameOn.trans ha i j) :=
        (hA i).smul_left_cancel' inf_le_left inf_le_left
          (hg.trans (IsFrameOn.app_trans_smul_pullbackLocalSection π ha i j).symm)
      rw [hg', Scheme.Modules.map_smul, Scheme.Modules.map_smul, smul_smul, hcoc i j, mul_smul,
        IsFrameOn.app_trans_smul_pullbackLocalSection π hb i j])
  exact ⟨e⟩

namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback exists_trivialization" end IsInvertible
namespace IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsInvertible" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_fin_affine_cover_isFrameOn₂ [CompactSpace X] {L₁ L₂ : X.Modules}
    (h₁ : IsInvertible L₁) (h₂ : IsInvertible L₂) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ k, IsAffineOpen (U k)) ∧ ⨆ k, U k = ⊤ ∧
      ∃ (a : ∀ k, Γ(L₁, U k)) (b : ∀ k, Γ(L₂, U k)),
        (∀ k, IsFrameOn (a k) (U k)) ∧ (∀ k, IsFrameOn (b k) (U k)) := by
  classical
  have key : ∀ x : X, ∃ (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧
      (∃ s : Γ(L₁, W), IsFrameOn s W) ∧ ∃ s : Γ(L₂, W), IsFrameOn s W := by
    intro x
    obtain ⟨V₁, hx₁, ⟨e₁⟩⟩ := h₁.exists_trivialization x
    obtain ⟨V₂, hx₂, ⟨e₂⟩⟩ := h₂.exists_trivialization x
    obtain ⟨s₁, hs₁⟩ := exists_isFrameOn_of_pullback_iso_unit V₁ e₁
    obtain ⟨s₂, hs₂⟩ := exists_isFrameOn_of_pullback_iso_unit V₂ e₂
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V₁ ⊓ V₂ : X.Opens) : Set X) from ⟨hx₁, hx₂⟩) (V₁ ⊓ V₂).isOpen
    have h1 : W ≤ V₁ := fun y hy => (hWV hy).1
    have h2 : W ≤ V₂ := fun y hy => (hWV hy).2
    exact ⟨W, hW, hxW, ⟨L₁.presheaf.map (homOfLE h1).op s₁, (hs₁.map _).mono h1⟩,
      ⟨L₂.presheaf.map (homOfLE h2).op s₂, (hs₂.map _).mono h2⟩⟩
  choose W hWaff hxW hfr₁ hfr₂ using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X)) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨t.card, fun k => W (t.equivFin.symm k), fun k => hWaff _, ?_, fun k => (hfr₁ _).choose,
    fun k => (hfr₂ _).choose, fun k => (hfr₁ _).choose_spec, fun k => (hfr₂ _).choose_spec⟩
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end IsInvertible
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsInvertible.exists_fin_affine_cover_isFrameOn₂"
end AlgebraicGeometry.Scheme.Modules

namespace LimitIsoFil

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Modules"

private theorem _root_.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf {X Y : Scheme.{u}} (π : Y ⟶ X) {W' V W : X.Opens}
    (h : W' ≤ V ⊓ W) : π ⁻¹ᵁ W' ≤ π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W := π.preimage_mono h

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf" "AlgebraicGeometry.Scheme.Hom.preimage_mono_inf"
lemma appInf_res {X Y : Scheme.{u}} (π : Y ⟶ X) (V W W' : X.Opens) (h : W' ≤ V ⊓ W) (t : Γ(X, V ⊓ W)) :
    Y.presheaf.map (homOfLE (π.preimage_mono_inf h)).op (π.appInf V W t) =
      π.app W' (X.presheaf.map (homOfLE h).op t) := by
  have e := congrArg (fun k => (ConcreteCategory.hom k) t) (π.naturality (homOfLE h).op)
  simp only [CategoryTheory.comp_apply] at e
  exact e.symm

lemma res_res {X : Scheme.{u}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

lemma cocycle_res {X Y : Scheme.{u}} (π : Y ⟶ X) {V W W' : X.Opens} (h : W' ≤ V ⊓ W) (t₁ t₂ : Γ(X, V ⊓ W))
    (uV : Γ(Y, π ⁻¹ᵁ V)) (uW : Γ(Y, π ⁻¹ᵁ W))
    (hc : π.appInf V W t₁ * Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V)).op uV =
      Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ W)).op uW * π.appInf V W t₂) :
    π.app W' (X.presheaf.map (homOfLE h).op t₁) *
        Y.presheaf.map (homOfLE (π.preimage_mono (h.trans inf_le_left))).op uV =
      Y.presheaf.map (homOfLE (π.preimage_mono (h.trans inf_le_right))).op uW *
        π.app W' (X.presheaf.map (homOfLE h).op t₂) := by
  have e := congrArg (Y.presheaf.map (homOfLE (π.preimage_mono_inf h)).op) hc
  rw [map_mul, map_mul, appInf_res, appInf_res, res_res, res_res] at e
  exact e

lemma map_swap {K : Type u} [CommRing K] {A A' B B' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra K A] [Algebra K A'] [Algebra K B] [Algebra K B'] (ψ : A →ₐ[K] A') (ρ : B →ₐ[K] B') (x : A ⊗[K] B) :
    Algebra.TensorProduct.map ψ (AlgHom.id K B') (Algebra.TensorProduct.map (AlgHom.id K A) ρ x) =
      Algebra.TensorProduct.map (AlgHom.id K A') ρ (Algebra.TensorProduct.map ψ (AlgHom.id K B) x) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  simp only [AlgHom.comp_id, AlgHom.id_comp]

lemma map_one_tmul {K : Type u} [CommRing K] {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra K A] [Algebra K A'] [Algebra K B] (ψ : A →ₐ[K] A') (b : B) :
    Algebra.TensorProduct.map ψ (AlgHom.id K B) ((1 : A) ⊗ₜ[K] b) = (1 : A') ⊗ₜ[K] b := by
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

lemma exists_ge₂ {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)] {α β : Type*} [Finite α] [Finite β]
    (f : α → J) (g : β → J) : ∃ m : J, (∀ a, f a ≤ m) ∧ ∀ b, g b ≤ m := by
  classical
  haveI := Fintype.ofFinite α; haveI := Fintype.ofFinite β
  obtain ⟨m, hm⟩ := Finset.exists_le (Finset.univ.image f ∪ Finset.univ.image g)
  exact ⟨m, fun a => hm _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ a))),
    fun b => hm _ (Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ b)))⟩

lemma nonempty_iso_pullback_of_fac {X Y Z : Scheme.{u}} (h : X ⟶ Y) (π : Y ⟶ Z) (p : X ⟶ Z) (hp : h ≫ π = p)
    (L₁ L₂ : Z.Modules)
    (e : Nonempty ((Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂)) :
    Nonempty ((Scheme.Modules.pullback p).obj L₁ ≅ (Scheme.Modules.pullback p).obj L₂) := by
  obtain ⟨e⟩ := e
  exact ⟨((Scheme.Modules.pullbackComp h π).app L₁ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₁).symm ≪≫
    (Scheme.Modules.pullback h).mapIso e ≪≫
    ((Scheme.Modules.pullbackComp h π).app L₂ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₂)⟩

end LimitIsoFil

open LimitIsoFil _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛₁ 𝓛₂ : X.Modules) (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (h₂ : Scheme.Modules.IsInvertible 𝓛₂)
    (hiso : Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj 𝓛₂)) :
    ∃ (j : ι) (hij : i ≤ j), Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj 𝓛₂) := by
  classical

  haveI : CompactSpace ↥(Spec (CommRingCat.of (G i))) := (inferInstance : CompactSpace (PrimeSpectrum (G i)))
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace fX
  haveI : QuasiSeparatedSpace ↥X := (quasiSeparated_iff_quasiSeparatedSpace fX).mp inferInstance

  let J : Type u := {j : ι // i ≤ j}
  haveI : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  haveI : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  letI algK : ∀ j : J, Algebra (G i) (G j.1) := fun j => (φ i j.1 j.2).toAlgebra
  letI algR : Algebra (G i) R := (g i).toAlgebra
  letI algGR : ∀ j : J, Algebra (G j.1) R := fun j => (g j.1).toAlgebra
  haveI hST : ∀ j : J, IsScalarTower (G i) (G j.1) R := fun j =>
    IsScalarTower.of_algebraMap_eq (fun r => (IsDirectLimit.compatibility (f := fun i j h => ⇑(φ i j h))
      (g := fun i => ⇑(g i)) i j.1 j.2 r).symm)
  let f' : ∀ j k : J, j ≤ k → G j.1 →ₐ[G i] G k.1 := fun j k h =>
    { toRingHom := φ j.1 k.1 h
      commutes' := fun r => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) j.2 h r }
  haveI hDS : DirectedSystem (fun j : J => G j.1) (fun j k h => ⇑(f' j k h)) :=
    ⟨fun j x => DirectedSystem.map_self (f := fun i j h => ⇑(φ i j h)) x,
     fun k j l hlj hjk x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hlj hjk x⟩
  have hR' : IsDirectLimit (fun j k h => ⇑(f' j k h)) (fun j : J => ⇑(algebraMap (G j.1) R)) := by
    refine ⟨fun x => ?_, fun j k x y hxy => ?_, fun j k h x => ?_⟩
    · obtain ⟨i', y, hy⟩ := hR.surj x
      obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
      exact ⟨⟨k, hik⟩, φ i' k hi'k y, by rw [← hy]; exact hR.compatibility i' k hi'k y⟩
    · obtain ⟨l, hjl, hkl, e⟩ := hR.inj j.1 k.1 x y hxy
      exact ⟨⟨l, j.2.trans hjl⟩, hjl, hkl, e⟩
    · exact hR.compatibility j.1 k.1 h x

  letI instK : ∀ V : X.Opens, Algebra (G i) Γ(X, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom fX V
  letI instKR : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).Opens,
      Algebra (G i) Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫ fX) W
  obtain ⟨εR, hεaff, hε1, -, hε2⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen (G i) fX R

  have hDL : ∀ V : X.Opens, ∃ _ : DirectedSystem (fun j : J => G j.1 ⊗[G i] Γ(X, V))
      (fun j k h => ⇑(Algebra.TensorProduct.map (f' j k h) (AlgHom.id (G i) Γ(X, V)))),
      IsDirectLimit (fun j k h => ⇑(Algebra.TensorProduct.map (f' j k h) (AlgHom.id (G i) Γ(X, V))))
        (fun j : J => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom (G i) (G j.1) R)
          (AlgHom.id (G i) Γ(X, V)))) := fun V =>
    Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit (G i) (fun j : J => G j.1) f' R hR' Γ(X, V)
  choose hDSv hDLv using hDL

  let γR : ∀ (V : X.Opens) (hV : IsAffineOpen V),
      Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ V) ≃ₐ[G i]
      R ⊗[G i] Γ(X, V) := fun V hV => (εR V hV).trans (Algebra.TensorProduct.comm (G i) Γ(X, V) R)
  have γR1 : ∀ (V : X.Opens) (hV : IsAffineOpen V) (s : Γ(X, V)),
      γR V hV ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app V s) =
        (1 : R) ⊗ₜ[G i] s := by
    intro V hV s
    change Algebra.TensorProduct.comm (G i) _ R (εR V hV _) = _
    erw [hε1 V hV s]
    exact Algebra.TensorProduct.comm_tmul _ _ _
  have γR2 : ∀ (V V' : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
      (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (AlgHom.id (G i) R) (Scheme.TwoAffineOpenCover.restrictAlgHom fX hle) (γR V hV s) =
        γR V' hV' ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).preimage_mono
            hle)).op s) := by
    intro V V' hV hV' hle s
    change Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.comm (G i) _ R (εR V hV s)) =
      Algebra.TensorProduct.comm (G i) _ R (εR V' hV' _)
    rw [← hε2 V V' hV hV' hle s]
    exact (Algebra.TensorProduct.comm_comp_map_apply _ _ _).symm

  obtain ⟨n, U, hUaff, hUcov, fa, fb, ha, hb⟩ := h₁.exists_fin_affine_cover_isFrameOn₂ h₂
  have hiso' : Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))))).obj 𝓛₂) :=
    hiso
  obtain ⟨u, hu, hcoc⟩ := exists_units_of_iso
    (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ha hb hiso'.some

  have hWc : ∀ k l : Fin n, IsCompact ((U k ⊓ U l : X.Opens) : Set X) := fun k l =>
    QuasiSeparatedSpace.inter_isCompact _ _ (U k).isOpen (hUaff k).isCompact (U l).isOpen (hUaff l).isCompact
  have hP := fun k l : Fin n => (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := U k ⊓ U l)).1 (hWc k l)
  choose S hSfin hSeq using hP
  have hSle : ∀ (k l : Fin n) (W : ↥(S k l)), ((W : X.affineOpens) : X.Opens) ≤ U k ⊓ U l := fun k l W => by
    rw [hSeq k l]; exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ S k l) => (i : X.Opens)) W.1 W.2
  haveI : ∀ k l : Fin n, Finite ↥(S k l) := fun k l => (hSfin k l).to_subtype

  have s1 := fun k => (hDLv (U k)).surj (γR (U k) (hUaff k) (u k))
  choose j₁ uT huT using s1
  have s2 := fun k => (hDLv (U k)).surj (γR (U k) (hUaff k) ↑(hu k).unit⁻¹)
  choose j₂ wT hwT using s2
  obtain ⟨j₀, hj₁, hj₂⟩ := exists_ge₂ j₁ j₂

  obtain ⟨uT0, huT0⟩ : ∃ uT0 : ∀ k, G j₀.1 ⊗[G i] Γ(X, U k), ∀ k,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom (G i) (G j₀.1) R) (AlgHom.id (G i) Γ(X, U k)) (uT0 k) =
        γR (U k) (hUaff k) (u k) :=
    ⟨fun k => Algebra.TensorProduct.map (f' (j₁ k) j₀ (hj₁ k)) (AlgHom.id (G i) Γ(X, U k)) (uT k), fun k => by
      rw [← huT k]; exact (hDLv (U k)).compatibility (j₁ k) j₀ (hj₁ k) (uT k)⟩
  obtain ⟨wT0, hwT0⟩ : ∃ wT0 : ∀ k, G j₀.1 ⊗[G i] Γ(X, U k), ∀ k,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom (G i) (G j₀.1) R) (AlgHom.id (G i) Γ(X, U k)) (wT0 k) =
        γR (U k) (hUaff k) ↑(hu k).unit⁻¹ :=
    ⟨fun k => Algebra.TensorProduct.map (f' (j₂ k) j₀ (hj₂ k)) (AlgHom.id (G i) Γ(X, U k)) (wT k), fun k => by
      rw [← hwT k]; exact (hDLv (U k)).compatibility (j₂ k) j₀ (hj₂ k) (wT k)⟩

  have s3 : ∀ k, ∃ (l : J) (h h' : j₀ ≤ l),
      Algebra.TensorProduct.map (f' j₀ l h) (AlgHom.id (G i) Γ(X, U k)) (uT0 k * wT0 k) =
      Algebra.TensorProduct.map (f' j₀ l h') (AlgHom.id (G i) Γ(X, U k)) 1 := fun k =>
    (hDLv (U k)).inj j₀ j₀ (uT0 k * wT0 k) 1 (by
      rw [map_mul, huT0, hwT0, map_one, ← map_mul, IsUnit.mul_val_inv, map_one])
  choose j₃ hj₃ hj₃' huw using s3

  have s4 : ∀ (k l : Fin n) (W : ↥(S k l)), ∃ (m : J) (h h' : j₀ ≤ m),
      Algebra.TensorProduct.map (f' j₀ m h) (AlgHom.id (G i) Γ(X, W))
        (((1 : G j₀.1) ⊗ₜ[G i] X.presheaf.map (homOfLE (hSle k l W)).op (IsFrameOn.trans ha k l)) *
          Algebra.TensorProduct.map (AlgHom.id (G i) (G j₀.1))
            (Scheme.TwoAffineOpenCover.restrictAlgHom fX ((hSle k l W).trans inf_le_left)) (uT0 k)) =
      Algebra.TensorProduct.map (f' j₀ m h') (AlgHom.id (G i) Γ(X, W))
        (Algebra.TensorProduct.map (AlgHom.id (G i) (G j₀.1))
            (Scheme.TwoAffineOpenCover.restrictAlgHom fX ((hSle k l W).trans inf_le_right)) (uT0 l) *
          ((1 : G j₀.1) ⊗ₜ[G i] X.presheaf.map (homOfLE (hSle k l W)).op (IsFrameOn.trans hb k l))) := by
    intro k l W
    apply (hDLv W).inj j₀ j₀

    have hc := cocycle_res _ (hSle k l W) (IsFrameOn.trans ha k l) (IsFrameOn.trans hb k l) (u k) (u l) (hcoc k l)
    have hc' := congrArg (γR W W.1.2) hc
    rw [map_mul, map_mul, γR1, γR1, ← γR2 (U k) W (hUaff k) W.1.2 ((hSle k l W).trans inf_le_left),
      ← γR2 (U l) W (hUaff l) W.1.2 ((hSle k l W).trans inf_le_right), ← huT0, ← huT0,
      ← map_swap, ← map_swap] at hc'
    rw [map_mul, map_mul, map_one_tmul, map_one_tmul]
    exact hc'
  choose j₄ hj₄ hj₄' hz using s4

  obtain ⟨m₁, hm₃, hm₄⟩ := exists_ge₂ j₃ (fun p : Σ k : Fin n, Σ l : Fin n, ↥(S k l) => j₄ p.1 p.2.1 p.2.2)
  obtain ⟨js, h0s, h1s⟩ := directed_of (· ≤ ·) j₀ m₁
  letI instKs : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).Opens,
      Algebra (G i) Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))) ≫ fX) W

  obtain ⟨εs, hεsaff, hεs1, -, hεs2⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen (G i) fX (G js.1)
  let γs : ∀ (V : X.Opens) (hV : IsAffineOpen V),
      Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ V) ≃ₐ[G i]
      G js.1 ⊗[G i] Γ(X, V) := fun V hV => (εs V hV).trans (Algebra.TensorProduct.comm (G i) Γ(X, V) (G js.1))
  have γs1 : ∀ (V : X.Opens) (hV : IsAffineOpen V) (s : Γ(X, V)),
      γs V hV ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).app V s) =
        (1 : G js.1) ⊗ₜ[G i] s := by
    intro V hV s
    change Algebra.TensorProduct.comm (G i) _ (G js.1) (εs V hV _) = _
    erw [hεs1 V hV s]
    exact Algebra.TensorProduct.comm_tmul _ _ _
  have γs2 : ∀ (V V' : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
      (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (AlgHom.id (G i) (G js.1)) (Scheme.TwoAffineOpenCover.restrictAlgHom fX hle)
          (γs V hV s) =
        γs V' hV' ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX
            (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).preimage_mono hle)).op s) := by
    intro V V' hV hV' hle s
    change Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.comm (G i) _ (G js.1) (εs V hV s)) =
      Algebra.TensorProduct.comm (G i) _ (G js.1) (εs V' hV' _)
    rw [← hεs2 V V' hV hV' hle s]
    exact (Algebra.TensorProduct.comm_comp_map_apply _ _ _).symm

  let v : ∀ k, Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))),
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ U k) := fun k =>
    (γs (U k) (hUaff k)).symm
      (Algebra.TensorProduct.map (f' j₀ js h0s) (AlgHom.id (G i) Γ(X, U k)) (uT0 k))
  have hγv : ∀ k, γs (U k) (hUaff k) (v k) =
      Algebra.TensorProduct.map (f' j₀ js h0s) (AlgHom.id (G i) Γ(X, U k)) (uT0 k) := fun k =>
    (γs (U k) (hUaff k)).apply_symm_apply _
  have hPuw : ∀ k, Algebra.TensorProduct.map (f' j₀ js h0s) (AlgHom.id (G i) Γ(X, U k)) (uT0 k) *
      Algebra.TensorProduct.map (f' j₀ js h0s) (AlgHom.id (G i) Γ(X, U k)) (wT0 k) = 1 := fun k => by
    have e := congrArg (Algebra.TensorProduct.map (f' (j₃ k) js ((hm₃ k).trans h1s)) (AlgHom.id (G i) Γ(X, U k)))
      (huw k)
    rw [(hDSv (U k)).map_map, (hDSv (U k)).map_map, map_one] at e
    rw [← map_mul]
    exact e
  have hv : ∀ k, IsUnit (v k) := fun k => by
    have e : v k * (γs (U k) (hUaff k)).symm
        (Algebra.TensorProduct.map (f' j₀ js h0s) (AlgHom.id (G i) Γ(X, U k)) (wT0 k)) = 1 := by
      apply (γs (U k) (hUaff k)).injective
      rw [map_mul, hγv, AlgEquiv.apply_symm_apply, map_one]
      exact hPuw k
    exact IsUnit.of_mul_eq_one _ e

  have hcocs : ∀ k l,
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).appInf (U k) (U l)
          (IsFrameOn.trans ha k l) *
        (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map
          (homOfLE (inf_le_left :
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ U k ⊓
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ U l ≤ _)).op
          (v k) =
      (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map
          (homOfLE (inf_le_right :
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ U k ⊓
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ U l ≤ _)).op
          (v l) *
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).appInf (U k) (U l)
          (IsFrameOn.trans hb k l) := by
    intro k l
    apply TopCat.Sheaf.eq_of_locally_eq'
      (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).sheaf
      (fun W : ↥(S k l) => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ
        ((W : X.affineOpens) : X.Opens))
      _ (fun W => homOfLE ((Limits.pullback.fst fX
        (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).preimage_mono_inf (hSle k l W)))
    · intro x hx
      have hx' : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) x ∈
          (⨆ W ∈ S k l, (W : X.Opens)) := by rw [← hSeq k l]; exact hx
      obtain ⟨W, hW⟩ := Opens.mem_iSup.1 hx'
      obtain ⟨hWS, hxW⟩ := Opens.mem_iSup.1 hW
      exact Opens.mem_iSup.2 ⟨⟨W, hWS⟩, hxW⟩
    · intro W
      change (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX
            (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).preimage_mono_inf (hSle k l W))).op (_ * _) =
        (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX
            (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).preimage_mono_inf (hSle k l W))).op (_ * _)
      rw [map_mul, map_mul, appInf_res _ _ _ _ (hSle k l W), appInf_res _ _ _ _ (hSle k l W), res_res, res_res]
      apply (γs W W.1.2).injective
      rw [map_mul, map_mul, γs1, γs1, ← γs2 (U k) W (hUaff k) W.1.2 ((hSle k l W).trans inf_le_left),
        ← γs2 (U l) W (hUaff l) W.1.2 ((hSle k l W).trans inf_le_right), hγv, hγv, ← map_swap, ← map_swap,
        ← map_one_tmul (f' j₀ js h0s) (X.presheaf.map (homOfLE (hSle k l W)).op (IsFrameOn.trans ha k l)),
        ← map_one_tmul (f' j₀ js h0s) (X.presheaf.map (homOfLE (hSle k l W)).op (IsFrameOn.trans hb k l)),
        ← map_mul, ← map_mul]
      have e := congrArg (Algebra.TensorProduct.map (f' (j₄ k l W) js ((hm₄ ⟨k, l, W⟩).trans h1s))
        (AlgHom.id (G i) Γ(X, ((W : X.affineOpens) : X.Opens)))) (hz k l W)
      rw [(hDSv _).map_map, (hDSv _).map_map] at e
      exact e

  have key := nonempty_iso_of_units
    (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) (ι := ULift.{u} (Fin n))
    (U := fun k => U k.down) (by rw [← hUcov, iSup_ulift]) (a := fun k => fa k.down) (b := fun k => fb k.down)
    (fun k => ha k.down) (fun k => hb k.down) (fun k => v k.down) (fun k => hv k.down)
    (fun k l => hcocs k.down l.down)
  exact ⟨js.1, js.2, key⟩

end

end S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit (solution)
