-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/aa875629-fdd7-5b6a-bf36-e0a6de08b957

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_baseChange
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsOpenImmersion.lift Surjective SmoothOfRelativeDimension IsProper morphismRestrict_ι morphismRestrict_base_coe Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom GeometricallyIntegral Scheme.Hom.support_ker LocallyOfFiniteType GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Scheme Spec.map_surjective IsOpenImmersion Scheme.Hom.comp_base isIntegral_of_isOpenImmersion IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId smoothOfRelativeDimension_comp Scheme.Modules Scheme.Opens isIso_of_isClosedImmersion_of_surjective IsOpenImmersion.lift_fac Scheme.Hom.comp_apply geometrically Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv.idealModule RelEffCartierDiv.lineBundle RelEffCartierDiv graphOver graphOver_fst RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I RelEffCartierDiv.supportedIn_iff Scheme.Modules.pullbackTensorObjIso RelEffCartierDiv.isInvertible_I_of_supportedIn RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing geometricallyIntegral_of_isAlgClosed"
p2m_open "AlgebraicGeometry"

namespace RelEffCartierDiv p2m_export "AlgebraicGeometry.RelEffCartierDiv" "idealModule lineBundle ext I ofPoint ofPoint_I SupportedIn supportedIn_iff isInvertible_I_of_supportedIn nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset" end RelEffCartierDiv
p2m_open_scoped "AlgebraicGeometry.RelEffCartierDiv" in

theorem RelEffCartierDiv.coe_support_ofPoint_I'
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) = Set.range (graphOver f a ha) := by
  rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker,
    (graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq]

p2m_open_scoped "AlgebraicGeometry.RelEffCartierDiv" in

theorem RelEffCartierDiv.supportedIn_ofPoint_of_range_subset'
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (haU : Set.range a ⊆ (U : Set 𝒞)) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  rw [RelEffCartierDiv.supportedIn_iff]
  intro x hx
  have hx' : x ∈ ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) := hx
  rw [RelEffCartierDiv.coe_support_ofPoint_I'] at hx'
  obtain ⟨y, rfl⟩ := hx'
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact haU ⟨y, rfl⟩

p2m_open_scoped "AlgebraicGeometry.RelEffCartierDiv" in

theorem RelEffCartierDiv.ofPoint_congr'
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (h : a = a') (ha : a ≫ f = g) (ha' : a' ≫ f = g) :
    RelEffCartierDiv.ofPoint f a ha = RelEffCartierDiv.ofPoint f a' ha' := by
  subst h; rfl

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Opens.range_ι Hom empty Hom.support_ker Hom.comp_base Modules.pullbackCongr Modules.pullbackId Modules Opens Hom.comp_apply Modules.pullbackComp Modules.IsInvertible Modules.pullbackTensorObjIso Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image app support_ker comp_base cover isClosedEmbedding comp_apply" end Scheme.Hom
namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private def _root_.AlgebraicGeometry.Scheme.Hom.complRange {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.complRange"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in
lemma Scheme.Hom.mem_complRange_iff {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (z : X) :
    z ∈ i.complRange ↔ z ∉ Set.range i.base := Iff.rfl

section TwoGlued

variable {k : Type u} [Field k] {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
  (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (i₁ : SchemeHomOver c₁ x) (i₂ : C₂ ⟶ X)
  [IsClosedImmersion i₁.1] [IsClosedImmersion i₂]

theorem isIso_morphismRestrict_complRange_of_twoGlued [IsReduced X]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.base) :
    IsIso (i₁.1 ∣_ i₂.complRange) := by
  haveI : Surjective (i₁.1 ∣_ i₂.complRange) := ⟨fun w => by
    obtain ⟨c, hc⟩ : w.1 ∈ Set.range i₁.1.base := (hjs w.1).resolve_right w.2
    refine ⟨⟨c, show i₁.1.base c ∈ i₂.complRange by rw [hc]; exact w.2⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hc⟩
  exact isIso_of_isClosedImmersion_of_surjective _

theorem smoothOfRelativeDimension_one_complRange_of_twoGlued [IsReduced X] [SmoothOfRelativeDimension 1 c₁]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.base) :
    SmoothOfRelativeDimension 1 (i₂.complRange.ι ≫ x) := by
  haveI := isIso_morphismRestrict_complRange_of_twoGlued x c₁ i₁ i₂ hjs
  have heq : i₂.complRange.ι ≫ x = inv (i₁.1 ∣_ i₂.complRange) ≫ ((i₁.1 ⁻¹ᵁ i₂.complRange).ι ≫ c₁) := by
    rw [← IsIso.inv_hom_id_assoc (i₁.1 ∣_ i₂.complRange) (i₂.complRange.ι ≫ x),
      ← Category.assoc (i₁.1 ∣_ i₂.complRange), morphismRestrict_ι, Category.assoc, i₁.2]
  rw [heq]
  haveI : SmoothOfRelativeDimension 1 ((i₁.1 ⁻¹ᵁ i₂.complRange).ι ≫ c₁) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

theorem isIntegral_complRange_of_twoGlued [IsReduced X] [GeometricallyIntegral c₁]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.base) [Nonempty (i₂.complRange : Scheme.{u})] :
    IsIntegral (i₂.complRange : Scheme.{u}) := by
  haveI := isIso_morphismRestrict_complRange_of_twoGlued x c₁ i₁ i₂ hjs
  haveI : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  haveI : Nonempty ((i₁.1 ⁻¹ᵁ i₂.complRange : C₁.Opens) : Scheme.{u}) :=
    ⟨(inv (i₁.1 ∣_ i₂.complRange)).base (Classical.arbitrary _)⟩
  haveI : IsIntegral ((i₁.1 ⁻¹ᵁ i₂.complRange : C₁.Opens) : Scheme.{u}) :=
    isIntegral_of_isOpenImmersion (i₁.1 ⁻¹ᵁ i₂.complRange).ι
  exact isIntegral_of_isOpenImmersion (inv (i₁.1 ∣_ i₂.complRange))

end TwoGlued

section AbelJacobi

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
  [IsSeparated x] [LocallyOfFiniteType x]
  (W : X.Opens) [SmoothOfRelativeDimension 1 (W.ι ≫ x)] [IsIntegral (W : Scheme.{u})]

namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle IsAlgEquivZero FibrewiseAlgEquivZero" end RelPicard
p2m_open_scoped "AlgebraicGeometry.RelPicard" in

theorem RelPicard.isAlgEquivZero_ofPoint_lineBundle_tensor_ofPoint_idealModule
    (p q : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ x = 𝟙 _) (hq : q ≫ x = 𝟙 _)
    (hpW : Set.range p.base ⊆ (W : Set X)) (hqW : Set.range q.base ⊆ (W : Set X)) :
    IsAlgEquivZero (pullback.snd x (𝟙 _))
      ((RelEffCartierDiv.ofPoint x p hp).lineBundle ⊗ (RelEffCartierDiv.ofPoint x q hq).idealModule) := by

  let h : (W : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := W.ι ≫ x
  haveI : LocallyOfFiniteType h := inferInstance
  haveI : GeometricallyIntegral h := geometricallyIntegral_of_isAlgClosed h

  have hpW' : Set.range p.base ⊆ Set.range W.ι.base := by rwa [Scheme.Opens.range_ι]
  have hqW' : Set.range q.base ⊆ Set.range W.ι.base := by rwa [Scheme.Opens.range_ι]
  let pw : Spec (CommRingCat.of k) ⟶ W := IsOpenImmersion.lift W.ι p hpW'
  let qw : Spec (CommRingCat.of k) ⟶ W := IsOpenImmersion.lift W.ι q hqW'
  have hpw : pw ≫ W.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hqw : qw ≫ W.ι = q := IsOpenImmersion.lift_fac _ _ _
  let t₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h := ⟨pw, by rw [← Category.assoc, hpw, hp]⟩
  let t₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h := ⟨qw, by rw [← Category.assoc, hqw, hq]⟩

  let σ : SchemeHomOver h x := ⟨W.ι, rfl⟩
  let τ : SchemeHomOver h x := ⟨h ≫ q, by rw [Category.assoc, hq, Category.comp_id]⟩
  have hσW : Set.range σ.1.base ⊆ (W : Set X) := by rw [Scheme.Opens.range_ι]
  have hτW : Set.range τ.1.base ⊆ (W : Set X) := by
    rintro _ ⟨w, rfl⟩
    refine hqW ⟨h.base w, ?_⟩
    show q.base (h.base w) = (h ≫ q).base w
    rw [Scheme.Hom.comp_base]; rfl

  let M : (pullback x h).Modules :=
    (RelEffCartierDiv.ofPoint x σ.1 σ.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint x τ.1 τ.2).idealModule
  have hIσ := RelEffCartierDiv.isInvertible_I_of_supportedIn W (RelEffCartierDiv.ofPoint x σ.1 σ.2)
    (RelEffCartierDiv.supportedIn_ofPoint_of_range_subset' x σ.1 σ.2 W hσW)
  have hIτ := RelEffCartierDiv.isInvertible_I_of_supportedIn W (RelEffCartierDiv.ofPoint x τ.1 τ.2)
    (RelEffCartierDiv.supportedIn_ofPoint_of_range_subset' x τ.1 τ.2 W hτW)
  have hM : Scheme.Modules.IsInvertible M := hIσ.isInvertible_invModule.tensor hIτ.isInvertible_module

  have ht₀σ : (t₀.1 ≫ σ.1) ≫ x = 𝟙 _ := by rw [Category.assoc, σ.2, t₀.2]
  have ht₀τ : (t₀.1 ≫ τ.1) ≫ x = 𝟙 _ := by rw [Category.assoc, τ.2, t₀.2]
  have ht₁σ : (t₁.1 ≫ σ.1) ≫ x = 𝟙 _ := by rw [Category.assoc, σ.2, t₁.2]
  have ht₁τ : (t₁.1 ≫ τ.1) ≫ x = 𝟙 _ := by rw [Category.assoc, τ.2, t₁.2]
  obtain ⟨⟨eσ₀⟩, -⟩ := RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    k x W σ hσW t₀ ht₀σ
  obtain ⟨-, ⟨eτ₀⟩⟩ := RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    k x W τ hτW t₀ ht₀τ
  obtain ⟨⟨eσ₁⟩, -⟩ := RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    k x W σ hσW t₁ ht₁σ
  obtain ⟨-, ⟨eτ₁⟩⟩ := RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    k x W τ hτW t₁ ht₁τ

  have e₀σ : t₀.1 ≫ σ.1 = q := hqw
  have e₀τ : t₀.1 ≫ τ.1 = q := by
    show qw ≫ (W.ι ≫ x) ≫ q = q
    rw [← Category.assoc, ← Category.assoc, hqw, hq, Category.id_comp]
  have e₁σ : t₁.1 ≫ σ.1 = p := hpw
  have e₁τ : t₁.1 ≫ τ.1 = q := by
    show pw ≫ (W.ι ≫ x) ≫ q = q
    rw [← Category.assoc, ← Category.assoc, hpw, hp, Category.id_comp]

  have hIq := RelEffCartierDiv.isInvertible_I_of_supportedIn W (RelEffCartierDiv.ofPoint x q hq)
    (RelEffCartierDiv.supportedIn_ofPoint_of_range_subset' x q hq W hqW)
  obtain ⟨-, ⟨eunit⟩⟩ := hIq.isInvertible_module.dual

  let fst := pullback.fst x (𝟙 (Spec (CommRingCat.of k)))
  let L : (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules :=
    (RelEffCartierDiv.ofPoint x p hp).lineBundle ⊗ (RelEffCartierDiv.ofPoint x q hq).idealModule
  let eFst : (Scheme.Modules.pullback fst).obj ((Scheme.Modules.pullback (inv fst)).obj L) ≅ L :=
    (Scheme.Modules.pullbackComp fst (inv fst)).app L ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id fst)).app L ≪≫ (Scheme.Modules.pullbackId _).app L
  have key : IsAlgEquivZero x ((Scheme.Modules.pullback (inv fst)).obj L) := by
    refine ⟨W, h, inferInstance, inferInstance, M, hM, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
    ·
      refine Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eσ₀ ⊗ᵢ eτ₀) ≪≫
        (eqToIso (congrArg RelEffCartierDiv.lineBundle (RelEffCartierDiv.ofPoint_congr' x e₀σ ht₀σ hq)) ⊗ᵢ
          eqToIso (congrArg RelEffCartierDiv.idealModule (RelEffCartierDiv.ofPoint_congr' x e₀τ ht₀τ hq))) ≪≫
        β_ _ _ ≪≫ eunit
    ·
      refine Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eσ₁ ⊗ᵢ eτ₁) ≪≫
        (eqToIso (congrArg RelEffCartierDiv.lineBundle (RelEffCartierDiv.ofPoint_congr' x e₁σ ht₁σ hp)) ⊗ᵢ
          eqToIso (congrArg RelEffCartierDiv.idealModule (RelEffCartierDiv.ofPoint_congr' x e₁τ ht₁τ hq))) ≪≫
        eFst.symm
  have hfst : fst ≫ x = pullback.snd x (𝟙 (Spec (CommRingCat.of k))) := by rw [pullback.condition, Category.comp_id]
  exact (key.pullback fst hfst).of_iso eFst

end AbelJacobi

end AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x)
    (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
    (hP : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
    (hQ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base) :
    ∃ M : RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of k))),
      Nonempty (M.L ≅
        (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
          (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule) ∧
      FibrewiseAlgEquivZero M := by

  haveI : IsReduced X := hXred

  haveI := smoothOfRelativeDimension_one_complRange_of_twoGlued x c₁ i₁ i₂.1 hjs
  have hrange : ∀ (R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      (R.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      Set.range (R.1 ≫ i₁.1).base ⊆ (i₂.1.complRange : Set X) := by
    rintro R hR _ ⟨pt, rfl⟩
    obtain rfl : pt = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact hR
  have hPW := hrange P hP
  have hQW := hrange Q hQ
  haveI : Nonempty (i₂.1.complRange : Scheme.{u}) := ⟨(⟨_, hPW ⟨IsLocalRing.closedPoint k, rfl⟩⟩ : i₂.1.complRange)⟩
  haveI := isIntegral_complRange_of_twoGlued x c₁ i₁ i₂.1 hjs
  have hPx : (P.1 ≫ i₁.1) ≫ x = 𝟙 _ := by rw [Category.assoc, i₁.2]; exact P.2
  have hQx : (Q.1 ≫ i₁.1) ≫ x = 𝟙 _ := by rw [Category.assoc, i₁.2]; exact Q.2
  have key := RelPicard.isAlgEquivZero_ofPoint_lineBundle_tensor_ofPoint_idealModule x i₂.1.complRange
    (P.1 ≫ i₁.1) (Q.1 ≫ i₁.1) hPx hQx hPW hQW

  have hIP := RelEffCartierDiv.isInvertible_I_of_supportedIn i₂.1.complRange (RelEffCartierDiv.ofPoint x _ hPx)
    (RelEffCartierDiv.supportedIn_ofPoint_of_range_subset' x _ hPx _ hPW)
  have hIQ := RelEffCartierDiv.isInvertible_I_of_supportedIn i₂.1.complRange (RelEffCartierDiv.ofPoint x _ hQx)
    (RelEffCartierDiv.supportedIn_ofPoint_of_range_subset' x _ hQx _ hQW)
  have hL : Scheme.Modules.IsInvertible
      ((RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) hPx).lineBundle ⊗ (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) hQx).idealModule) :=
    hIP.isInvertible_invModule.tensor hIQ.isInvertible_module

  refine ⟨⟨_, hL, ?_⟩, ⟨Iso.refl _⟩, ?_⟩
  · exact Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing (hL.pullback _)
  ·
    intro K _ _ s
    obtain ⟨φ, rfl⟩ := Spec.map_surjective s
    letI : Algebra k K := φ.hom.toAlgebra
    exact key.baseChange K

end S_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves (solution)
