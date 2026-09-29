-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2ced94e8-c19e-5282-adbc-eed3dbe503a4

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
import Theorems.Thm_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp.AlgebraicGeometry Opposite HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsOpenImmersion.lift Spec.map_inj Proj.opensRange_awayι Scheme.Hom Scheme.Hom.appLE_comp_appLE Proj.basicOpenIsoSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Proj.awayι Spec.map_surjective Scheme.Hom.appTop Scheme.Hom.comp_appLE IsOpenImmersion Proj Spec.map_injective SpecMap_ΓSpecIso_hom isAffineOpen_top Spec.map_id Proj.basicOpenIsoSpec_inv_ι Proj.basicOpen IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Opens.toSpecΓ_top Scheme.Opens.toSpecΓ_SpecMap_appLE Proj.iSup_basicOpen_eq_top Scheme.Hom.comp_preimage Proj.awayToSection Proj.basicOpenIsoSpec_hom IsOpenImmersion.lift_fac toSpecΓ Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.ProjPresentation ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.ratio_self Scheme.Modules.toUnitSection Scheme.Modules.pullbackSection Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq"
namespace P2mWs3HypEq
p2m_open "AlgebraicGeometry"

theorem appLE_hom_eq_of_eq {X Y : Scheme.{u}} {F G : X ⟶ Y} (hFG : F = G) (U : Y.Opens) (V : X.Opens)
    (h1 : V ≤ F ⁻¹ᵁ U) (h2 : V ≤ G ⁻¹ᵁ U) (y : Γ(Y, U)) :
    (F.appLE U V h1).hom y = (G.appLE U V h2).hom y := by
  subst hFG; rfl

theorem appLE_hom_app {X Y Z : Scheme.{u}} (T : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : X.Opens)
    (h : V ≤ T ⁻¹ᵁ (g ⁻¹ᵁ U)) (y : Γ(Z, U)) :
    (T.appLE (g ⁻¹ᵁ U) V h).hom ((g.app U).hom y) =
      ((T ≫ g).appLE U V (by rwa [Scheme.Hom.comp_preimage])).hom y := by
  rw [Scheme.Hom.comp_appLE T g U V]
  rfl

theorem appLE_hom_appLE {X Y Z : Scheme.{u}} (T : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hW : W ≤ g ⁻¹ᵁ U) (h : V ≤ T ⁻¹ᵁ W) (y : Γ(Z, U)) :
    (T.appLE W V h).hom ((g.appLE U W hW).hom y) =
      ((T ≫ g).appLE U V (h.trans ((TopologicalSpace.Opens.map T.base).map (homOfLE hW)).le)).hom y := by
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem specMap_appLE_top {R S : CommRingCat.{u}} (g : R ⟶ S) (h : (⊤ : (Spec S).Opens) ≤ Spec.map g ⁻¹ᵁ ⊤) (r : R) :
    ((Spec.map g).appLE ⊤ ⊤ h).hom ((Scheme.ΓSpecIso R).inv.hom r) = (Scheme.ΓSpecIso S).inv.hom (g.hom r) := by
  have hop : (homOfLE h).op = 𝟙 (op (⊤ : (Spec S).Opens)) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have e1 : ((Spec.map g).appLE ⊤ ⊤ h).hom ((Scheme.ΓSpecIso R).inv.hom r) =
      (Spec.map g).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, hop]
    erw [CategoryTheory.Functor.map_id]
    rfl
  rw [e1, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

theorem appLE_awayToSection_of_fac {X : Scheme.{u}} {A τ : Type u} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜]
    {g : A} {m : ℕ} (g_deg : g ∈ 𝒜 m) (hm : 0 < m)
    (φ : X ⟶ Proj 𝒜) {V : X.Opens} (hV : IsAffineOpen V) (ψ : Away 𝒜 g →+* Γ(X, V))
    (hfac : V.ι ≫ φ = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Proj.awayι 𝒜 g g_deg hm)
    (hle : V ≤ φ ⁻¹ᵁ Proj.basicOpen 𝒜 g) (z : Away 𝒜 g) :
    φ.appLE (Proj.basicOpen 𝒜 g) V hle (Proj.awayToSection 𝒜 g z) = ψ z := by
  have h1 : φ.resLE _ V hle =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ (Proj.basicOpenIsoSpec 𝒜 g g_deg hm).inv := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 g).ι, Scheme.Hom.resLE_comp_ι, hfac]
    simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have h2 := Scheme.Opens.toSpecΓ_SpecMap_appLE φ (Proj.basicOpen 𝒜 g) V hle
  rw [h1] at h2
  have h3 : V.toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 g ≫ φ.appLE (Proj.basicOpen 𝒜 g) V hle) =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) := by
    have e : (Proj.basicOpen 𝒜 g).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 g) =
        (Proj.basicOpenIsoSpec 𝒜 g g_deg hm).hom := by
      rw [Proj.basicOpenIsoSpec_hom]; rfl
    rw [Spec.map_comp, reassoc_of% h2]
    try simp only [Category.assoc]
    rw [e, Iso.inv_hom_id, Category.comp_id]
  haveI : IsIso V.toSpecΓ := by rw [← hV.isoSpec_hom]; infer_instance
  rw [cancel_epi] at h3
  have h4 := Spec.map_inj.mp h3
  have := congr_arg (fun t => t.hom z) h4
  simpa using this

theorem appLE_awayToSection_specMap {A τ : Type u} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜] {g : A} {m : ℕ} (g_deg : g ∈ 𝒜 m) (hm : 0 < m)
    {B : Type u} [CommRing B] (φ : CommRingCat.of (Away 𝒜 g) ⟶ CommRingCat.of B)
    (F : Spec (CommRingCat.of B) ⟶ Proj 𝒜) (hF : F = Spec.map φ ≫ Proj.awayι 𝒜 g g_deg hm)
    (hle : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ F ⁻¹ᵁ Proj.basicOpen 𝒜 g) (z : Away 𝒜 g) :
    (F.appLE (Proj.basicOpen 𝒜 g) ⊤ hle).hom (Proj.awayToSection 𝒜 g z) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ.hom z) := by
  have hfac : (⊤ : (Spec (CommRingCat.of B)).Opens).ι ≫ F =
      (⊤ : (Spec (CommRingCat.of B)).Opens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.comp φ.hom)) ≫
          Proj.awayι 𝒜 g g_deg hm := by
    rw [Scheme.Opens.toSpecΓ_top, ← SpecMap_ΓSpecIso_hom, hF]
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc (Spec.map _), ← Spec.map_comp]
    congr 2
    ext x
    show φ.hom x = ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom (φ.hom x)
    rw [Iso.inv_hom_id]
    rfl
  exact appLE_awayToSection_of_fac 𝒜 g_deg hm F (isAffineOpen_top (Spec (CommRingCat.of B))) _ hfac hle z

theorem exists_unitHom_app_eq {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) :
    ∃ θ : 𝟙_ X.Modules ⟶ M, θ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  let s : M.sections := PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m)
    (fun U V i => by
      change M.presheaf.map i (M.presheaf.map (homOfLE _).op m) = M.presheaf.map (homOfLE _).op m
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl)
  refine ⟨(SheafOfModules.unitHomEquiv M).symm s, ?_⟩
  set θ : 𝟙_ X.Modules ⟶ M := (SheafOfModules.unitHomEquiv M).symm s with hθ
  have hl : s.val (Opposite.op ⊤) = m := by
    change M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
    rw [this]
    simp
  have e1 : (SheafOfModules.unitHomEquiv M) θ = s := by rw [hθ]; exact Equiv.apply_symm_apply _ _
  have e2 : ((SheafOfModules.unitHomEquiv M) θ).val (Opposite.op ⊤) = s.val (Opposite.op ⊤) := by rw [e1]
  have e3 := SheafOfModules.unitHomEquiv_apply_coe M θ (Opposite.op ⊤)
  exact e3.symm.trans (e2.trans hl)

section Pres

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} {𝓝 : X.Modules}
  {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k
local notation "D₊" i => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

theorem exists_chart {B : Type u} [CommRing B] (t : Spec (CommRingCat.of B) ⟶ X)
    (x₀ : Spec (CommRingCat.of B)) (hx : ∀ y : Spec (CommRingCat.of B), y = x₀) :
    ∃ i : Fin (N + 1), (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ D₊ i) := by
  have hcover := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k) (ProjSpace.irrelevant_le_span_X k N)
  have hxmem : (t ≫ 𝔓.toProj).base x₀ ∈
      (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcover, TopologicalSpace.Opens.mem_iSup] at hxmem
  obtain ⟨i, hi⟩ := hxmem
  refine ⟨i, fun y _ => ?_⟩
  show 𝔓.toProj.base (t.base y) ∈ D₊ i
  rw [hx y]; exact hi

theorem exists_fac {B : Type u} [CommRing B] (t : Spec (CommRingCat.of B) ⟶ X) (i : Fin (N + 1))
    (ht : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ D₊ i)) :
    ∃ φ : CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) ⟶ CommRingCat.of B,
      t ≫ 𝔓.toProj = Spec.map φ ≫ Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos := by
  have hr : Set.range (t ≫ 𝔓.toProj).base ⊆
      Set.range (Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos).base := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ D₊ i) := ht (Set.mem_univ y)
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    (IsOpenImmersion.lift (Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos) (t ≫ 𝔓.toProj) hr)
  exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩

theorem apply_algebraMap_of_fac {B : Type u} [CommRing B] [Algebra k B] (t : Spec (CommRingCat.of B) ⟶ X)
    (htf : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) (i : Fin (N + 1))
    (φ : CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) ⟶ CommRingCat.of B)
    (hφ : t ≫ 𝔓.toProj = Spec.map φ ≫ Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos) (r : k) :
    φ.hom (algebraMap k (Away 𝒜 (MvPolynomial.X i)) r) = algebraMap k B r := by
  have h1 : t ≫ 𝔓.toProj ≫ ProjSpace.π k N = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [𝔓.toProj_π, htf]
  rw [reassoc_of% hφ, ProjSpace.awayι_comp_π, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  have := congr_arg (fun g => g.hom r) h2
  simpa using this

noncomputable def algHomOfFac {B : Type u} [CommRing B] [Algebra k B] (t : Spec (CommRingCat.of B) ⟶ X)
    (htf : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) (i : Fin (N + 1))
    (φ : CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) ⟶ CommRingCat.of B)
    (hφ : t ≫ 𝔓.toProj = Spec.map φ ≫ Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos) :
    Away 𝒜 (MvPolynomial.X i) →ₐ[k] B :=
  { φ.hom with commutes' := apply_algebraMap_of_fac 𝔓 t htf i φ hφ }

theorem algHomOfFac_apply {B : Type u} [CommRing B] [Algebra k B] (t : Spec (CommRingCat.of B) ⟶ X)
    (htf : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) (i : Fin (N + 1))
    (φ : CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) ⟶ CommRingCat.of B)
    (hφ : t ≫ 𝔓.toProj = Spec.map φ ≫ Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos)
    (z : Away 𝒜 (MvPolynomial.X i)) :
    algHomOfFac 𝔓 t htf i φ hφ z = φ.hom z := rfl

theorem ofHom_algHomOfFac {B : Type u} [CommRing B] [Algebra k B] (t : Spec (CommRingCat.of B) ⟶ X)
    (htf : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) (i : Fin (N + 1))
    (φ : CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) ⟶ CommRingCat.of B)
    (hφ : t ≫ 𝔓.toProj = Spec.map φ ≫ Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos) :
    CommRingCat.ofHom (algHomOfFac 𝔓 t htf i φ hφ).toRingHom = φ := rfl

theorem pullbackSection_eq_zero_iff_sum_eq_zero {B : Type u} [CommRing B] [Algebra k B]
    (t : Spec (CommRingCat.of B) ⟶ X) (htf : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (i : Fin (N + 1)) (ht : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ D₊ i))
    (φ : CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) ⟶ CommRingCat.of B)
    (hφ : t ≫ 𝔓.toProj = Spec.map φ ≫ Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one k N i) one_pos)
    (c : Fin (N + 1) → k) (s : 𝟙_ X.Modules ⟶ 𝓝)
    (hs : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c j))) • 𝔓.σ j) :
    Scheme.Modules.pullbackSection t s = 0 ↔ ∑ j, algebraMap k B (c j) * φ.hom (ProjSpace.ratio k N i j) = 0 := by
  rw [Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero 𝔓 s c hs t i ht]
  have hφtop : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (t ≫ 𝔓.toProj) ⁻¹ᵁ D₊ i := by
    rwa [Scheme.Hom.comp_preimage]
  have hκ : ∀ j, (t.appLE (𝔓.toProj ⁻¹ᵁ D₊ i) ⊤ ht).hom
      ((f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ D₊ i) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c j))) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap k B (c j)) := by
    intro j
    rw [appLE_hom_appLE t f ⊤ _ ⊤ le_top ht, appLE_hom_eq_of_eq htf ⊤ ⊤ _ le_top,
      specMap_appLE_top]
    rfl
  have hu : ∀ j, (t.appLE (𝔓.toProj ⁻¹ᵁ D₊ i) ⊤ ht).hom
      ((𝔓.toProj.app (D₊ i)).hom (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio k N i j))) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ.hom (ProjSpace.ratio k N i j)) := by
    intro j
    rw [appLE_hom_app t 𝔓.toProj (D₊ i) ⊤ ht]
    exact appLE_awayToSection_specMap _ (ProjSpace.X_mem_one k N i) one_pos φ (t ≫ 𝔓.toProj) hφ hφtop _
  have hsum : (t.appLE (𝔓.toProj ⁻¹ᵁ D₊ i) ⊤ ht).hom
      (∑ j, (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ D₊ i) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c j)) *
        (𝔓.toProj.app (D₊ i)).hom (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio k N i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (∑ j, algebraMap k B (c j) * φ.hom (ProjSpace.ratio k N i j)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hκ, hu]
  rw [hsum]
  exact map_eq_zero_iff _ (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv.injective

theorem sum_test_mul {B : Type u} [CommRing B] (l i : Fin (N + 1)) (r : B) (x : Fin (N + 1) → B) :
    ∑ j, ((if j = l then (1 : B) else 0) - r * (if j = i then 1 else 0)) * x j = x l - r * x i := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_assoc, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← Finset.mul_sum]

end Pres

end AlgebraicGeometry.P2mWs3HypEq

open AlgebraicGeometry.P2mWs3HypEq in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N)
    (p q : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (hincl : ∀ s : 𝟙_ X.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection p s = 0 → Scheme.Modules.pullbackSection q s = 0) :
    p ≫ 𝔓.toProj = q ≫ 𝔓.toProj := by
  classical
  have hp' : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
    rw [hp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hq' : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
    rw [hq, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hpt : ∀ y : Spec (CommRingCat.of k), y = IsLocalRing.closedPoint k := fun y => Subsingleton.elim _ _
  obtain ⟨i, hpU⟩ := exists_chart 𝔓 p _ hpt
  obtain ⟨i', hqU⟩ := exists_chart 𝔓 q _ hpt
  obtain ⟨φp, hφp⟩ := exists_fac 𝔓 p i hpU
  obtain ⟨φq, hφq⟩ := exists_fac 𝔓 q i' hqU

  set a : Fin (N + 1) → k := fun l => φp.hom (ProjSpace.ratio k N i l) with ha
  set b : Fin (N + 1) → k := fun l => φq.hom (ProjSpace.ratio k N i' l) with hb
  have hai : a i = 1 := by simp only [ha, ProjSpace.ratio_self, map_one]
  have hbi' : b i' = 1 := by simp only [hb, ProjSpace.ratio_self, map_one]

  have key : ∀ l, b l = a l * b i := by
    intro l
    set c : Fin (N + 1) → k := fun j => (if j = l then (1 : k) else 0) - a l * (if j = i then 1 else 0) with hc
    obtain ⟨s, hs⟩ := exists_unitHom_app_eq 𝓝
      (∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c j))) • 𝔓.σ j)
    have hsP : Scheme.Modules.pullbackSection p s = 0 := by
      rw [pullbackSection_eq_zero_iff_sum_eq_zero 𝔓 p hp' i hpU φp hφp c s hs]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, hc]
      rw [sum_test_mul]
      change a l - a l * a i = 0
      rw [hai, mul_one, sub_self]
    have hsQ := (pullbackSection_eq_zero_iff_sum_eq_zero 𝔓 q hq' i' hqU φq hφq c s hs).mp (hincl s hsP)
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hc] at hsQ
    rw [sum_test_mul] at hsQ
    change b l - a l * b i = 0 at hsQ
    exact sub_eq_zero.mp hsQ
  have hunit : a i' * b i = 1 := by rw [← key i', hbi']

  have H := AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq k N k a i i'
    (by rw [hai]; exact isUnit_one) ⟨⟨a i', b i, hunit, (mul_comm _ _).trans hunit⟩, rfl⟩
    (algHomOfFac 𝔓 p hp' i φp hφp) (algHomOfFac 𝔓 q hq' i' φq hφq)
    (fun l => by rw [algHomOfFac_apply, hai, mul_one])
    (fun l => by
      rw [algHomOfFac_apply]
      change b l * a i' = a l
      rw [key l, mul_assoc, mul_comm (b i), hunit, mul_one])
  rw [ofHom_algHomOfFac, ofHom_algHomOfFac] at H
  rw [hφp, hφq]
  exact H

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp (solution)
