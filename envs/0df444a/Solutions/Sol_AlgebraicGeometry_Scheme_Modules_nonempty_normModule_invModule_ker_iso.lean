-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_normModule_invModule_ker_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4efd10a5-bc04-5428-8255-0b6ec57307f3

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Theorems.Thm_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.Modules.Hom.app_smul Surjective SmoothOfRelativeDimension Scheme.Modules.pushforward IsClosedImmersion.of_comp Scheme.Hom.id_app Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom.comp_app Scheme.Modules.Hom IsFinite Spec Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrict_map Flat Scheme.IdealSheafData.ext_of_iSup_eq_top IsClosedImmersion IsSeparated Scheme.Hom.comp_app IsAffineOpen Scheme.Modules Scheme.Hom.ker_apply Scheme.Hom.appLE_map SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension LocallyOfFinitePresentation IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.Modules.normModule Scheme.Modules.normModuleUnitEval Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.IsLocallyFreeOfRank Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Modules.IsInvertible.normModule Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app Modules.Hom.app_smul Modules.pushforward Hom.id_app Hom Hom.appLE_comp_appLE Γ Modules.Hom.comp_app empty Modules.Hom topIso Modules.Hom.id_app Modules.restrict_map IdealSheafData.ext_of_iSup_eq_top affineOpens Hom.comp_app basicOpen Modules Hom.ker_apply Opens Hom.appLE_map Modules.map_smul basicOpen_le restrict Hom.appLE IdealSheafData ΓSpecIso evaluation Modules.normModule Modules.normModuleUnitEval Modules.IsInvertible Modules.isInvertible_unit Modules.IsLocallyFreeOfRank Hom.isInvertible_ker_of_comp_eq_id Modules.IsInvertible.normModule Modules.isInvertible_det_of_isLocallyFreeOfRank Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map restrict map_smul normModule normModuleFunctor normModuleUnitEval toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map ofUnitSection_smul restrictSection coeff zeroSchemeIdeal restrictIsoOfLE IsInvertible isInvertible_unit IsLocallyFreeOfRank IsFrameOn isFrameOn_unitSection image_preimage_eq_of_le restrict_smul_eq IsInvertible.normModule isInvertible_det_of_isLocallyFreeOfRank isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite IsInvertible.exists_iso_invModule_zeroSchemeIdeal IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq exists_isFrameOn_normModule_and_app_eq_norm_smul"
namespace NormPoint
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {K : Type u} [Field K] {X X' : Scheme.{u}}

noncomputable def detSection (π : X' ⟶ X) (d : ℕ) [IsIso (normModuleUnitEval π d)]
    {L : X'.Modules} (s : 𝟙_ X'.Modules ⟶ L) : 𝟙_ X.Modules ⟶ normModule π d L :=
  inv (normModuleUnitEval π d) ≫ (normModuleFunctor π d).map s

set_option maxHeartbeats 3200000 in

theorem ideal_zeroSchemeIdeal_detSection_eq_span_norm
    (π : X' ⟶ X) [IsAffineHom π] (d : ℕ) [IsIso (normModuleUnitEval π d)]
    {P : X'.Modules} (hN : IsInvertible (normModule π d P)) (ι' : 𝟙_ X'.Modules ⟶ P)
    (U : X.affineOpens)
    (e : Fin d → Γ((pushforward π).obj (𝟙_ X'.Modules), U.1))
    (he : ∀ (W : X.Opens) (hW : W ≤ U.1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i))
    (s : Γ(P, π ⁻¹ᵁ U.1)) (hs : IsFrameOn s (π ⁻¹ᵁ U.1))
    (g : Γ(X', π ⁻¹ᵁ U.1)) (hg : ι'.app (π ⁻¹ᵁ U.1) (toUnitSection _ 1) = g • s) :
    letI : Algebra Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
    (zeroSchemeIdeal (detSection π d ι')).ideal U = Ideal.span {Algebra.norm Γ(X, U.1) g} := by
  letI : Algebra Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
  obtain ⟨Ω, hΩ, hσ⟩ := exists_isFrameOn_normModule_and_app_eq_norm_smul π d ι' U.1 e he s hs g hg
  have := hN.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul Ω hΩ (detSection π d ι') (Algebra.norm Γ(X, U.1) g)
    hσ U le_rfl
  rw [this]
  congr 2
  change (X.presheaf.map (homOfLE (le_refl U.1)).op) _ = _
  rw [show (homOfLE (le_refl U.1)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem presheaf_map_congr {M : X.Modules} {A B : X.Opens} (f g : op A ⟶ op B) (m : Γ(M, A)) :
    M.presheaf.map f m = M.presheaf.map g m := by
  have hfg : f = g := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  subst hfg
  rfl

set_option maxHeartbeats 6400000 in

theorem isFrameOn_of_isFrameOn_restrict {M : X.Modules} (V : X.Opens)
    (s₀ : Γ(M.restrict V.ι, ⊤)) (h : IsFrameOn (M := M.restrict V.ι) s₀ ⊤) :
    IsFrameOn (M := M) (M.presheaf.map (eqToHom V.ι_image_top.symm).op (show Γ(M, V.ι ''ᵁ ⊤) from s₀)) V := by
  intro W hWV _
  obtain ⟨W₀, rfl⟩ : ∃ W₀, V.ι ''ᵁ W₀ = W := ⟨V.ι ⁻¹ᵁ W, image_preimage_eq_of_le hWV⟩
  have hb₀ := h (W := W₀) le_top le_top
  have heq : (fun a : Γ((V : Scheme.{u}), W₀) =>
      a • (M.restrict V.ι).presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op s₀) =
      (fun a : Γ(X, V.ι ''ᵁ W₀) => a • (show Γ(M, V.ι ''ᵁ W₀) from
        (M.restrict V.ι).presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op s₀)) := by
    funext a; exact restrict_smul_eq _ a _
  rw [heq, Scheme.Modules.restrict_map] at hb₀
  have helt : M.presheaf.map (homOfLE hWV).op
      (M.presheaf.map (eqToHom V.ι_image_top.symm).op (show Γ(M, V.ι ''ᵁ ⊤) from s₀)) =
      M.presheaf.map (V.ι.opensFunctor.map (homOfLE (le_top : W₀ ≤ ⊤))).op (show Γ(M, V.ι ''ᵁ ⊤) from s₀) := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    exact presheaf_map_congr _ _ _
  rw [helt]
  exact hb₀

set_option maxHeartbeats 6400000 in

theorem exists_isFrameOn_and_app_eq_coeff_smul {P : X.Modules} (ι' : 𝟙_ X.Modules ⟶ P) (V : X.Opens)
    (τ : P.restrict V.ι ≅ 𝟙_ (V : Scheme.{u}).Modules) :
    ∃ s : Γ(P, V), IsFrameOn s V ∧ ι'.app V (toUnitSection V 1) = (coeff ι' V τ.hom) • s := by

  let s₀ : Γ(P.restrict V.ι, ⊤) := τ.inv.app ⊤ (toUnitSection ⊤ 1)
  have hs₀ : IsFrameOn (M := P.restrict V.ι) s₀ ⊤ :=
    (isFrameOn_unitSection (X := (V : Scheme.{u})) (U := ⊤) ⊤).map_iso τ.symm
  refine ⟨P.presheaf.map (eqToHom V.ι_image_top.symm).op (show Γ(P, V.ι ''ᵁ ⊤) from s₀),
    isFrameOn_of_isFrameOn_restrict V s₀ hs₀, ?_⟩

  set r₀ : Γ((V : Scheme.{u}), ⊤) := ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection ι' V)) with hr₀
  have hcoeff : coeff ι' V τ.hom = V.topIso.hom r₀ := rfl

  have e1 : τ.hom.app ⊤ (restrictSection ι' V) = r₀ • toUnitSection ⊤ 1 := by
    apply ofUnitSection_injective
    rw [ofUnitSection_smul, ofUnitSection_toUnitSection, mul_one]
  have e2 : restrictSection ι' V = r₀ • s₀ := by
    have := congrArg (τ.inv.app ⊤) e1
    rw [Scheme.Modules.Hom.app_smul] at this
    refine Eq.trans ?_ this
    change _ = (τ.hom.app ⊤ ≫ τ.inv.app ⊤) (restrictSection ι' V)
    rw [← Scheme.Modules.Hom.comp_app, τ.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl

  have e3 : ι'.app V (toUnitSection V 1) =
      P.presheaf.map (eqToHom V.ι_image_top.symm).op (restrictSection ι' V) := by
    have nat := (ι'.mapPresheaf).naturality (eqToHom V.ι_image_top.symm).op
    have := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(𝟙_ X.Modules, V.ι ''ᵁ ⊤) → Γ(P, V))) nat)
      (toUnitSection (V.ι ''ᵁ ⊤) 1)
    simp only [mapPresheaf_app] at this
    refine Eq.trans ?_ this
    change ι'.app V (toUnitSection V 1) = ι'.app V ((𝟙_ X.Modules).presheaf.map _ (toUnitSection _ 1))
    congr 1
    apply ofUnitSection_injective
    rw [ofUnitSection_map, ofUnitSection_toUnitSection, ofUnitSection_toUnitSection, map_one]
  rw [e3, e2, restrict_smul_eq (M := P) ⊤ r₀ s₀, Scheme.Modules.map_smul, hcoeff]
  congr 1

theorem opens_eq_top_of_mem {W : (Spec (CommRingCat.of K)).Opens} {p : Spec (CommRingCat.of K)} (hp : p ∈ W) :
    W = ⊤ := by
  ext q
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rwa [Subsingleton.elim q p]

theorem opens_eq_bot_of_not_mem {W : (Spec (CommRingCat.of K)).Opens} {p : Spec (CommRingCat.of K)}
    (hp : p ∉ W) : W = ⊥ := by
  ext q
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  rwa [Subsingleton.elim q p]

set_option maxHeartbeats 6400000 in

theorem zeroSchemeIdeal_detSection_invModuleSection
    (t : X ⟶ Spec (CommRingCat.of K)) (t' : X' ⟶ Spec (CommRingCat.of K))
    [IsSeparated t] [IsSeparated t'] [SmoothOfRelativeDimension 1 t] [SmoothOfRelativeDimension 1 t']
    (π : X' ⟶ X) (hπ : π ≫ t = t') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : X, π.finrank y = d) [IsIso (normModuleUnitEval π d)]
    (x' : {q : Spec (CommRingCat.of K) ⟶ X' // q ≫ t' = 𝟙 _}) :
    zeroSchemeIdeal (detSection π d (x'.1.ker).invModuleSection) = (x'.1 ≫ π).ker := by
  classical

  set x : Spec (CommRingCat.of K) ⟶ X := x'.1 ≫ π with hxdef
  have hxt : x ≫ t = 𝟙 _ := by rw [hxdef, Category.assoc, hπ, x'.2]
  haveI : IsClosedImmersion (x'.1 ≫ t') := by rw [x'.2]; infer_instance
  haveI : IsClosedImmersion x'.1 := IsClosedImmersion.of_comp x'.1 t'
  haveI : IsClosedImmersion (x ≫ t) := by rw [hxt]; infer_instance
  haveI : IsClosedImmersion x := IsClosedImmersion.of_comp x t
  have hI' : (x'.1.ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := t') x'.1 x'.2
  set P : X'.Modules := (x'.1.ker).invModule with hPdef
  have hP : IsInvertible P := hI'.isInvertible_invModule
  have hN : IsInvertible (normModule π d P) := IsInvertible.normModule π d hd hP
  set ι' : 𝟙_ X'.Modules ⟶ P := (x'.1.ker).invModuleSection with hι'
  have hZι' : zeroSchemeIdeal ι' = x'.1.ker := hI'.zeroSchemeIdeal_invModuleSection

  have hE : IsLocallyFreeOfRank d ((pushforward π).obj (𝟙_ X'.Modules)) :=
    isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd (𝟙_ X'.Modules)
      (fun y => IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π (isInvertible_unit X') y)

  set pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K with hpt

  let Good (U : X.affineOpens) : Prop :=
    (∃ e : Fin d → Γ((pushforward π).obj (𝟙_ X'.Modules), U.1), ∀ (W : X.Opens) (hW : W ≤ U.1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i)) ∧
    (Nonempty (P.restrict (π ⁻¹ᵁ U.1).ι ≅ 𝟙_ ((π ⁻¹ᵁ U.1 : X'.Opens) : Scheme.{u}).Modules)) ∧
    RingHom.IsStandardSmoothOfRelativeDimension 1 (t.appLE ⊤ U.1 le_top).hom

  have hgood : ∀ y : X, ∃ U : X.affineOpens, y ∈ U.1 ∧ Good U := by
    intro y

    obtain ⟨V₁, hyV₁, e₁, he₁⟩ := hE.exists_basis y

    obtain ⟨V₂, hyV₂, ⟨τ₂⟩⟩ :=
      IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π hP y

    obtain ⟨W₀, hW₀, V₃, hV₃, hyV₃, hle₃, hsm₃⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := t) y
    have hW₀top : W₀ = ⊤ := opens_eq_top_of_mem (p := t.base y) (hle₃ hyV₃)
    subst hW₀top

    obtain ⟨r, hrle, hyr⟩ :=
      hV₃.exists_basicOpen_le (V := V₁ ⊓ V₂) ⟨y, ⟨hyV₁, hyV₂⟩⟩ hyV₃
    have hUaff : IsAffineOpen (X.basicOpen r) := hV₃.basicOpen r
    have hUV₃ : X.basicOpen r ≤ V₃ := X.basicOpen_le r
    have hUV₁ : X.basicOpen r ≤ V₁ := hrle.trans inf_le_left
    refine ⟨⟨X.basicOpen r, hUaff⟩, hyr,
      ⟨fun i => ((pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hUV₁).op (e₁ i), ?_⟩, ⟨?_⟩, ?_⟩
    · intro W hW
      obtain ⟨b, hb⟩ := he₁ W (hW.trans hUV₁)
      refine ⟨b, fun i => ?_⟩
      rw [hb i, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    · exact restrictIsoOfLE (by
        show π ⁻¹ᵁ X.basicOpen r ≤ π ⁻¹ᵁ V₂
        exact fun z hz => (hrle.trans inf_le_right) hz) τ₂
    ·
      have hloc : RingHom.IsStandardSmoothOfRelativeDimension 0
          (X.presheaf.map (homOfLE hUV₃).op).hom := by
        letI := (X.presheaf.map (homOfLE hUV₃).op).hom.toAlgebra
        haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := hV₃.isLocalization_basicOpen r
        exact RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
      have := RingHom.IsStandardSmoothOfRelativeDimension.comp hloc hsm₃
      rwa [← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at this
  choose Uof hyU hgoodU using hgood

  apply Scheme.IdealSheafData.ext_of_iSup_eq_top Uof
  · exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  intro y
  set U : X.affineOpens := Uof y with hUdef
  obtain ⟨⟨e, he⟩, ⟨τ⟩, hsm⟩ := hgoodU y

  letI alg : Algebra Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
  have hUaff' : IsAffineOpen (π ⁻¹ᵁ U.1) := U.2.preimage π

  have hker' : (x'.1.ker).ideal ⟨π ⁻¹ᵁ U.1, hUaff'⟩ = RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom :=
    Scheme.Hom.ker_apply x'.1 ⟨π ⁻¹ᵁ U.1, hUaff'⟩
  have hker : (x.ker).ideal U = RingHom.ker (x.app U.1).hom := Scheme.Hom.ker_apply x U
  by_cases hxU : x.base pt ∈ U.1
  ·

    obtain ⟨s, hs, hgs⟩ := exists_isFrameOn_and_app_eq_coeff_smul ι' (π ⁻¹ᵁ U.1) τ
    set g : Γ(X', π ⁻¹ᵁ U.1) := coeff ι' (π ⁻¹ᵁ U.1) τ.hom with hgdef
    have hgspan : RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom = Ideal.span {g} := by
      rw [← hker', ← hZι']
      exact ((IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hP ι').2 ⟨π ⁻¹ᵁ U.1, hUaff'⟩ τ).1

    have hloc := ideal_zeroSchemeIdeal_detSection_eq_span_norm π d hN ι' U e he s hs g hgs

    obtain ⟨b₀, -⟩ := he U.1 le_rfl
    let b₁ : Module.Basis (Fin d) Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := Module.Basis.ofRepr
      { toFun := fun v => b₀.repr v, invFun := fun c => b₀.repr.symm c,
        map_add' := fun v w => b₀.repr.map_add v w, map_smul' := fun r v => b₀.repr.map_smul r v,
        left_inv := fun v => b₀.repr.symm_apply_apply v, right_inv := fun c => b₀.repr.apply_symm_apply c }
    haveI : Module.Free Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := Module.Free.of_basis b₁
    haveI : Module.Finite Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := Module.Finite.of_basis b₁

    have hx'U : x'.1.base pt ∈ π ⁻¹ᵁ U.1 := by
      rw [hxdef] at hxU
      exact hxU
    have htop : x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1) = ⊤ := opens_eq_top_of_mem (p := pt) hx'U
    let tail : Γ(Spec (CommRingCat.of K), x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1)) ⟶ CommRingCat.of K :=
      (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
    haveI : IsIso tail := by dsimp only [tail]; infer_instance
    have hinj : Function.Injective tail.hom := (asIso tail).commRingCatIsoToRingEquiv.injective
    let χ : Γ(X', π ⁻¹ᵁ U.1) →+* K := (x'.1.app (π ⁻¹ᵁ U.1) ≫ tail).hom
    have hkerχ : RingHom.ker χ = RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom := by
      ext a
      simp only [RingHom.mem_ker]
      exact map_eq_zero_iff tail.hom hinj

    have key : ∀ k : K, χ ((π.app U.1).hom ((t.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k))) = k := by
      intro k
      change ((Scheme.ΓSpecIso _).inv ≫ (t.appLE ⊤ U.1 le_top ≫ π.app U.1 ≫ x'.1.app (π ⁻¹ᵁ U.1) ≫
        (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op) ≫ (Scheme.ΓSpecIso _).hom) k = k
      have hmid : t.appLE ⊤ U.1 le_top ≫ π.app U.1 ≫ x'.1.app (π ⁻¹ᵁ U.1) ≫
          (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op = 𝟙 _ := by
        have h1 : π.app U.1 ≫ x'.1.app (π ⁻¹ᵁ U.1) = x.app U.1 := (Scheme.Hom.comp_app x'.1 π U.1).symm
        have h2 : t.app ⊤ ≫ x.app ⊤ = (x ≫ t).app ⊤ := (Scheme.Hom.comp_app x t ⊤).symm
        have h3 : ∀ f : op (⊤ : (Spec (CommRingCat.of K)).Opens) ⟶ op ⊤,
            (Spec (CommRingCat.of K)).presheaf.map f = 𝟙 _ := fun f => by
          have hf : f = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
          rw [hf, CategoryTheory.Functor.map_id]
        have e' : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1) := le_of_eq htop.symm
        have h4 : x.app U.1 ≫ (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op =
            x.appLE U.1 ⊤ e' := by
          rw [Scheme.Hom.appLE]
          congr 2
        rw [reassoc_of% h1]
        erw [h4]
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE, Scheme.Hom.congr_app hxt ⊤,
          Scheme.Hom.id_app]
        erw [Category.id_comp]
        first
          | exact h3 _
          | (erw [← Functor.map_comp]; exact h3 _)
      rw [hmid, Category.id_comp, Iso.inv_hom_id]
      rfl
    have hχ : Function.Surjective (χ.comp (algebraMap Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1))) := fun k => ⟨_, key k⟩
    set 𝔪 : Ideal Γ(X, U.1) := RingHom.ker (χ.comp (algebraMap Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1))) with h𝔪def
    haveI h𝔪max : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ

    have h𝔪ker : 𝔪 = RingHom.ker (x.app U.1).hom := by
      ext a
      simp only [h𝔪def, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
      change tail.hom ((x'.1.app (π ⁻¹ᵁ U.1)).hom ((π.app U.1).hom a)) = 0 ↔ _
      rw [map_eq_zero_iff tail.hom hinj]
      exact Iff.rfl

    letI algK : Algebra K Γ(X, U.1) :=
      ((t.appLE ⊤ U.1 le_top).hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm : K →+* _)).toAlgebra
    haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, U.1) :=
      RingHom.IsStandardSmoothOfRelativeDimension.comp hsm
        (RingHom.IsStandardSmoothOfRelativeDimension.equiv
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm)
    obtain ⟨hdom, hdvr⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime (k := K) 𝔪

    rw [hloc, hker, ← h𝔪ker]
    exact Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing χ hχ g (hkerχ.trans hgspan) 𝔪 rfl
      (Localization.AtPrime 𝔪)
  ·
    obtain ⟨s, hs, hgs⟩ := exists_isFrameOn_and_app_eq_coeff_smul ι' (π ⁻¹ᵁ U.1) τ
    set g : Γ(X', π ⁻¹ᵁ U.1) := coeff ι' (π ⁻¹ᵁ U.1) τ.hom with hgdef
    have hgspan : RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom = Ideal.span {g} := by
      rw [← hker', ← hZι']
      exact ((IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hP ι').2 ⟨π ⁻¹ᵁ U.1, hUaff'⟩ τ).1
    have hloc := ideal_zeroSchemeIdeal_detSection_eq_span_norm π d hN ι' U e he s hs g hgs

    have hx'U : x'.1.base pt ∉ π ⁻¹ᵁ U.1 := fun h => hxU (by rw [hxdef]; exact h)
    have hbot : x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1) = ⊥ := opens_eq_bot_of_not_mem (p := pt) hx'U
    haveI : Subsingleton Γ(Spec (CommRingCat.of K), x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1)) := by
      rw [hbot]; exact CommRingCat.subsingleton_of_isTerminal (Spec (CommRingCat.of K)).sheaf.isTerminalOfEmpty
    have hgunit : IsUnit g := by
      rw [← Ideal.span_singleton_eq_top, ← hgspan, Ideal.eq_top_iff_one, RingHom.mem_ker]
      exact Subsingleton.elim _ _
    rw [hloc, hker, Ideal.span_singleton_eq_top.mpr (hgunit.map _)]

    have hbot' : x ⁻¹ᵁ U.1 = ⊥ := opens_eq_bot_of_not_mem (p := pt) hxU
    haveI : Subsingleton Γ(Spec (CommRingCat.of K), x ⁻¹ᵁ U.1) := by
      rw [hbot']; exact CommRingCat.subsingleton_of_isTerminal (Spec (CommRingCat.of K)).sheaf.isTerminalOfEmpty
    symm
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Modules.NormPoint

open AlgebraicGeometry.Scheme.Modules.NormPoint in
set_option maxHeartbeats 3200000 in
theorem solution
    {K : Type u} [Field K] {X X' : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) (t' : X' ⟶ Spec (CommRingCat.of K))
    [IsSeparated t] [IsSeparated t'] [SmoothOfRelativeDimension 1 t] [SmoothOfRelativeDimension 1 t']
    (π : X' ⟶ X) (hπ : π ≫ t = t') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : X, π.finrank y = d)
    (x' : {q : Spec (CommRingCat.of K) ⟶ X' // q ≫ t' = 𝟙 _}) :
    Nonempty (Scheme.Modules.normModule π d (x'.1.ker).invModule ≅ ((x'.1 ≫ π).ker).invModule) := by

  have hI' : (x'.1.ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := t') x'.1 x'.2
  have hx : (x'.1 ≫ π) ≫ t = 𝟙 _ := by rw [Category.assoc, hπ, x'.2]
  have hI : ((x'.1 ≫ π).ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := t) (x'.1 ≫ π) hx

  have hN : Scheme.Modules.IsInvertible (Scheme.Modules.normModule π d (x'.1.ker).invModule) :=
    Scheme.Modules.IsInvertible.normModule π d hd hI'.isInvertible_invModule

  haveI : IsIso (Scheme.Modules.normModuleUnitEval π d) := by
    have hE : Scheme.Modules.IsLocallyFreeOfRank d
        ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)) :=
      Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd (𝟙_ X'.Modules)
        (fun y => Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π
          (Scheme.Modules.isInvertible_unit X') y)
    exact (Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank hE).isIso_ev_app_tensorUnit

  obtain ⟨e, -⟩ := hN.exists_iso_invModule_zeroSchemeIdeal (detSection π d (x'.1.ker).invModuleSection)
    (by rw [zeroSchemeIdeal_detSection_invModuleSection t t' π hπ d hd x']; exact hI)
  rw [zeroSchemeIdeal_detSection_invModuleSection t t' π hπ d hd x'] at e
  exact ⟨e⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso (solution)
