-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:03:40.922338+00:00
-- url     : https://prove2.me/theorems/af609978-9d3b-5167-b248-e00fd173f84e
-- title:
--   Exact And Surjective App Of Exact Of Epi
-- statement:
--   Definitions and structural lemmas for Exact And Surjective App Of Exact Of Epi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_restrict_fromSpec_iff
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_res_self
import Theorems.Thm_GlobalTheory_QCoh_restrict_fromSpec_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
namespace GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
section Sections
def appLinear (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul φ
@[simp]
theorem appLinear_apply (φ : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    appLinear φ U s = φ.app U s := rfl
theorem app_app (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (s : Γ(M, U)) :
    ψ.app U (φ.app U s) = (φ ≫ ψ).app U s := rfl
theorem app_res (φ : M ⟶ N) (h : V ≤ U) (s : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app U s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)
def sections (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} Γ(X, U) where
  obj M := ModuleCat.of Γ(X, U) Γ(M, U)
  map φ := ModuleCat.ofHom (appLinear φ U)
@[simp]
theorem sections_obj (U : X.Opens) (M : X.Modules) :
    (sections U).obj M = ModuleCat.of Γ(X, U) Γ(M, U) := rfl
@[simp]
theorem sections_map (U : X.Opens) (φ : M ⟶ N) :
    (sections U).map φ = ModuleCat.ofHom (appLinear φ U) := rfl
instance (U : X.Opens) : (sections U).Additive where
instance sections_preservesLimits (U : X.Opens) : PreservesLimits (sections U) := by
  have : PreservesLimits (sections U ⋙ forget₂ (ModuleCat.{u} Γ(X, U)) Ab.{u}) :=
    haveI : PreservesLimits ((evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U)) :=
      ⟨fun {_} _ ↦ evaluation_preservesLimitsOfShape _⟩
    comp_preservesLimits (Scheme.Modules.toPresheaf X) ((evaluation _ _).obj (op U))
  exact preservesLimits_of_reflects_of_preserves _ (forget₂ (ModuleCat.{u} Γ(X, U)) Ab.{u})
instance (U : X.Opens) : PreservesFiniteLimits (sections U) :=
  PreservesLimitsOfSize.preservesFiniteLimits _
theorem injective_app_of_mono (φ : M ⟶ N) [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) :=
  (ModuleCat.mono_iff_injective ((sections U).map φ)).mp inferInstance
theorem exact_app_of_exact_of_mono {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f]
    (U : X.Opens) : Function.Exact (S.f.app U) (S.g.app U) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map (sections U))).mp
    (hS.map_of_mono_of_preservesKernel (sections U) inferInstance inferInstance)
def sectionsIsoSpec (hU : IsAffineOpen U) :
    sections U ≅ Scheme.Modules.restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor (R := Γ(X, U)) :=
  NatIso.ofComponents (fun F ↦ LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (M := Γ(F, U)) (M₂ := Γ(F.restrict hU.fromSpec, ⊤))
      { toFun := fun s ↦ (F.restrictAppIso hU.fromSpec ⊤).inv
          (F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op s)
        map_add' := fun s t ↦ by simp
        map_smul' := fun r s ↦ by
          rw [F.map_smul, RingHom.id_apply]
          exact (restrict_fromSpec_smul F hU ⊤ r _).symm }
      (by
        have key : ∀ (W : X.Opens) (h : W ≤ U), W = U →
            Function.Bijective (F.presheaf.map (homOfLE h).op) := by
          rintro W h rfl
          have : ⇑(F.presheaf.map (homOfLE h).op) = id := funext (res_self F h)
          rw [this]
          exact Function.bijective_id
        exact key _ (fromSpec_image_le hU ⊤)
          (by rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]))))
    fun φ ↦ by
      ext s
      exact (app_res φ (fromSpec_image_le hU ⊤) s).symm
end Sections
section Colimits
variable {J : Type w} [Category.{w'} J]
set_option backward.isDefEq.respectTransparency false in
theorem isQuasicoherent_of_iso (e : M ≅ N) [M.IsQuasicoherent] : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e ‹_›
def tildeDiagramIso {R : CommRingCat.{u}} (D : J ⥤ (Spec R).Modules)
    [∀ j, (D.obj j).IsQuasicoherent] :
    (D ⋙ moduleSpecΓFunctor (R := R)) ⋙ tilde.functor R ≅ D :=
  haveI (j : J) : IsIso (tilde.adjunction.counit.app (D.obj j)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (D.obj j)
  NatIso.ofComponents (fun j ↦ asIso (tilde.adjunction.counit.app (D.obj j)))
    fun f ↦ tilde.adjunction.counit.naturality (D.map f)
theorem isQuasicoherent_of_isColimit_Spec {R : CommRingCat.{u}}
    [HasColimitsOfShape J (ModuleCat.{u} R)] {D : J ⥤ (Spec R).Modules}
    [∀ j, (D.obj j).IsQuasicoherent] {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent :=
  isQuasicoherent_of_iso (M := (tilde.functor R).obj (colimit (D ⋙ moduleSpecΓFunctor (R := R))))
    (IsColimit.coconePointsIsoOfNatIso
      (isColimitOfPreserves (tilde.functor R) (colimit.isColimit _)) hc (tildeDiagramIso D))
theorem preservesColimit_moduleSpecΓFunctor {R : CommRingCat.{u}}
    [HasColimitsOfShape J (ModuleCat.{u} R)] (D : J ⥤ (Spec R).Modules)
    [∀ j, (D.obj j).IsQuasicoherent] :
    PreservesColimit D (moduleSpecΓFunctor (R := R)) := by
  have : PreservesColimit (D ⋙ moduleSpecΓFunctor (R := R))
      (tilde.functor R ⋙ moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_natIso _ tilde.toTildeΓNatIso
  have : PreservesColimit ((D ⋙ moduleSpecΓFunctor (R := R)) ⋙ tilde.functor R)
      (moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (tilde.functor R) (colimit.isColimit _))
      (isColimitOfPreserves (tilde.functor R ⋙ moduleSpecΓFunctor (R := R)) (colimit.isColimit _))
  exact preservesColimit_of_iso_diagram _ (tildeDiagramIso D)
variable [Small.{u} J]
theorem isQuasicoherent_of_isColimit {D : J ⥤ X.Modules}
    [∀ j, (D.obj j).IsQuasicoherent] {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine _).mpr fun U hU ↦ ?_
  rw [← isQuasicoherent_restrict_fromSpec_iff _ hU]
  have (j : J) : ((D ⋙ Scheme.Modules.restrictFunctor hU.fromSpec).obj j).IsQuasicoherent :=
    inferInstanceAs ((D.obj j).restrict hU.fromSpec).IsQuasicoherent
  exact isQuasicoherent_of_isColimit_Spec
    (isColimitOfPreserves (Scheme.Modules.restrictFunctor hU.fromSpec) hc)
theorem preservesColimit_sections (hU : IsAffineOpen U) (D : J ⥤ X.Modules)
    [∀ j, (D.obj j).IsQuasicoherent] : PreservesColimit D (sections U) := by
  have (j : J) : ((D ⋙ Scheme.Modules.restrictFunctor hU.fromSpec).obj j).IsQuasicoherent :=
    inferInstanceAs ((D.obj j).restrict hU.fromSpec).IsQuasicoherent
  have := preservesColimit_moduleSpecΓFunctor (D ⋙ Scheme.Modules.restrictFunctor hU.fromSpec)
  have : PreservesColimit D
      (Scheme.Modules.restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor (R := Γ(X, U))) :=
    ⟨fun hc ↦ ⟨isColimitOfPreserves (moduleSpecΓFunctor (R := Γ(X, U)))
      (isColimitOfPreserves (Scheme.Modules.restrictFunctor hU.fromSpec) hc)⟩⟩
  exact preservesColimit_of_natIso _ (sectionsIsoSpec hU).symm
end Colimits
section Closure
instance isQuasicoherent_colimit {J : Type w} [Category.{w'} J] [Small.{u} J] (D : J ⥤ X.Modules)
    [HasColimit D] [∀ j, (D.obj j).IsQuasicoherent] : (colimit D).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (colimit.isColimit D)
instance isQuasicoherent_parallelPair_obj (φ ψ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (j : WalkingParallelPair) : ((parallelPair φ ψ).obj j).IsQuasicoherent := by
  cases j <;> assumption
instance isQuasicoherent_discrete_obj {ι : Type w} (F : ι → X.Modules)
    [h : ∀ i, (F i).IsQuasicoherent] (j : Discrete ι) :
    ((Discrete.functor F).obj j).IsQuasicoherent := h j.as
instance isQuasicoherent_pair_obj [M.IsQuasicoherent] [N.IsQuasicoherent]
    (j : Discrete WalkingPair) : ((pair M N).obj j).IsQuasicoherent := by
  obtain ⟨_ | _⟩ := j <;> assumption
theorem isQuasicoherent_of_isZero (h : IsZero M) : M.IsQuasicoherent :=
  haveI (j : Discrete PEmpty.{1}) : ((Functor.empty.{0} X.Modules).obj j).IsQuasicoherent :=
    j.as.elim
  isQuasicoherent_of_isColimit (D := Functor.empty.{0} X.Modules) h.isInitial
open ZeroObject in
instance isQuasicoherent_zero : (0 : X.Modules).IsQuasicoherent :=
  isQuasicoherent_of_isZero (isZero_zero _)
instance isQuasicoherent_cokernel (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel φ).IsQuasicoherent :=
  isQuasicoherent_colimit _
instance isQuasicoherent_sigma {ι : Type w} [Small.{u} ι] (F : ι → X.Modules) [HasCoproduct F]
    [∀ i, (F i).IsQuasicoherent] : (∐ F).IsQuasicoherent :=
  isQuasicoherent_colimit _
instance isQuasicoherent_biproduct {ι : Type w} [Small.{u} ι] (F : ι → X.Modules)
    [HasBiproduct F] [∀ i, (F i).IsQuasicoherent] : (⨁ F).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (biproduct.isColimit F)
instance isQuasicoherent_biprod [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (BinaryBiproduct.isColimit M N)
instance isQuasicoherent_coprod [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨿ N).IsQuasicoherent :=
  isQuasicoherent_colimit _
instance isQuasicoherent_prod [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨯ N).IsQuasicoherent :=
  isQuasicoherent_of_iso (biprod.isoProd M N)
instance isQuasicoherent_pi {ι : Type w} [Finite ι] (F : ι → X.Modules) [HasProduct F]
    [∀ i, (F i).IsQuasicoherent] : (∏ᶜ F).IsQuasicoherent :=
  haveI : HasBiproduct F := HasBiproduct.of_hasProduct F
  isQuasicoherent_of_iso (biproduct.isoProduct F)
theorem isQuasicoherent_of_exact_app {K : X.Modules} (ι : K ⟶ M) (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hι : ∀ U, IsAffineOpen U → Function.Injective (ι.app U))
    (hex : ∀ U, IsAffineOpen U → Function.Exact (ι.app U) (φ.app U)) :
    K.IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine _).mpr fun U hU f ↦ ?_
  rw [isLocalizedModule_resBasicOpen_iff]
  refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_res M hU f (X.basicOpen_le f) rfl (ι.app _ s)
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero N hU f (X.basicOpen_le f) rfl (φ.app U m) (by
      rw [← app_res, ← hm, Scheme.Modules.Hom.app_smul,
        (hex _ (hU.basicOpen f)).apply_apply_eq_zero, smul_zero])
    rw [← Scheme.Modules.Hom.app_smul] at hk
    obtain ⟨t, ht⟩ := (hex U hU _).mp hk
    refine ⟨k + n, t, hι _ (hU.basicOpen f) ?_⟩
    rw [app_res, ht, M.map_smul, ← hm, Scheme.Modules.Hom.app_smul, map_pow, pow_add, mul_smul]
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero M hU f (X.basicOpen_le f) rfl (ι.app U t) (by
      rw [← app_res, ht, map_zero])
    exact ⟨n, hι U hU (by rw [Scheme.Modules.Hom.app_smul, hn, map_zero])⟩
theorem injective_kernel_ι_app (φ : M ⟶ N) (U : X.Opens) :
    Function.Injective ((kernel.ι φ).app U) :=
  injective_app_of_mono _ U
theorem exact_kernel_ι_app (φ : M ⟶ N) (U : X.Opens) :
    Function.Exact ((kernel.ι φ).app U) (φ.app U) :=
  exact_app_of_exact_of_mono (S := ShortComplex.mk _ _ (kernel.condition φ))
    (ShortComplex.exact_kernel φ) U
instance isQuasicoherent_kernel (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel φ).IsQuasicoherent :=
  isQuasicoherent_of_exact_app (kernel.ι φ) φ (fun U _ ↦ injective_kernel_ι_app φ U)
    fun U _ ↦ exact_kernel_ι_app φ U
instance isQuasicoherent_abelianImage (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (Abelian.image φ).IsQuasicoherent :=
  isQuasicoherent_kernel _
instance isQuasicoherent_abelianCoimage (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (Abelian.coimage φ).IsQuasicoherent :=
  isQuasicoherent_cokernel _
instance isQuasicoherent_image (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (image φ).IsQuasicoherent :=
  isQuasicoherent_of_iso (Abelian.imageIsoImage φ)
instance isQuasicoherent_cycles (S : ShortComplex X.Modules) [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] : S.cycles.IsQuasicoherent :=
  isQuasicoherent_of_iso S.cyclesIsoKernel.symm
instance isQuasicoherent_homology (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.homology.IsQuasicoherent :=
  isQuasicoherent_of_isColimit S.homologyIsCokernel
end Closure
section Affine
theorem exact_and_surjective_app_of_exact_of_epi {S : ShortComplex X.Modules} (hS : S.Exact)
    [Epi S.g] [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] (hU : IsAffineOpen U) :
    Function.Exact (S.f.app U) (S.g.app U) ∧ Function.Surjective (S.g.app U) := by
  have := preservesColimit_sections hU (parallelPair S.f 0)
  have h := ((S.map (sections U)).exact_and_epi_g_iff_g_is_cokernel).mpr
    ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel (sections U)⟩
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map (sections U))).mp h.1,
    (ModuleCat.epi_iff_surjective _).mp h.2⟩
theorem exact_cokernel_π_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Function.Exact (φ.app U) ((cokernel.π φ).app U) :=
  (exact_and_surjective_app_of_exact_of_epi (S := ShortComplex.mk _ _ (cokernel.condition φ))
    (ShortComplex.exact_cokernel φ) hU).1
theorem surjective_cokernel_π_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Function.Surjective ((cokernel.π φ).app U) :=
  (exact_and_surjective_app_of_exact_of_epi (S := ShortComplex.mk _ _ (cokernel.condition φ))
    (ShortComplex.exact_cokernel φ) hU).2
theorem subsingleton_sections_of_isZero (h : IsZero M) (U : X.Opens) : Subsingleton Γ(M, U) :=
  ModuleCat.isZero_iff_subsingleton.mp ((sections U).map_isZero h)
theorem surjective_app_of_epi (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi φ]
    (hU : IsAffineOpen U) : Function.Surjective (φ.app U) := fun t ↦
  haveI := subsingleton_sections_of_isZero (isZero_cokernel_of_epi φ) U
  (exact_cokernel_π_app φ hU t).mp (Subsingleton.elim _ _)
theorem injective_image_ι_app (φ : M ⟶ N) (U : X.Opens) :
    Function.Injective ((image.ι φ).app U) :=
  injective_app_of_mono _ U
theorem surjective_factorThruImage_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Function.Surjective ((factorThruImage φ).app U) :=
  surjective_app_of_epi _ hU
theorem range_image_ι_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    LinearMap.range (appLinear (image.ι φ) U) = LinearMap.range (appLinear φ U) := by
  ext t
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s, rfl⟩ := surjective_factorThruImage_app φ hU s
    exact ⟨s, by rw [appLinear_apply, appLinear_apply, app_app, image.fac]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(factorThruImage φ).app U s, by rw [appLinear_apply, appLinear_apply, app_app, image.fac]⟩
end Affine
section Cover
variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff
variable [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]
end Cover
section Subcategory
variable (X) in

abbrev qcoh : ObjectProperty X.Modules := fun M ↦ M.IsQuasicoherent
instance : (qcoh X).IsClosedUnderIsomorphisms where
  of_iso e _ := isQuasicoherent_of_iso e
instance : (qcoh X).ContainsZero where
  exists_zero := ⟨_, isZero_zero _, isQuasicoherent_zero⟩
instance : (qcoh X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, h₁, h₂⟩
    exact isQuasicoherent_of_iso (M := kernel φ)
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk)
instance : (qcoh X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, h₁, h₂⟩
    exact isQuasicoherent_of_isColimit hk
instance (J : Type w) [Category.{w'} J] [Small.{u} J] :
    (qcoh X).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro _ ⟨p⟩
    have := p.prop_diag_obj
    exact isQuasicoherent_of_isColimit p.isColimit
instance : (qcoh X).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := .mk' (by
    rintro _ ⟨F, hF⟩
    have (j : J) : (F.obj ⟨j⟩).IsQuasicoherent := hF ⟨j⟩
    exact isQuasicoherent_of_iso (M := ∏ᶜ fun j ↦ F.obj ⟨j⟩)
      (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))).symm)
instance : Abelian (qcoh X).FullSubcategory := inferInstance
instance : PreservesFiniteLimits (qcoh X).ι :=
  haveI := (qcoh X).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels _
instance (J : Type) [SmallCategory J] [FinCategory J] : (qcoh X).IsClosedUnderLimitsOfShape J :=
  (qcoh X).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι J
theorem isQuasicoherent_of_isLimit {J : Type} [SmallCategory J] [FinCategory J]
    {D : J ⥤ X.Modules} [h : ∀ j, (D.obj j).IsQuasicoherent] {c : Cone D} (hc : IsLimit c) :
    c.pt.IsQuasicoherent :=
  (qcoh X).prop_of_isLimit hc h
instance isQuasicoherent_limit {J : Type} [SmallCategory J] [FinCategory J]
    (D : J ⥤ X.Modules) [∀ j, (D.obj j).IsQuasicoherent] : (limit D).IsQuasicoherent :=
  isQuasicoherent_of_isLimit (limit.isLimit D)
instance isQuasicoherent_fiberProduct (φ : M ⟶ P) (ψ : N ⟶ P) [M.IsQuasicoherent]
    [N.IsQuasicoherent] [P.IsQuasicoherent] : (pullback φ ψ).IsQuasicoherent :=
  haveI (j : WalkingCospan) : ((cospan φ ψ).obj j).IsQuasicoherent := by
    obtain _ | _ | _ := j <;> assumption
  isQuasicoherent_limit _
instance isQuasicoherent_amalgamatedSum (φ : P ⟶ M) (ψ : P ⟶ N) [M.IsQuasicoherent]
    [N.IsQuasicoherent] [P.IsQuasicoherent] : (pushout φ ψ).IsQuasicoherent :=
  haveI (j : WalkingSpan) : ((span φ ψ).obj j).IsQuasicoherent := by
    obtain _ | _ | _ := j <;> assumption
  isQuasicoherent_colimit _
end Subcategory
section Equivs
theorem range_kernel_ι_app (φ : M ⟶ N) (U : X.Opens) :
    LinearMap.range (appLinear (kernel.ι φ) U) = LinearMap.ker (appLinear φ U) :=
  Submodule.ext fun s ↦ (exact_kernel_ι_app φ U s).symm
theorem ker_cokernel_π_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    LinearMap.ker (appLinear (cokernel.π φ) U) = LinearMap.range (appLinear φ U) :=
  Submodule.ext fun s ↦ exact_cokernel_π_app φ hU s
def kernelSectionsEquiv (φ : M ⟶ N) (U : X.Opens) :
    Γ(kernel φ, U) ≃ₗ[Γ(X, U)] LinearMap.ker (appLinear φ U) :=
  (LinearEquiv.ofInjective (appLinear (kernel.ι φ) U) (injective_kernel_ι_app φ U)).trans
    (LinearEquiv.ofEq _ _ (range_kernel_ι_app φ U))
@[simp]
theorem kernelSectionsEquiv_apply_coe (φ : M ⟶ N) (U : X.Opens) (s : Γ(kernel φ, U)) :
    (kernelSectionsEquiv φ U s : Γ(M, U)) = (kernel.ι φ).app U s := rfl
def cokernelSectionsEquiv (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    (Γ(N, U) ⧸ LinearMap.range (appLinear φ U)) ≃ₗ[Γ(X, U)] Γ(cokernel φ, U) :=
  (Submodule.quotEquivOfEq _ _ (ker_cokernel_π_app φ hU).symm).trans
    (LinearMap.quotKerEquivOfSurjective (appLinear (cokernel.π φ) U)
      (surjective_cokernel_π_app φ hU))
@[simp]
theorem cokernelSectionsEquiv_mk (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) (s : Γ(N, U)) :
    cokernelSectionsEquiv φ hU (Submodule.Quotient.mk s) = (cokernel.π φ).app U s := rfl
def imageSectionsEquiv (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Γ(image φ, U) ≃ₗ[Γ(X, U)] LinearMap.range (appLinear φ U) :=
  (LinearEquiv.ofInjective (appLinear (image.ι φ) U) (injective_image_ι_app φ U)).trans
    (LinearEquiv.ofEq _ _ (range_image_ι_app φ hU))
@[simp]
theorem imageSectionsEquiv_apply_coe (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) (s : Γ(image φ, U)) :
    (imageSectionsEquiv φ hU s : Γ(N, U)) = (image.ι φ).app U s := rfl
open DirectSum in

def sigmaSectionsEquiv {ι : Type u} [DecidableEq ι] (F : ι → X.Modules)
    [∀ i, (F i).IsQuasicoherent] (hU : IsAffineOpen U) :
    (⨁ i, Γ(F i, U)) ≃ₗ[Γ(X, U)] Γ(∐ F, U) :=
  haveI := preservesColimit_sections hU (Discrete.functor F)
  ((ModuleCat.coprodIsoDirectSum fun i ↦ (sections U).obj (F i)).symm ≪≫
    (PreservesCoproduct.iso (sections U) F).symm).toLinearEquiv
@[simp]
theorem sigmaSectionsEquiv_lof {ι : Type u} [DecidableEq ι] (F : ι → X.Modules)
    [∀ i, (F i).IsQuasicoherent] (hU : IsAffineOpen U) (i : ι) (s : Γ(F i, U)) :
    sigmaSectionsEquiv F hU (DirectSum.lof Γ(X, U) ι (fun i ↦ Γ(F i, U)) i s) =
      (Sigma.ι F i).app U s := by
  have := preservesColimit_sections hU (Discrete.functor F)
  have h : ModuleCat.ofHom (DirectSum.lof Γ(X, U) ι (fun i ↦ (sections U).obj (F i)) i) ≫
      (ModuleCat.coprodIsoDirectSum fun i ↦ (sections U).obj (F i)).inv ≫
      (PreservesCoproduct.iso (sections U) F).inv = (sections U).map (Sigma.ι F i) := by
    rw [← Category.assoc, ModuleCat.lof_coprodIsoDirectSum_inv, PreservesCoproduct.inv_hom,
      ι_comp_sigmaComparison]
  exact congr($h s)
def piSectionsEquiv {ι : Type u} (F : ι → X.Modules) (U : X.Opens) :
    Γ(∏ᶜ F, U) ≃ₗ[Γ(X, U)] (∀ i, Γ(F i, U)) :=
  (PreservesProduct.iso (sections U) F ≪≫
    ModuleCat.piIsoPi fun i ↦ (sections U).obj (F i)).toLinearEquiv
@[simp]
theorem piSectionsEquiv_apply {ι : Type u} (F : ι → X.Modules) (U : X.Opens) (s : Γ(∏ᶜ F, U))
    (i : ι) : piSectionsEquiv F U s i = (Pi.π F i).app U s := by
  have h : (PreservesProduct.iso (sections U) F).hom ≫
      (ModuleCat.piIsoPi fun i ↦ (sections U).obj (F i)).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) = (sections U).map (Pi.π F i) := by
    rw [ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom, piComparison_comp_π]
  exact congr($h s)
theorem app_sum {ι : Type w} (t : Finset ι) (φ : ι → (M ⟶ N)) (U : X.Opens) (s : Γ(M, U)) :
    (∑ i ∈ t, φ i).app U s = ∑ i ∈ t, (φ i).app U s := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
def biproductSectionsEquiv {ι : Type} [Fintype ι] (F : ι → X.Modules) [HasBiproduct F]
    (U : X.Opens) : Γ(⨁ F, U) ≃ₗ[Γ(X, U)] (∀ i, Γ(F i, U)) where
  toLinearMap := LinearMap.pi fun i ↦ appLinear (biproduct.π F i) U
  invFun s := ∑ i, (biproduct.ι F i).app U (s i)
  left_inv s := by
    simp only [LinearMap.toFun_eq_coe, LinearMap.pi_apply, appLinear_apply, app_app]
    rw [← app_sum, biproduct.total]
    rfl
  right_inv s := by
    classical
    ext i
    simp only [LinearMap.toFun_eq_coe, LinearMap.pi_apply, appLinear_apply, map_sum, app_app]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [biproduct.ι_π_ne F hj]; rfl) (by simp),
      biproduct.ι_π_self]
    rfl
@[simp]
theorem biproductSectionsEquiv_apply {ι : Type} [Fintype ι] (F : ι → X.Modules) [HasBiproduct F]
    (U : X.Opens) (s : Γ(⨁ F, U)) (i : ι) :
    biproductSectionsEquiv F U s i = (biproduct.π F i).app U s := rfl
def biprodSectionsEquiv (M N : X.Modules) (U : X.Opens) :
    Γ(M ⊞ N, U) ≃ₗ[Γ(X, U)] Γ(M, U) × Γ(N, U) where
  toLinearMap := LinearMap.prod (appLinear biprod.fst U) (appLinear biprod.snd U)
  invFun s := (biprod.inl : M ⟶ M ⊞ N).app U s.1 + (biprod.inr : N ⟶ M ⊞ N).app U s.2
  left_inv s := by
    change (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : M ⊞ N ⟶ M ⊞ N).app U s = s
    rw [biprod.total]
    rfl
  right_inv s := by
    ext
    · change (biprod.fst : M ⊞ N ⟶ M).app U _ = _
      rw [map_add, app_app, app_app, biprod.inl_fst, biprod.inr_fst]
      exact add_zero _
    · change (biprod.snd : M ⊞ N ⟶ N).app U _ = _
      rw [map_add, app_app, app_app, biprod.inl_snd, biprod.inr_snd]
      exact zero_add _
end Equivs
section AllAffine
variable [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]
end AllAffine
end GlobalTheory.QCoh


