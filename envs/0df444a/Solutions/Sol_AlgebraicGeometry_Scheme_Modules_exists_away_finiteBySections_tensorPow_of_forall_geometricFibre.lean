-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_away_finiteBySections_tensorPow_of_forall_geometricFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4ab0dddc-38d5-54be-986e-65a2e9a6c61d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_finiteBySections_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_away_finiteBySections_tensorPow_of_forall_geometricFibre
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

section W2LOC_assembly
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory"
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable abbrev W2LOC.ι (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

theorem W2LOC.exists_iso_forall_unit_eq {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hh : g ≫ f = h) (M : X.Modules) :
    ∃ e : (Scheme.Modules.pullback h).obj M ≅ (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M),
      ∀ s : Γ(M, ⊤),
        (e.hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app ⊤) s) =
          (show Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M), ⊤) from
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app ((Scheme.Modules.pullback f).obj M)).app ⊤)
              (show Γ((Scheme.Modules.pullback f).obj M, ⊤) from
                (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) s)) := by
  subst hh
  refine ⟨((Scheme.Modules.pullbackComp g f).app M).symm, fun s => ?_⟩
  exact CategoryTheory.ConcreteCategory.congr_hom (Scheme.Modules.unit_app_comp_pullbackComp_inv g f M ⊤) s

open W2LOC in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hfin : ∀ (𝒰 : X.OrderedAffineCover) (n : ℕ), (OModulePresheaf.ofModules f (L.tensorPow n)).CechFinite 𝒰)
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K], ∃ n : ℕ,
      Scheme.Modules.FiniteBySections
          ((Scheme.Modules.pullback
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj (L.tensorPow n))
          (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      ∀ 𝒲 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).OrderedAffineCover,
        Subsingleton
          ((OModulePresheaf.ofModules (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
              ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
                (L.tensorPow n))).HSucc 𝒲 0))
    (𝔭 : PrimeSpectrum R) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∃ n : ℕ, 0 < n ∧ Scheme.Modules.FiniteBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))).obj (L.tensorPow n))
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))))) := by
  classical

  let K : Type u := AlgebraicClosure 𝔭.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap R K) = 𝔭.asIdeal := by
    rw [IsScalarTower.algebraMap_eq R 𝔭.asIdeal.ResidueField K, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap 𝔭.asIdeal.ResidueField K).injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  obtain ⟨n, ⟨N, 𝔓b, h𝔓b⟩, hH1⟩ := hfib K

  let M : X.Modules := L.tensorPow n
  have hM : Scheme.Modules.IsInvertible M := hL.tensorPow n
  let pK := Limits.pullback.fst f (ι R K)
  let fK := Limits.pullback.snd f (ι R K)

  obtain ⟨N', m, c, hσ⟩ :=
    Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc R f M hM (fun 𝒰 => hfin 𝒰 n) K hH1 𝔓b.σ

  have hgenK : ∀ z : ↑(Limits.pullback f (ι R K)),
      ∃ (j : Fin (N' + 1)) (U' : (Limits.pullback f (ι R K)).Opens), z ∈ U' ∧
        ∀ V' : (Limits.pullback f (ι R K)).Opens, V' ≤ U' →
          Function.Bijective fun g : Γ(Limits.pullback f (ι R K), V') =>
            g • (((Scheme.Modules.pullback pK).obj M).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
              ((((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M).app ⊤) (m j)) :
              Γ((Scheme.Modules.pullback pK).obj M, V')) := by
    intro z
    obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), z ∈ 𝔓b.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) := by
      have := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) (ProjSpace.irrelevant_le_span_X K N)
      have hz : 𝔓b.toProj z ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).Opens) := trivial
      rw [← this, TopologicalSpace.Opens.mem_iSup] at hz
      exact hz
    obtain ⟨j, U', hzU', hU'⟩ := Scheme.Modules.exists_frame_of_frame_sum_smul ((Scheme.Modules.pullback pK).obj M)
      (fun j => fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (c i j)))
      (fun j => show Γ((Scheme.Modules.pullback pK).obj M, ⊤) from
        (((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M).app ⊤) (m j)) z
      ⟨_, hi, fun V hV => by simpa only [hσ i] using 𝔓b.frame i V hV⟩
    exact ⟨j, U', hzU', hU'⟩

  obtain ⟨g₁, hg₁, hgen⟩ :=
    Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback f M hM m K 𝔭 hker hgenK

  let R₁ : Type u := Localization.Away g₁
  let p₁ := Limits.pullback.fst f (ι R R₁)
  let f₁ := Limits.pullback.snd f (ι R R₁)
  let M₁ : (Limits.pullback f (ι R R₁)).Modules := (Scheme.Modules.pullback p₁).obj M
  let σ₁ : Fin (N' + 1) → Γ(M₁, ⊤) := fun j =>
    show Γ(M₁, ⊤) from (((Scheme.Modules.pullbackPushforwardAdjunction p₁).unit.app M).app ⊤) (m j)
  let U₁ : Fin (N' + 1) → (Limits.pullback f (ι R R₁)).Opens := fun j =>
    sSup {W | ∀ V : (Limits.pullback f (ι R R₁)).Opens, V ≤ W →
      Function.Bijective fun g : Γ(Limits.pullback f (ι R R₁), V) =>
        g • (M₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ₁ j) : Γ(M₁, V))}
  have hframe₁ : ∀ j (V : (Limits.pullback f (ι R R₁)).Opens), V ≤ U₁ j →
      Function.Bijective fun g : Γ(Limits.pullback f (ι R R₁), V) =>
        g • (M₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ₁ j) : Γ(M₁, V)) := by
    intro j V hV
    apply Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul M₁ (σ₁ j) V
    intro x hx
    obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.1 (hV hx)
    exact ⟨W, hxW, hW⟩
  have hU₁ : iSup U₁ = ⊤ := by
    rw [eq_top_iff]
    rintro x₁ -
    have hx : f (p₁ x₁) ∈ PrimeSpectrum.basicOpen g₁ := by
      have h1 : f (p₁ x₁) = (ι R R₁) (f₁ x₁) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.pullback.condition]
      have h2 : (ι R R₁) (f₁ x₁) ∈ Set.range (PrimeSpectrum.comap (algebraMap R R₁)) :=
        ⟨f₁ x₁, (Spec.map_apply (CommRingCat.ofHom (algebraMap R R₁)) (f₁ x₁)).symm⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g₁) g₁] at h2
      rw [h1]
      exact h2
    obtain ⟨j, U, hxU, hU⟩ := hgen (p₁ x₁) hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, TopologicalSpace.Opens.mem_sSup.2 ⟨p₁ ⁻¹ᵁ U, ?_, hxU⟩⟩
    intro W hW
    exact Scheme.Modules.bijective_smul_unit_app_of_bijective_smul p₁ M (m j) hU W hW
  obtain ⟨𝔔, h𝔔σ, -⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top f₁ M₁ N' σ₁ U₁ hU₁ hframe₁

  have hg₁K : IsUnit (algebraMap R K g₁) := by
    rw [isUnit_iff_ne_zero, ne_eq, ← RingHom.mem_ker, hker]
    exact hg₁
  letI : Algebra R₁ K := (IsLocalization.Away.lift g₁ hg₁K).toAlgebra
  haveI : IsScalarTower R R₁ K :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq g₁ hg₁K r).symm
  have hιK : ι R K = ι R₁ K ≫ ι R R₁ := by
    rw [ι, ι, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let q : Limits.pullback f (ι R K) ⟶ Limits.pullback f (ι R R₁) :=
    Limits.pullback.lift pK (fK ≫ ι R₁ K) (by rw [Category.assoc, ← hιK]; exact Limits.pullback.condition)
  have hq : q ≫ p₁ = pK := Limits.pullback.lift_fst _ _ _
  have sqK : IsPullback q fK f₁ (ι R₁ K) := by
    refine IsPullback.of_right ?_ (Limits.pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (ι R R₁))
    rw [hq, ← hιK]; exact IsPullback.of_hasPullback f (ι R K)
  obtain ⟨𝔔K, h𝔔Kσ, h𝔔Kcomp, h𝔔Ksq⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sqK 𝔔
  obtain ⟨e, he⟩ := W2LOC.exists_iso_forall_unit_eq q p₁ pK hq M
  obtain ⟨𝔓', h𝔓'π, h𝔓'σ⟩ := Scheme.Modules.ProjPresentation.exists_of_iso 𝔓b e
  haveI : IsFinite 𝔓'.toProj := by rw [h𝔓'π]; exact h𝔓b
  have hcoef : ∀ i, ∃ c' : Fin (N' + 1) → K,
      𝔓'.σ i = ∑ j, (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (c' j))) • 𝔔K.σ j := by
    intro i
    refine ⟨c i, ?_⟩
    rw [h𝔓'σ, hσ i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.Hom.app_smul]
    congr 1
    rw [h𝔔Kσ j, h𝔔σ]
    exact he (m j)
  have hLQF : LocallyQuasiFinite 𝔔K.toProj :=
    Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul 𝔓' 𝔔K hcoef

  let 𝔭₁ : PrimeSpectrum R₁ := ⟨RingHom.ker (algebraMap R₁ K), RingHom.ker_isPrime _⟩
  haveI : LocallyOfFiniteType 𝔔.toProj := by
    have : LocallyOfFiniteType (𝔔.toProj ≫ ProjSpace.π R₁ N') := by rw [𝔔.toProj_π]; infer_instance
    exact locallyOfFiniteType_of_comp _ (ProjSpace.π R₁ N')
  have hqf : ∀ x₁ : ↑(Limits.pullback f (ι R R₁)), f₁ x₁ = 𝔭₁ → 𝔔.toProj.QuasiFiniteAt x₁ := by
    intro x₁ hx₁
    obtain ⟨z, hz⟩ : ∃ z : ↑(Limits.pullback f (ι R K)), q z = x₁ := by
      have hpt : f₁ x₁ = (ι R₁ K) (⊥ : PrimeSpectrum K) := by
        rw [hx₁]; apply PrimeSpectrum.ext
        rw [ι, Spec.map_apply]
        simp only [CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal]
        exact (RingHom.ker_eq_comap_bot _)
      obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f₁) (g := ι R₁ K) x₁ _ hpt
      refine ⟨sqK.isoPullback.inv w, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw1]
    refine Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite h𝔔Ksq (𝔔K.toProj z) x₁ ?_
    rw [← Scheme.Hom.comp_apply, h𝔔Kcomp, Scheme.Hom.comp_apply, hz]
  obtain ⟨g₂, hg₂, hfinA⟩ :=
    Scheme.Modules.ProjPresentation.exists_finiteBySections_pullback_of_quasiFiniteAt 𝔔 𝔭₁ hqf

  obtain ⟨k, r, hr⟩ := IsLocalization.Away.surj g₁ g₂
  have hr𝔭 : r ∉ 𝔭.asIdeal := by
    intro hr'
    apply hg₂
    have h0 : algebraMap R K r = 0 := by rwa [← RingHom.mem_ker, hker]
    have h1 : algebraMap R₁ K (g₂ * algebraMap R R₁ g₁ ^ k) = 0 := by
      rw [hr, ← IsScalarTower.algebraMap_apply, h0]
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at h1
    show algebraMap R₁ K g₂ = 0
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hg₁K.ne_zero)
  refine ⟨g₁ * r, 𝔭.isPrime.mul_notMem hg₁ hr𝔭, ?_⟩
  let A : Type u := Localization.Away (g₁ * r)
  have hg₁A : IsUnit (algebraMap R A g₁) :=
    isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (g₁ * r))
  letI : Algebra R₁ A := (IsLocalization.Away.lift g₁ hg₁A).toAlgebra
  haveI : IsScalarTower R R₁ A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq g₁ hg₁A x).symm
  have hιA : ι R A = ι R₁ A ≫ ι R R₁ := by
    rw [ι, ι, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hg₂A : IsUnit (algebraMap R₁ A g₂) := by
    have hrA : IsUnit (algebraMap R A r) :=
      isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (g₁ * r))
    rw [IsScalarTower.algebraMap_apply R R₁ A, ← hr, map_mul] at hrA
    exact isUnit_of_mul_isUnit_left hrA
  let pA : Limits.pullback f (ι R A) ⟶ Limits.pullback f (ι R R₁) :=
    Limits.pullback.lift (Limits.pullback.fst f (ι R A)) (Limits.pullback.snd f (ι R A) ≫ ι R₁ A)
      (by rw [Category.assoc, ← hιA]; exact Limits.pullback.condition)
  have hpA : pA ≫ p₁ = Limits.pullback.fst f (ι R A) := Limits.pullback.lift_fst _ _ _
  have sqA : IsPullback pA (Limits.pullback.snd f (ι R A)) f₁ (ι R₁ A) := by
    refine IsPullback.of_right ?_ (Limits.pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (ι R R₁))
    rw [hpA, ← hιA]; exact IsPullback.of_hasPullback f (ι R A)
  have hF : Scheme.Modules.FiniteBySections
      ((Scheme.Modules.pullback (Limits.pullback.fst f (ι R A))).obj M) (Limits.pullback.snd f (ι R A)) := by
    refine Scheme.Modules.FiniteBySections.of_iso ?_ (hfinA A hg₂A pA _ sqA)
    exact ((Scheme.Modules.pullbackComp pA p₁).app M) ≪≫ (Scheme.Modules.pullbackCongr hpA).app M
  by_cases hn : n = 0
  · refine ⟨1, one_pos, ?_⟩
    subst hn
    have h𝒪 : Scheme.Modules.FiniteBySections
        (SheafOfModules.unit (Limits.pullback f (ι R A)).ringCatSheaf : (Limits.pullback f (ι R A)).Modules)
        (Limits.pullback.snd f (ι R A)) :=
      Scheme.Modules.FiniteBySections.of_iso (Scheme.Modules.pullbackUnitIso _) hF
    exact Scheme.Modules.FiniteBySections.of_finiteBySections_unit _ h𝒪 _ ((hL.tensorPow 1).pullback _)
  · exact ⟨n, Nat.pos_of_ne_zero hn, hF⟩

end W2LOC_assembly

end S_AlgebraicGeometry_Scheme_Modules_exists_away_finiteBySections_tensorPow_of_forall_geometricFibre
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_away_finiteBySections_tensorPow_of_forall_geometricFibre (solution)
