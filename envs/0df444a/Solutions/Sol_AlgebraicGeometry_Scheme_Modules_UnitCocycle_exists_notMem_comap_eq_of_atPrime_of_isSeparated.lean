-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_notMem_comap_eq_of_atPrime_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f4c0c0c1-9c0d-5ebd-9272-81a0e2326905

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Theorems.Thm_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated.AlgebraicGeometry TopologicalSpace Opposite"

universe u

noncomputable section

namespace LimitIso

section BaseFun

variable {R : Type u} [CommRing R] {B : Scheme.{u}} (q : B ⟶ Spec (.of R))

def baseFun (V : B.Opens) : R →+* Γ(B, V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop ≫ B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom

lemma baseFun_apply (V : B.Opens) (r : R) :
    baseFun q V r = B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (q.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) :=
  rfl

lemma map_baseFun {V W : B.Opens} (h : W ≤ V) (r : R) :
    B.presheaf.map (homOfLE h).op (baseFun q V r) = baseFun q W r := by
  rw [baseFun_apply, baseFun_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma app_baseFun {B' : Scheme.{u}} (p : B' ⟶ B) (V : B.Opens) (r : R) :
    p.app V (baseFun q V r) = baseFun (p ≫ q) (p ⁻¹ᵁ V) r := by
  rw [baseFun_apply, baseFun_apply, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2 := congrArg (fun k => (ConcreteCategory.hom k) (q.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
    (p.naturality (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CategoryTheory.comp_apply] at h2
  rw [h2]
  rfl

lemma isUnit_baseFun {T : Type u} [CommRing T] [Algebra R T]
    (s : B ⟶ Spec (.of T)) (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = q) (W : B.Opens)
    (r : R) (hr : IsUnit (algebraMap R T r)) : IsUnit (baseFun q W r) := by
  subst hs
  rw [baseFun_apply, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2 := congrArg (fun k => (ConcreteCategory.hom k) r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R T)))
  simp only [CategoryTheory.comp_apply] at h2
  rw [← h2]
  exact ((hr.map _).map _).map _

end BaseFun

section SBC

variable {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
  {B : Scheme.{u}} (q : B ⟶ Spec (.of R))

abbrev BC : Scheme.{u} := pullback q (Spec.map (CommRingCat.ofHom (algebraMap R T)))

abbrev pr : BC T q ⟶ B := pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T)))

theorem isLocalization_sections (V : B.Opens) (hV : IsAffineOpen V) :
    letI := ((pr T q).app V).hom.toAlgebra
    IsLocalization (M.map (baseFun q V : R →* Γ(B, V))) Γ(BC T q, pr T q ⁻¹ᵁ V) :=
  AlgebraicGeometry.isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen M T q V hV

lemma isUnit_baseFun_pr (W : (BC T q).Opens) (m : M) : IsUnit (baseFun (pr T q ≫ q) W m) :=
  isUnit_baseFun (pr T q ≫ q) (pullback.snd _ _) pullback.condition.symm W m (IsLocalization.map_units T m)

lemma sbc_surj (V : B.Opens) (hV : IsAffineOpen V) (x : Γ(BC T q, pr T q ⁻¹ᵁ V)) :
    ∃ (y : Γ(B, V)) (m : M), x * baseFun (pr T q ≫ q) (pr T q ⁻¹ᵁ V) m = (pr T q).app V y := by
  letI := ((pr T q).app V).hom.toAlgebra
  haveI := isLocalization_sections M T q V hV
  obtain ⟨⟨y, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (M.map (baseFun q V : R →* Γ(B, V))) x
  refine ⟨y, ⟨m, hm⟩, ?_⟩
  rw [← app_baseFun]
  exact h

lemma sbc_exists_of_eq (V : B.Opens) (hV : IsAffineOpen V) (y y' : Γ(B, V))
    (h : (pr T q).app V y = (pr T q).app V y') :
    ∃ m : M, baseFun q V m * y = baseFun q V m * y' := by
  letI := ((pr T q).app V).hom.toAlgebra
  haveI := isLocalization_sections M T q V hV
  obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩ := (IsLocalization.eq_iff_exists (M.map (baseFun q V : R →* Γ(B, V))) _).1 h
  exact ⟨⟨m, hm⟩, hc⟩

end SBC

section CoverSpread

variable {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
  {B : Scheme.{u}} (q : B ⟶ Spec (.of R))

lemma exists_mem_preimage_le_iSup_of_isAffineOpen {ι : Type*} (W : ι → B.Opens) (Y : B.Opens)
    (hY : IsAffineOpen Y) (h : pr T q ⁻¹ᵁ Y ≤ ⨆ k, pr T q ⁻¹ᵁ W k) :
    ∃ m ∈ M, ∀ (T' : Type u) [CommRing T'] [Algebra R T'], IsUnit (algebraMap R T' m) →
      pr T' q ⁻¹ᵁ Y ≤ ⨆ k, pr T' q ⁻¹ᵁ W k := by
  classical

  let H : Set Γ(B, Y) := {h | ∃ k, B.basicOpen h ≤ W k}
  have hcovB : ∀ x : B, x ∈ Y → (∃ k, x ∈ W k) → ∃ h ∈ H, x ∈ B.basicOpen h := by
    intro x hxY hk
    obtain ⟨k, hxk⟩ := hk
    obtain ⟨h, hle, hxh⟩ := hY.exists_basicOpen_le ⟨x, hxk⟩ hxY
    exact ⟨h, ⟨k, hle⟩, hxh⟩

  have hT : pr T q ⁻¹ᵁ Y ≤ ⨆ h : H, (BC T q).basicOpen ((pr T q).app Y h.1) := by
    intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (h hx)
    obtain ⟨h', hH, hxh⟩ := hcovB _ hx ⟨k, hk⟩
    refine Opens.mem_iSup.2 ⟨⟨h', hH⟩, ?_⟩
    rw [← Scheme.preimage_basicOpen]
    exact hxh
  haveI : IsAffineHom (pr T q) := MorphismProperty.pullback_fst _ _ inferInstance
  have hYT : IsAffineOpen (pr T q ⁻¹ᵁ Y) := hY.preimage (pr T q)
  have hspan : Ideal.span (((pr T q).app Y).hom '' H) = ⊤ := by
    rw [← hYT.self_le_iSup_basicOpen_iff]
    refine hT.trans (iSup_le fun h' => ?_)
    exact le_iSup (fun f : ↥(((pr T q).app Y).hom '' H) => (BC T q).basicOpen f.1) ⟨_, h'.1, h'.2, rfl⟩

  letI := ((pr T q).app Y).hom.toAlgebra
  haveI := isLocalization_sections M T q Y hY
  have h1 : (1 : Γ(BC T q, pr T q ⁻¹ᵁ Y)) ∈
      (Ideal.span H).map (algebraMap Γ(B, Y) Γ(BC T q, pr T q ⁻¹ᵁ Y)) := by
    rw [Ideal.map_span]
    change (1 : Γ(BC T q, pr T q ⁻¹ᵁ Y)) ∈ Ideal.span (((pr T q).app Y).hom '' H)
    rw [hspan]; trivial
  obtain ⟨⟨⟨a, ha⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, hma⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M.map (baseFun q Y : R →* Γ(B, Y))) _).1 h1
  simp only [one_mul] at hma
  obtain ⟨⟨_, ⟨m', hm', rfl⟩⟩, hc⟩ :=
    (IsLocalization.eq_iff_exists (M.map (baseFun q Y : R →* Γ(B, Y))) _).1 hma
  have hc' : baseFun q Y m' * baseFun q Y m = baseFun q Y m' * a := hc
  refine ⟨m' * m, M.mul_mem hm' hm, fun T' _ _ hu => ?_⟩
  have hmem : baseFun q Y (m' * m) ∈ Ideal.span H := by
    rw [map_mul, hc']
    exact Ideal.mul_mem_left _ _ ha
  haveI : IsAffineHom (pr T' q) := MorphismProperty.pullback_fst _ _ inferInstance
  have hYT' : IsAffineOpen (pr T' q ⁻¹ᵁ Y) := hY.preimage (pr T' q)
  have hspan' : Ideal.span (((pr T' q).app Y).hom '' H) = ⊤ := by
    rw [← Ideal.map_span]
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem) ?_
    change IsUnit ((pr T' q).app Y (baseFun q Y (m' * m)))
    rw [app_baseFun]
    exact isUnit_baseFun _ _ pullback.condition.symm _ _ hu
  refine ((hYT'.self_le_iSup_basicOpen_iff).2 hspan').trans (iSup_le fun f => ?_)
  obtain ⟨f, h', ⟨k, hk⟩, rfl⟩ := f
  calc (BC T' q).basicOpen (((pr T' q).app Y).hom h') = pr T' q ⁻¹ᵁ B.basicOpen h' :=
        (Scheme.preimage_basicOpen _ _).symm
    _ ≤ pr T' q ⁻¹ᵁ W k := (pr T' q).preimage_mono hk
    _ ≤ ⨆ k, pr T' q ⁻¹ᵁ W k := le_iSup (fun k => pr T' q ⁻¹ᵁ W k) k

theorem exists_mem_iSup_preimage_eq_top [CompactSpace B] {ι : Type*} (W : ι → B.Opens)
    (hcov : ⨆ k, pr T q ⁻¹ᵁ W k = ⊤) :
    ∃ m ∈ M, ∀ (T' : Type u) [CommRing T'] [Algebra R T'], IsUnit (algebraMap R T' m) →
      ⨆ k, pr T' q ⁻¹ᵁ W k = ⊤ := by
  classical
  obtain ⟨S, hSfin, htop⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : B.Opens))).1
    (by simpa using isCompact_univ)
  haveI : Fintype S := hSfin.fintype
  have key := fun Y : S => exists_mem_preimage_le_iSup_of_isAffineOpen M T q W Y Y.1.2
    (by rw [hcov]; exact le_top)
  choose m hm hstage using key
  refine ⟨∏ Y : S, (m Y : R), M.prod_mem fun Y _ => hm Y, fun T' _ _ hu => ?_⟩
  refine top_le_iff.mp fun x _ => ?_
  have hx : (pr T' q) x ∈ (⨆ Y ∈ S, (Y : B.Opens)) := by rw [← htop]; trivial
  obtain ⟨Y, hY⟩ := Opens.mem_iSup.1 hx
  obtain ⟨hYS, hxY⟩ := Opens.mem_iSup.1 hY
  exact hstage ⟨Y, hYS⟩ T'
    (isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun Y : S => (m Y : R)) (Finset.mem_univ _))) hu)
    hxY

end CoverSpread

end LimitIso

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app Scheme.Hom QuasiCompact Scheme.preimage_basicOpen Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appTop Scheme.Hom.preimage_mono IsSeparated Scheme.Hom.comp_app isAffineOpen_top isAffineHom_diagonal_iff IsAffineOpen isCompact_iff_finite_and_eq_biUnion_affineOpens Scheme.Modules Scheme.Hom.comp_preimage IsAffineHom Scheme.ΓSpecIso Scheme.Modules.UnitCocycle isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen" namespace LimitPic end AlgebraicGeometry.LimitPic
p2m_open_scoped "AlgebraicGeometry" in
theorem AlgebraicGeometry.LimitPic.iSup_preimage_eq_top_of_dvd
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f]
    (𝔭 : Ideal S) [𝔭.IsPrime] {ι : Type u} [Finite ι] (W : ι → A.Opens) (hW : ∀ k, IsAffineOpen (W k))
    (hcov : (⨆ k, (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) = ⊤) :
    ∃ r₀ : S, r₀ ∉ 𝔭 ∧ ∀ r : S, r₀ ∣ r →
      (⨆ k, (Limits.pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k) = ⊤ := by
  haveI : CompactSpace ↥(Spec (CommRingCat.of S)) := (inferInstance : CompactSpace (PrimeSpectrum S))
  haveI : CompactSpace ↥A := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨m, hm, H⟩ :=
    LimitIso.exists_mem_iSup_preimage_eq_top 𝔭.primeCompl (Localization.AtPrime 𝔭) f W hcov
  exact ⟨m, hm, fun r hr => H (Localization.Away r) (IsLocalization.Away.isUnit_of_dvd (x := r) hr)⟩

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app Scheme.Hom QuasiCompact Scheme.preimage_basicOpen Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appTop Scheme.Hom.preimage_mono IsSeparated Scheme.Hom.comp_app isAffineOpen_top isAffineHom_diagonal_iff IsAffineOpen isCompact_iff_finite_and_eq_biUnion_affineOpens Scheme.Modules Scheme.Hom.comp_preimage IsAffineHom Scheme.ΓSpecIso Scheme.Modules.UnitCocycle isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen"
namespace CocycleStage
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated.LimitIso"

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))

theorem isAffineOpen_inf [IsSeparated f] {U V : A.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) :=
  (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

variable (𝔭 : Ideal S) [𝔭.IsPrime]

private def _root_.AlgebraicGeometry.CocycleStage.trans (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭)) :
    BC (Localization.AtPrime 𝔭) f ⟶ BC (Localization.Away r) f :=
  Limits.pullback.lift (pr (Localization.AtPrime 𝔭) f)
    (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
      Spec.map (CommRingCat.ofHom ψ))
    (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])

p2m_export "AlgebraicGeometry.CocycleStage" "trans"
variable {𝔭} in
theorem trans_pr (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭)) :
    trans f 𝔭 r ψ hψ ≫ pr (Localization.Away r) f = pr (Localization.AtPrime 𝔭) f :=
  Limits.pullback.lift_fst _ _ _

variable {𝔭} in
theorem preimage_trans_pr (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭)) (W : A.Opens) :
    trans f 𝔭 r ψ hψ ⁻¹ᵁ (pr (Localization.Away r) f ⁻¹ᵁ W) = pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, trans_pr]

def θ (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭)) (V : A.Opens) :
    Γ(BC (Localization.Away r) f, pr (Localization.Away r) f ⁻¹ᵁ V) →+*
      Γ(BC (Localization.AtPrime 𝔭) f, pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ V) :=
  ((trans f 𝔭 r ψ hψ).app (pr (Localization.Away r) f ⁻¹ᵁ V) ≫
    (BC (Localization.AtPrime 𝔭) f).presheaf.map (eqToHom (preimage_trans_pr f r ψ hψ V).symm).op).hom

variable {𝔭} in
theorem θ_app (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭)) (V : A.Opens)
    (y : Γ(A, V)) :
    θ f 𝔭 r ψ hψ V ((pr (Localization.Away r) f).app V y) = (pr (Localization.AtPrime 𝔭) f).app V y := by
  have h := Scheme.Hom.congr_app (trans_pr f r ψ hψ).symm V
  rw [h, Scheme.Hom.comp_app]
  rfl

variable {𝔭} in
theorem app_rO (T : Type u) [CommRing T] [Algebra S T] {V V' : A.Opens} (h : V' ≤ V) (y : Γ(A, V)) :
    GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) h) ((pr T f).app V y) = (pr T f).app V' (GlueOfCocycle.rO h y) := by
  have := congrArg (fun k => (ConcreteCategory.hom k) y) ((pr T f).naturality (homOfLE h).op)
  simp only [CategoryTheory.comp_apply] at this
  exact this.symm

variable {𝔭} in

theorem map_eqToHom_baseFun {B : Scheme.{u}} (q : B ⟶ Spec (.of S)) {W W' : B.Opens} (e : W = W') (m : S) :
    B.presheaf.map (eqToHom e).op (baseFun q W' m) = baseFun q W m := by
  rw [Subsingleton.elim (eqToHom e) (homOfLE e.le), map_baseFun]

variable {𝔭} in
theorem θ_baseFun (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭)) (V : A.Opens) (m : S) :
    θ f 𝔭 r ψ hψ V (baseFun (pr (Localization.Away r) f ≫ f) (pr (Localization.Away r) f ⁻¹ᵁ V) m) =
      baseFun (pr (Localization.AtPrime 𝔭) f ≫ f) (pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ V) m := by
  change (BC (Localization.AtPrime 𝔭) f).presheaf.map (eqToHom (preimage_trans_pr f r ψ hψ V).symm).op
      ((trans f 𝔭 r ψ hψ).app _ (baseFun (pr (Localization.Away r) f ≫ f) (pr (Localization.Away r) f ⁻¹ᵁ V) m)) = _
  rw [app_baseFun, map_eqToHom_baseFun, ← Category.assoc, trans_pr]

section Stage

variable {𝔭}
variable {ι : Type u} (W : ι → A.Opens)
  (T : Type u) [CommRing T] [Algebra S T]
  (y : ∀ i j, Γ(A, W i ⊓ W j)) (m : ∀ i j, S) (hm : ∀ i j, IsUnit (algebraMap S T (m i j)))

def bfU (V : A.Opens) (s : S) (hs : IsUnit (algebraMap S T s)) : (Γ(BC T f, pr T f ⁻¹ᵁ V))ˣ :=
  (isUnit_baseFun (pr T f ≫ f) (Limits.pullback.snd _ _) Limits.pullback.condition.symm (pr T f ⁻¹ᵁ V) s hs).unit

theorem bfU_val (V : A.Opens) (s : S) (hs : IsUnit (algebraMap S T s)) :
    (bfU f T V s hs : Γ(BC T f, pr T f ⁻¹ᵁ V)) = baseFun (pr T f ≫ f) (pr T f ⁻¹ᵁ V) s := rfl

def uT (i j : ι) : Γ(BC T f, pr T f ⁻¹ᵁ (W i ⊓ W j)) :=
  (pr T f).app (W i ⊓ W j) (y i j) * ↑(bfU f T (W i ⊓ W j) (m i j) (hm i j))⁻¹

theorem uT_mul_bf (i j : ι) :
    uT f W T y m hm i j * baseFun (pr T f ≫ f) (pr T f ⁻¹ᵁ (W i ⊓ W j)) (m i j) = (pr T f).app (W i ⊓ W j) (y i j) := by
  change (pr T f).app (W i ⊓ W j) (y i j) * ↑(bfU f T (W i ⊓ W j) (m i j) (hm i j))⁻¹ *
    ↑(bfU f T (W i ⊓ W j) (m i j) (hm i j)) = _
  rw [Units.inv_mul_cancel_right]

end Stage

section Stage2

variable {𝔭}
variable {ι : Type u} (W : ι → A.Opens)
  (T : Type u) [CommRing T] [Algebra S T]
  (y : ∀ i j, Γ(A, W i ⊓ W j)) (m : ∀ i j, S) (hm : ∀ i j, IsUnit (algebraMap S T (m i j)))

abbrev bfT (V : A.Opens) (s : S) : Γ(BC T f, pr T f ⁻¹ᵁ V) := baseFun (pr T f ≫ f) (pr T f ⁻¹ᵁ V) s

abbrev bfA (V : A.Opens) (s : S) : Γ(A, V) := baseFun f V s

theorem app_bfA (V : A.Opens) (s : S) : (pr T f).app V (bfA f V s) = bfT f T V s := app_baseFun f (pr T f) V s

theorem isUnit_bfT (V : A.Opens) (s : S) (hs : IsUnit (algebraMap S T s)) : IsUnit (bfT f T V s) :=
  isUnit_baseFun (pr T f ≫ f) (Limits.pullback.snd _ _) Limits.pullback.condition.symm _ s hs

theorem uT_refl (i : ι) (t : S) (ht : IsUnit (algebraMap S T t))
    (H : bfA f (W i ⊓ W i) t * y i i = bfA f (W i ⊓ W i) t * bfA f (W i ⊓ W i) (m i i)) :
    uT f W T y m hm i i = 1 := by
  have h1 : (pr T f).app (W i ⊓ W i) (y i i) = bfT f T (W i ⊓ W i) (m i i) := by
    have := congrArg ((pr T f).app (W i ⊓ W i)) H
    simp only [map_mul, app_bfA] at this
    exact (isUnit_bfT f T _ t ht).mul_left_cancel this
  change (pr T f).app (W i ⊓ W i) (y i i) * ↑(bfU f T (W i ⊓ W i) (m i i) (hm i i))⁻¹ = 1
  rw [h1]
  exact Units.mul_inv_eq_one.mpr rfl

abbrev le12 (i j k : ι) : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j := le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
abbrev le23 (i j k : ι) : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
abbrev le13 (i j k : ι) : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k := le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem uT_cocycle (i j k : ι) (t : S) (ht : IsUnit (algebraMap S T t))
    (H : bfA f (W i ⊓ W j ⊓ W k) t *
          (GlueOfCocycle.rO (le12 W i j k) (y i j) * GlueOfCocycle.rO (le23 W i j k) (y j k) *
            bfA f (W i ⊓ W j ⊓ W k) (m i k)) =
        bfA f (W i ⊓ W j ⊓ W k) t *
          (GlueOfCocycle.rO (le13 W i j k) (y i k) * bfA f (W i ⊓ W j ⊓ W k) (m i j) *
            bfA f (W i ⊓ W j ⊓ W k) (m j k))) :
    GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le12 W i j k)) (uT f W T y m hm i j) *
        GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le23 W i j k)) (uT f W T y m hm j k) =
      GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le13 W i j k)) (uT f W T y m hm i k) := by

  have hB : IsUnit (bfT f T (W i ⊓ W j ⊓ W k) (m i j) * bfT f T (W i ⊓ W j ⊓ W k) (m j k) * bfT f T (W i ⊓ W j ⊓ W k) (m i k) * bfT f T (W i ⊓ W j ⊓ W k) t) :=
    (((isUnit_bfT f T (W i ⊓ W j ⊓ W k) _ (hm i j)).mul (isUnit_bfT f T (W i ⊓ W j ⊓ W k) _ (hm j k))).mul (isUnit_bfT f T (W i ⊓ W j ⊓ W k) _ (hm i k))).mul
      (isUnit_bfT f T (W i ⊓ W j ⊓ W k) _ ht)
  apply (hB.mul_left_inj).mp

  have rij : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le12 W i j k)) (uT f W T y m hm i j) * bfT f T (W i ⊓ W j ⊓ W k) (m i j) =
      (pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le12 W i j k) (y i j)) := by
    rw [← app_rO, ← uT_mul_bf f W T y m hm i j, map_mul]
    congr 1
    exact (map_baseFun _ _ _).symm
  have rjk : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le23 W i j k)) (uT f W T y m hm j k) * bfT f T (W i ⊓ W j ⊓ W k) (m j k) =
      (pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le23 W i j k) (y j k)) := by
    rw [← app_rO, ← uT_mul_bf f W T y m hm j k, map_mul]
    congr 1
    exact (map_baseFun _ _ _).symm
  have rik : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le13 W i j k)) (uT f W T y m hm i k) * bfT f T (W i ⊓ W j ⊓ W k) (m i k) =
      (pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le13 W i j k) (y i k)) := by
    rw [← app_rO, ← uT_mul_bf f W T y m hm i k, map_mul]
    congr 1
    exact (map_baseFun _ _ _).symm
  have H' := congrArg ((pr T f).app (W i ⊓ W j ⊓ W k)) H
  simp only [map_mul, app_bfA] at H'

  calc _ = (GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le12 W i j k)) (uT f W T y m hm i j) * bfT f T (W i ⊓ W j ⊓ W k) (m i j)) *
        (GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le23 W i j k)) (uT f W T y m hm j k) * bfT f T (W i ⊓ W j ⊓ W k) (m j k)) *
        bfT f T (W i ⊓ W j ⊓ W k) (m i k) * bfT f T (W i ⊓ W j ⊓ W k) t := by ring
    _ = (pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le12 W i j k) (y i j)) * (pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le23 W i j k) (y j k)) *
        bfT f T (W i ⊓ W j ⊓ W k) (m i k) * bfT f T (W i ⊓ W j ⊓ W k) t := by rw [rij, rjk]
    _ = bfT f T (W i ⊓ W j ⊓ W k) t * ((pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le12 W i j k) (y i j)) *
        (pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le23 W i j k) (y j k)) * bfT f T (W i ⊓ W j ⊓ W k) (m i k)) := by ring
    _ = bfT f T (W i ⊓ W j ⊓ W k) t * ((pr T f).app (W i ⊓ W j ⊓ W k) (GlueOfCocycle.rO (le13 W i j k) (y i k)) * bfT f T (W i ⊓ W j ⊓ W k) (m i j) * bfT f T (W i ⊓ W j ⊓ W k) (m j k)) := H'
    _ = (GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr T f) (le13 W i j k)) (uT f W T y m hm i k) * bfT f T (W i ⊓ W j ⊓ W k) (m i k)) *
        bfT f T (W i ⊓ W j ⊓ W k) (m i j) * bfT f T (W i ⊓ W j ⊓ W k) (m j k) * bfT f T (W i ⊓ W j ⊓ W k) t := by rw [rik]; ring
    _ = _ := by ring

end Stage2

section Assembly

variable {𝔭}

theorem θ_uT_eq {ι : Type u} (W : ι → A.Opens) (r : S) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭))
    (y : ∀ i j, Γ(A, W i ⊓ W j)) (m : ∀ i j, S) (hm : ∀ i j, IsUnit (algebraMap S (Localization.Away r) (m i j)))
    (i j : ι) (x : Γ(BC (Localization.AtPrime 𝔭) f, pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ (W i ⊓ W j)))
    (hmM : m i j ∈ 𝔭.primeCompl)
    (hx : x * bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j) (m i j) =
      (pr (Localization.AtPrime 𝔭) f).app (W i ⊓ W j) (y i j)) :
    θ f 𝔭 r ψ hψ (W i ⊓ W j) (uT f W (Localization.Away r) y m hm i j) = x := by
  have hu : IsUnit (bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j) (m i j)) :=
    isUnit_bfT f (Localization.AtPrime 𝔭) _ _ (IsLocalization.map_units _ ⟨m i j, hmM⟩)
  apply (hu.mul_left_inj).mp
  rw [hx]
  change _ * baseFun (pr (Localization.AtPrime 𝔭) f ≫ f) (pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ (W i ⊓ W j)) (m i j) = _
  rw [← θ_baseFun f r ψ hψ (W i ⊓ W j) (m i j), ← map_mul]
  change θ f 𝔭 r ψ hψ (W i ⊓ W j) (uT f W (Localization.Away r) y m hm i j *
    baseFun (pr (Localization.Away r) f ≫ f) (pr (Localization.Away r) f ⁻¹ᵁ (W i ⊓ W j)) (m i j)) = _
  rw [uT_mul_bf, θ_app]

variable (𝔭)

theorem main [QuasiCompact f] [IsSeparated f] {ι : Type u} [Finite ι] (W : ι → A.Opens)
    (hW : ∀ k, IsAffineOpen (W k))
    (hcov : (⨆ k, pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ W k) = ⊤)
    (g : UnitCocycle fun k => pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ W k) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
      (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭))
      (c : UnitCocycle fun k => pr (Localization.Away r) f ⁻¹ᵁ W k),
      (⨆ k, pr (Localization.Away r) f ⁻¹ᵁ W k) = ⊤ ∧
      ∀ i j, θ f 𝔭 r ψ hψ (W i ⊓ W j) (c.u i j) = g.u i j := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hWij : ∀ i j, IsAffineOpen (W i ⊓ W j) := fun i j => isAffineOpen_inf f (hW i) (hW j)
  have hWijk : ∀ i j k, IsAffineOpen (W i ⊓ W j ⊓ W k) := fun i j k => isAffineOpen_inf f (hWij i j) (hW k)

  have dat : ∀ i j, ∃ (y : Γ(A, W i ⊓ W j)) (m : 𝔭.primeCompl),
      (show Γ(BC (Localization.AtPrime 𝔭) f, pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ (W i ⊓ W j)) from g.u i j) *
        bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j) m = (pr (Localization.AtPrime 𝔭) f).app _ y :=
    fun i j => sbc_surj 𝔭.primeCompl (Localization.AtPrime 𝔭) f (W i ⊓ W j) (hWij i j)
      (show Γ(BC (Localization.AtPrime 𝔭) f, pr (Localization.AtPrime 𝔭) f ⁻¹ᵁ (W i ⊓ W j)) from g.u i j)
  choose y m hym using dat
  have drefl : ∀ i, ∃ t : 𝔭.primeCompl, bfA f (W i ⊓ W i) t * y i i = bfA f (W i ⊓ W i) t * bfA f (W i ⊓ W i) (m i i) := by
    intro i
    apply sbc_exists_of_eq 𝔭.primeCompl (Localization.AtPrime 𝔭) f (W i ⊓ W i) (hWij i i)
    rw [← hym i i, app_bfA]
    change g.u i i * _ = _
    rw [g.refl i, one_mul]
  choose t₁ ht₁ using drefl
  have dcoc : ∀ i j k, ∃ t : 𝔭.primeCompl,
      bfA f (W i ⊓ W j ⊓ W k) t *
          (GlueOfCocycle.rO (le12 W i j k) (y i j) * GlueOfCocycle.rO (le23 W i j k) (y j k) *
            bfA f (W i ⊓ W j ⊓ W k) (m i k)) =
        bfA f (W i ⊓ W j ⊓ W k) t *
          (GlueOfCocycle.rO (le13 W i j k) (y i k) * bfA f (W i ⊓ W j ⊓ W k) (m i j) *
            bfA f (W i ⊓ W j ⊓ W k) (m j k)) := by
    intro i j k
    apply sbc_exists_of_eq 𝔭.primeCompl (Localization.AtPrime 𝔭) f _ (hWijk i j k)
    simp only [map_mul, app_bfA, ← app_rO]
    rw [← hym i j, ← hym j k, ← hym i k]
    simp only [map_mul]
    have e1 : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le12 W i j k))
        (bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j) ↑(m i j)) = bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j ⊓ W k) ↑(m i j) :=
      map_baseFun _ _ _
    have e2 : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le23 W i j k))
        (bfT f (Localization.AtPrime 𝔭) (W j ⊓ W k) ↑(m j k)) = bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j ⊓ W k) ↑(m j k) :=
      map_baseFun _ _ _
    have e3 : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le13 W i j k))
        (bfT f (Localization.AtPrime 𝔭) (W i ⊓ W k) ↑(m i k)) = bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j ⊓ W k) ↑(m i k) :=
      map_baseFun _ _ _
    rw [e1, e2, e3]
    have hc : GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le12 W i j k)) (g.u i j) *
        GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le23 W i j k)) (g.u j k) =
        GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le13 W i j k)) (g.u i k) :=
      g.cocycle i j k
    calc _ = (GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le12 W i j k)) (g.u i j) *
          GlueOfCocycle.rO (Scheme.Hom.preimage_mono (pr (Localization.AtPrime 𝔭) f) (le23 W i j k)) (g.u j k)) *
          bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j ⊓ W k) ↑(m i j) * bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j ⊓ W k) ↑(m j k) *
          bfT f (Localization.AtPrime 𝔭) (W i ⊓ W j ⊓ W k) ↑(m i k) := by ring
      _ = _ := by rw [hc]; ring
  choose t₃ ht₃ using dcoc

  obtain ⟨r₀, hr₀, hcovr⟩ := AlgebraicGeometry.LimitPic.iSup_preimage_eq_top_of_dvd f 𝔭 W hW hcov
  let P : S := (∏ i, ∏ j, (m i j : S)) * (∏ i, (t₁ i : S)) * ∏ i, ∏ j, ∏ k, (t₃ i j k : S)
  let r : S := r₀ * P
  have hP : P ∈ 𝔭.primeCompl := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.prod_mem _ fun j _ => (m i j).2
    · exact Submonoid.prod_mem _ fun i _ => (t₁ i).2
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.prod_mem _ fun j _ => Submonoid.prod_mem _ fun k _ => (t₃ i j k).2
  have hr : r ∈ 𝔭.primeCompl := Submonoid.mul_mem _ hr₀ hP
  have hunit : ∀ s : S, s ∣ r → IsUnit (algebraMap S (Localization.Away r) s) := fun s hs =>
    isUnit_of_dvd_unit (map_dvd _ hs) (IsLocalization.Away.algebraMap_isUnit r)
  have hmd : ∀ i j, (m i j : S) ∣ r := fun i j => by
    have h1 : (m i j : S) ∣ ∏ i, ∏ j, (m i j : S) :=
      (Finset.dvd_prod_of_mem (fun j => (m i j : S)) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (m i j : S)) (Finset.mem_univ i))
    exact ((h1.mul_right _).mul_right _).mul_left _
  have ht₁d : ∀ i, (t₁ i : S) ∣ r := fun i => by
    have h1 : (t₁ i : S) ∣ ∏ i, (t₁ i : S) := Finset.dvd_prod_of_mem (fun i => (t₁ i : S)) (Finset.mem_univ i)
    exact ((h1.mul_left _).mul_right _).mul_left _
  have ht₃d : ∀ i j k, (t₃ i j k : S) ∣ r := fun i j k => by
    have h1 : (t₃ i j k : S) ∣ ∏ i, ∏ j, ∏ k, (t₃ i j k : S) :=
      ((Finset.dvd_prod_of_mem (fun k => (t₃ i j k : S)) (Finset.mem_univ k)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ k, (t₃ i j k : S)) (Finset.mem_univ j))).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, ∏ k, (t₃ i j k : S)) (Finset.mem_univ i))
    exact (h1.mul_left _).mul_left _
  have hmr : ∀ i j, IsUnit (algebraMap S (Localization.Away r) (m i j : S)) := fun i j => hunit _ (hmd i j)
  let ψ : Localization.Away r →+* Localization.AtPrime 𝔭 :=
    IsLocalization.Away.lift r (g := algebraMap S (Localization.AtPrime 𝔭)) (IsLocalization.map_units _ ⟨r, hr⟩)
  have hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭) :=
    IsLocalization.Away.lift_comp r _
  let c : UnitCocycle fun k => pr (Localization.Away r) f ⁻¹ᵁ W k :=
    { u := fun i j => uT f W (Localization.Away r) y (fun i j => (m i j : S)) hmr i j
      refl := fun i => uT_refl f W (Localization.Away r) y (fun i j => (m i j : S)) hmr i (t₁ i) (hunit _ (ht₁d i)) (ht₁ i)
      cocycle := fun i j k =>
        uT_cocycle f W (Localization.Away r) y (fun i j => (m i j : S)) hmr i j k (t₃ i j k) (hunit _ (ht₃d i j k))
          (ht₃ i j k) }
  refine ⟨r, hr, ψ, hψ, c, hcovr r (dvd_mul_right _ _), fun i j => ?_⟩
  exact θ_uT_eq f W r ψ hψ y (fun i j => (m i j : S)) hmr i j (g.u i j) (m i j).2 (hym i j)

end Assembly

end AlgebraicGeometry.CocycleStage

end

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    [QuasiCompact f] [IsSeparated f] (𝔭 : Ideal S) [𝔭.IsPrime]
    {ι : Type u} [Finite ι] (W : ι → A.Opens) (hW : ∀ k, IsAffineOpen (W k))
    (hcov : (⨆ k, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) = ⊤)
    (g : Scheme.Modules.UnitCocycle fun k =>
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
      (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭))
      (c : Scheme.Modules.UnitCocycle fun k =>
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k),
      (⨆ k, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k) = ⊤ ∧
      ∀ (i j : ι)
        (e : (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W i ⊓
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W j =
            (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W i) ⊓
            (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W j)),
        (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))).presheaf.map
            (eqToHom e).op
            ((c.comap
              (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]))).u i j) =
          g.u i j := by
  obtain ⟨r, hr, ψ, hψ, c, hcov', hc⟩ := AlgebraicGeometry.CocycleStage.main f 𝔭 W hW hcov g
  exact ⟨r, hr, ψ, hψ, c, hcov', fun i j e => hc i j⟩

end S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated (solution)
