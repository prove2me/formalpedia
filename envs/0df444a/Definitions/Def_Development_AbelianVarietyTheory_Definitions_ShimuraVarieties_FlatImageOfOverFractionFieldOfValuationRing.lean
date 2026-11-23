-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:33.955645+00:00
-- url     : https://prove2.me/theorems/5a553b8a-306a-4dd4-9ead-d2e5a095d1c9
-- title:
--   Flat Image Of Over Fraction Field Of Valuation Ring
-- statement:
--   Definitions and structural lemmas for Flat Image Of Over Fraction Field Of Valuation Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
namespace GlobalTheory
noncomputable section
section Dominant
variable {T' T P : Scheme.{u}}
theorem ker_comp_of_schemeDominant (d : T' ⟶ T) (t : T ⟶ P) [IsSchemeTheoreticallyDominant d] :
    (d ≫ t).ker = t.ker := by
  rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]
theorem schemeDominant_of_comp (d : T' ⟶ T) (t : T ⟶ P) [IsSchemeTheoreticallyDominant (d ≫ t)] :
    IsSchemeTheoreticallyDominant t :=
  ⟨le_bot_iff.mp ((d.le_ker_comp t).trans (d ≫ t).ker_eq_bot.le)⟩
theorem schemeDominant_specMap_iff {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    IsSchemeTheoreticallyDominant (Spec.map φ) ↔ Function.Injective φ.hom := by
  have e : φ = (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso R').hom := by
    simp
  constructor
  · intro h
    rw [e]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').hom).1.comp
      (((Spec.map φ).app_injective ⊤).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1)
  · intro h
    have e' : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso R').inv := by
      simp
    have hi : Function.Injective (Spec.map φ).appTop.hom := by
      rw [e']
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').inv).1.comp
        (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hi
theorem isIntegral_of_schemeDominant (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    [QuasiCompact d] [IsIntegral T'] : IsIntegral T := by
  have : IsReduced T := IsSchemeTheoreticallyDominant.isReduced d
  have h : IsIrreducible (closure (Set.range d)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ T').image _ d.continuous.continuousOn).closure
  rw [d.denseRange.closure_range] at h
  have : IrreducibleSpace T := (irreducibleSpace_def T).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced T
set_option backward.isDefEq.respectTransparency false in

theorem eq_zero_of_mul_eq_zero_of_flat {S : Scheme.{u}} [IsAffine S] (s : T ⟶ S) [Flat s]
    (V : T.Opens) (r : Γ(S, ⊤)) (hr : r ∈ nonZeroDivisors Γ(S, ⊤)) (a : Γ(T, V))
    (h : s.appLE ⊤ V le_top r * a = 0) : a = 0 := by
  refine T.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨V', hVV, hxV, ?_⟩
  have hf : (s.appLE ⊤ V' le_top).hom.Flat := s.flat_appLE (isAffineOpen_top S) hV' le_top
  letI := (s.appLE ⊤ V' le_top).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) Γ(T, V') := hf
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(T, V')) hr
  have h' := congrArg (T.presheaf.map (homOfLE hVV).op) h
  rw [map_mul, map_zero, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h'
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h'
set_option backward.isDefEq.respectTransparency false in

theorem flat_of_schemeDominant_of_torsionFree_flat {O : CommRingCat.{u}}
    (hO : ∀ (M : Type u) [AddCommGroup M] [Module O M],
      Submodule.torsion O M = ⊥ → Module.Flat O M)
    (d : T' ⟶ T) (s : T ⟶ Spec O) [IsSchemeTheoreticallyDominant d] [QuasiCompact d]
    [Flat (d ≫ s)] : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : T.affineOpens ↦ U)
    (iSup_affineOpens_eq_top T) fun U ↦ ?_
  rw [← RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso O).inv]
  letI := ((s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso O).inv.hom).toAlgebra
  refine hO Γ(T, U) ?_
  rw [eq_bot_iff]
  rintro a ⟨⟨r, hr⟩, ha⟩
  have hr' : (Scheme.ΓSpecIso O).inv r ∈ nonZeroDivisors Γ(Spec O, ⊤) := by
    have := (MulEquivClass.map_nonZeroDivisors
      (Scheme.ΓSpecIso O).symm.commRingCatIsoToRingEquiv)
    rw [← this]
    exact ⟨r, hr, rfl⟩
  have ha' : s.appLE ⊤ U le_top ((Scheme.ΓSpecIso O).inv r) * a = 0 := ha
  have h0 : d.app U a = 0 := by
    refine eq_zero_of_mul_eq_zero_of_flat (d ≫ s) (d ⁻¹ᵁ U) _ hr' _ ?_
    have := congrArg (d.app U) ha'
    rw [map_mul, map_zero, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE] at this
    rw [Scheme.Hom.app_eq_appLE]
    exact this
  exact (d.app_injective U) (h0.trans (map_zero _).symm)
theorem flat_of_schemeDominant_of_isDedekindDomain {O : CommRingCat.{u}} [IsDedekindDomain O]
    (d : T' ⟶ T) (s : T ⟶ Spec O) [IsSchemeTheoreticallyDominant d] [QuasiCompact d]
    [Flat (d ≫ s)] : Flat s :=
  flat_of_schemeDominant_of_torsionFree_flat
    (fun _ _ _ ↦ IsDedekindDomain.flat_iff_torsion_eq_bot.mpr) d s
theorem flat_specMap_localization {O : Type u} [CommRing O] (M : Submonoid O) (K : Type u)
    [CommRing K] [Algebra O K] [IsLocalization M K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K M)
theorem flat_of_over_fractionField {O K : Type u} [CommRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (s : T ⟶ Spec (.of O)) (s' : T ⟶ Spec (.of K))
    (h : s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = s) : Flat s := by
  have := flat_specMap_localization (nonZeroDivisors O) K
  rw [← h]
  infer_instance
end Dominant
section Closure
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)
theorem ker_le_ker_of_schemeDominant (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : j.ker ≤ t.ker := by
  rw [← ker_comp_of_schemeDominant d t, h]
  exact w.le_ker_comp j
def closureLift (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : T ⟶ j.image :=
  IsClosedImmersion.lift j.imageι t
    (by simpa using ker_le_ker_of_schemeDominant j t d w h)
@[reassoc (attr := simp)]
theorem closureLift_imageι (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : closureLift j t d w h ≫ j.imageι = t :=
  IsClosedImmersion.lift_fac _ _ _
@[reassoc (attr := simp)]
theorem comp_closureLift (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : d ≫ closureLift j t d w h = w ≫ j.toImage := by
  rw [← cancel_mono j.imageι]
  simp [h]
theorem closure_hom_ext {a b : T ⟶ j.image} (h : a ≫ j.imageι = b ≫ j.imageι) : a = b :=
  (cancel_mono j.imageι).mp h
def closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i] (h : g ≫ i = j) :
    j.image ⟶ Z :=
  IsClosedImmersion.lift i j.imageι (by simpa [← h] using g.le_ker_comp i)
@[reassoc (attr := simp)]
theorem closureToClosed_comp (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i] (h : g ≫ i = j) :
    closureToClosed j g i h ≫ i = j.imageι :=
  IsClosedImmersion.lift_fac _ _ _
@[reassoc (attr := simp)]
theorem toImage_closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i] (h : g ≫ i = j) :
    j.toImage ≫ closureToClosed j g i h = g := by
  rw [← cancel_mono i]
  simp [h]
instance isClosedImmersion_closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i]
    (h : g ≫ i = j) : IsClosedImmersion (closureToClosed j g i h) :=
  have : IsClosedImmersion (closureToClosed j g i h ≫ i) := by
    rw [closureToClosed_comp]; infer_instance
  .of_comp _ i
instance schemeDominant_toImage : IsSchemeTheoreticallyDominant j.toImage := by
  let c := closureToClosed j j.toImage.toImage (j.toImage.imageι ≫ j.imageι) (by simp)
  have hc : c ≫ j.toImage.imageι = 𝟙 _ := by
    rw [← cancel_mono j.imageι, Category.assoc, closureToClosed_comp, Category.id_comp]
  have : IsSchemeTheoreticallyDominant (c ≫ j.toImage.imageι) := by
    rw [hc]; infer_instance
  have := schemeDominant_of_comp c j.toImage.imageι
  exact ⟨by simpa using j.toImage.imageι.ker_eq_bot⟩
instance isIso_closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i]
    [IsSchemeTheoreticallyDominant g] (h : g ≫ i = j) : IsIso (closureToClosed j g i h) :=
  IsClosedImmersion.isIso_of_ker_eq j.imageι i _ (closureToClosed_comp j g i h)
    (by simp [← h, ker_comp_of_schemeDominant])
theorem isIso_imageι_iff : IsIso j.imageι ↔ IsSchemeTheoreticallyDominant j := by
  rw [Scheme.isIso_subschemeι_iff_eq_bot, isSchemeTheoreticallyDominant_iff]
theorem isOpenImmersion_toImage [IsImmersion j] [QuasiCompact j] : IsOpenImmersion j.toImage :=
  inferInstance
theorem range_imageι [QuasiCompact j] : Set.range j.imageι = closure (Set.range j) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
instance isReduced_image [QuasiCompact j] [IsReduced W] : IsReduced j.image :=
  IsSchemeTheoreticallyDominant.isReduced j.toImage
instance isIntegral_image [QuasiCompact j] [IsIntegral W] : IsIntegral j.image :=
  isIntegral_of_schemeDominant j.toImage
theorem flat_image_of_isDedekindDomain {O : CommRingCat.{u}} [IsDedekindDomain O]
    (s : P ⟶ Spec O) [QuasiCompact j] [Flat (j ≫ s)] : Flat (j.imageι ≫ s) :=
  have : Flat (j.toImage ≫ j.imageι ≫ s) := by simpa
  flat_of_schemeDominant_of_isDedekindDomain j.toImage _
theorem flat_image_of_over_fractionField {O K : Type u} [CommRing O] [IsDedekindDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K] (s : P ⟶ Spec (.of O)) (s' : W ⟶ Spec (.of K))
    (h : s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = j ≫ s) [QuasiCompact j] :
    Flat (j.imageι ≫ s) :=
  have := flat_of_over_fractionField (j ≫ s) s' h
  flat_image_of_isDedekindDomain j s
def closureMap {W' P' : Scheme.{u}} (j' : W' ⟶ P') (w : W ⟶ W') (g : P ⟶ P')
    (h : j ≫ g = w ≫ j') : j.image ⟶ j'.image :=
  closureLift j' (j.imageι ≫ g) j.toImage w (by simpa using h)
@[reassoc (attr := simp)]
theorem closureMap_imageι {W' P' : Scheme.{u}} (j' : W' ⟶ P') (w : W ⟶ W') (g : P ⟶ P')
    (h : j ≫ g = w ≫ j') : closureMap j j' w g h ≫ j'.imageι = j.imageι ≫ g :=
  closureLift_imageι _ _ _ _ _
@[reassoc (attr := simp)]
theorem toImage_closureMap {W' P' : Scheme.{u}} (j' : W' ⟶ P') (w : W ⟶ W') (g : P ⟶ P')
    (h : j ≫ g = w ≫ j') : j.toImage ≫ closureMap j j' w g h = w ≫ j'.toImage :=
  comp_closureLift _ _ _ _ _
@[simp]
theorem closureMap_id : closureMap j j (𝟙 W) (𝟙 P) (by simp) = 𝟙 _ :=
  closure_hom_ext j (by simp)
@[reassoc (attr := simp)]
theorem closureMap_comp {W' P' W'' P'' : Scheme.{u}} (j' : W' ⟶ P') (j'' : W'' ⟶ P'')
    (w : W ⟶ W') (g : P ⟶ P') (h : j ≫ g = w ≫ j') (w' : W' ⟶ W'') (g' : P' ⟶ P'')
    (h' : j' ≫ g' = w' ≫ j'') :
    closureMap j j' w g h ≫ closureMap j' j'' w' g' h' =
      closureMap j j'' (w ≫ w') (g ≫ g') (by rw [reassoc_of% h, h', Category.assoc]) :=
  closure_hom_ext j'' (by simp)
theorem ker_eq_comap_of_flat {W' P' : Scheme.{u}} {j' : W' ⟶ P'} {w : W' ⟶ W} {g : P' ⟶ P}
    (H : IsPullback j' w g j) [Flat g] [QuasiCompact j] : j'.ker = j.ker.comap g := by
  let e : W' ⟶ pullback g j.imageι := pullback.lift j' (w ≫ j.toImage) (by simpa using H.w)
  have he : e ≫ pullback.fst g j.imageι = j' := pullback.lift_fst _ _ _
  have He : IsPullback w e j.toImage (pullback.snd g j.imageι) := by
    refine (IsPullback.of_right (h₁₂ := pullback.fst g j.imageι) (h₂₂ := j.imageι) (v₁₃ := g)
      ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g j.imageι)).flip
    rwa [he, j.toImage_imageι]
  have := IsSchemeTheoreticallyDominant.of_isPullback He
  rw [Scheme.IdealSheafData.comap, ← ker_comp_of_schemeDominant e, he]
theorem isPullback_toImage_of_isClosedImmersion {P' : Scheme.{u}} (c : W ⟶ P') (u : P' ⟶ P)
    [IsClosedImmersion c] [Flat u] [Mono u] (h : c ≫ u = j) [QuasiCompact j] :
    IsPullback c j.toImage u j.imageι := by
  have H : IsPullback c (𝟙 W) u j := by
    refine IsPullback.of_isLimit' ⟨by simpa using h⟩ (PullbackCone.IsLimit.mk _ (fun s ↦ s.snd)
      (fun s ↦ ?_) (fun s ↦ by simp) (fun s m _ h₂ ↦ by simpa using h₂))
    rw [← cancel_mono u, Category.assoc, h, s.condition]
  exact isPullback_of_isClosedImmersion _ _ _ _ (by simpa using h)
    (by simp [ker_eq_comap_of_flat j H])
def closureRestrictIso (P' : P.Opens) (c : W ⟶ P') [IsClosedImmersion c] (h : c ≫ P'.ι = j)
    [QuasiCompact j] : W ≅ (j.imageι ⁻¹ᵁ P' : j.image.Opens) :=
  (isPullback_toImage_of_isClosedImmersion j c P'.ι h).isoIsPullback _ _
    (isPullback_morphismRestrict j.imageι P')
@[reassoc (attr := simp)]
theorem closureRestrictIso_hom_ι (P' : P.Opens) (c : W ⟶ P') [IsClosedImmersion c]
    (h : c ≫ P'.ι = j) [QuasiCompact j] :
    (closureRestrictIso j P' c h).hom ≫ (j.imageι ⁻¹ᵁ P').ι = j.toImage :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _
@[reassoc (attr := simp)]
theorem closureRestrictIso_hom_restrict (P' : P.Opens) (c : W ⟶ P') [IsClosedImmersion c]
    (h : c ≫ P'.ι = j) [QuasiCompact j] :
    (closureRestrictIso j P' c h).hom ≫ j.imageι ∣_ P' = c :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _
def closureSpecIso {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (Spec.map φ).image ≅ Spec (.of (A ⧸ RingHom.ker φ.hom)) :=
  have := (schemeDominant_specMap_iff (CommRingCat.ofHom φ.hom.kerLift)).mpr
    φ.hom.kerLift_injective
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) Ideal.Quotient.mk_surjective
  asIso (closureToClosed (Spec.map φ) (Spec.map (CommRingCat.ofHom φ.hom.kerLift))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))))
    (by rw [← Spec.map_comp]; rfl))
@[reassoc (attr := simp)]
theorem closureSpecIso_hom_comp {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (closureSpecIso φ).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) =
      (Spec.map φ).imageι :=
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) Ideal.Quotient.mk_surjective
  closureToClosed_comp (Spec.map φ) (Spec.map (CommRingCat.ofHom φ.hom.kerLift)) _
    (by rw [← Spec.map_comp]; rfl)
end Closure
section Graph
variable {S Z₁ Z₂ U T T' : Scheme.{u}} (f₁ : Z₁ ⟶ S) (f₂ : Z₂ ⟶ S) (u : U ⟶ Z₁) (φ : U ⟶ Z₂)
  (h : u ≫ f₁ = φ ≫ f₂)
def graphMap : U ⟶ pullback f₁ f₂ := pullback.lift u φ h
@[reassoc (attr := simp)]
theorem graphMap_fst : graphMap f₁ f₂ u φ h ≫ pullback.fst f₁ f₂ = u := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem graphMap_snd : graphMap f₁ f₂ u φ h ≫ pullback.snd f₁ f₂ = φ := pullback.lift_snd _ _ _
instance isImmersion_graphMap [IsImmersion u] : IsImmersion (graphMap f₁ f₂ u φ h) :=
  have : IsImmersion (graphMap f₁ f₂ u φ h ≫ pullback.fst f₁ f₂) := by simpa
  IsImmersion.of_comp _ (pullback.fst f₁ f₂)
instance quasiCompact_graphMap [QuasiCompact u] [QuasiSeparated f₂] :
    QuasiCompact (graphMap f₁ f₂ u φ h) :=
  have : QuasiCompact (graphMap f₁ f₂ u φ h ≫ pullback.fst f₁ f₂) := by simpa
  QuasiCompact.of_comp _ (pullback.fst f₁ f₂)
def graphClosure : Scheme.{u} := (graphMap f₁ f₂ u φ h).image
namespace graphClosure
def ι : graphClosure f₁ f₂ u φ h ⟶ pullback f₁ f₂ := (graphMap f₁ f₂ u φ h).imageι
def incl : U ⟶ graphClosure f₁ f₂ u φ h := (graphMap f₁ f₂ u φ h).toImage
def fst : graphClosure f₁ f₂ u φ h ⟶ Z₁ := ι f₁ f₂ u φ h ≫ pullback.fst f₁ f₂
def snd : graphClosure f₁ f₂ u φ h ⟶ Z₂ := ι f₁ f₂ u φ h ≫ pullback.snd f₁ f₂
@[reassoc (attr := simp)]
theorem ι_fst : ι f₁ f₂ u φ h ≫ pullback.fst f₁ f₂ = fst f₁ f₂ u φ h := rfl
@[reassoc (attr := simp)]
theorem ι_snd : ι f₁ f₂ u φ h ≫ pullback.snd f₁ f₂ = snd f₁ f₂ u φ h := rfl
@[reassoc (attr := simp)]
theorem incl_ι : incl f₁ f₂ u φ h ≫ ι f₁ f₂ u φ h = graphMap f₁ f₂ u φ h :=
  (graphMap f₁ f₂ u φ h).toImage_imageι
@[reassoc (attr := simp)]
theorem incl_fst : incl f₁ f₂ u φ h ≫ fst f₁ f₂ u φ h = u := by
  rw [← ι_fst, incl_ι_assoc, graphMap_fst]
@[reassoc (attr := simp)]
theorem incl_snd : incl f₁ f₂ u φ h ≫ snd f₁ f₂ u φ h = φ := by
  rw [← ι_snd, incl_ι_assoc, graphMap_snd]
@[reassoc]
theorem condition : fst f₁ f₂ u φ h ≫ f₁ = snd f₁ f₂ u φ h ≫ f₂ := by
  rw [← ι_fst, ← ι_snd, Category.assoc, Category.assoc, pullback.condition]
instance isClosedImmersion_ι : IsClosedImmersion (ι f₁ f₂ u φ h) :=
  inferInstanceAs (IsClosedImmersion (graphMap f₁ f₂ u φ h).imageι)
instance schemeDominant_incl : IsSchemeTheoreticallyDominant (incl f₁ f₂ u φ h) :=
  schemeDominant_toImage (graphMap f₁ f₂ u φ h)
instance quasiCompact_incl [QuasiCompact u] [QuasiSeparated f₂] :
    QuasiCompact (incl f₁ f₂ u φ h) :=
  inferInstanceAs (QuasiCompact (graphMap f₁ f₂ u φ h).toImage)
instance isOpenImmersion_incl [IsImmersion u] [QuasiCompact u] [QuasiSeparated f₂] :
    IsOpenImmersion (incl f₁ f₂ u φ h) :=
  isOpenImmersion_toImage (graphMap f₁ f₂ u φ h)
theorem range_ι [QuasiCompact u] [QuasiSeparated f₂] :
    Set.range (ι f₁ f₂ u φ h) = closure (Set.range (graphMap f₁ f₂ u φ h)) :=
  range_imageι (graphMap f₁ f₂ u φ h)
instance isReduced [QuasiCompact u] [QuasiSeparated f₂] [IsReduced U] :
    IsReduced (graphClosure f₁ f₂ u φ h) :=
  isReduced_image (graphMap f₁ f₂ u φ h)
instance isIntegral [QuasiCompact u] [QuasiSeparated f₂] [IsIntegral U] :
    IsIntegral (graphClosure f₁ f₂ u φ h) :=
  isIntegral_image (graphMap f₁ f₂ u φ h)
theorem hom_ext {a b : T ⟶ graphClosure f₁ f₂ u φ h}
    (h₁ : a ≫ fst f₁ f₂ u φ h = b ≫ fst f₁ f₂ u φ h)
    (h₂ : a ≫ snd f₁ f₂ u φ h = b ≫ snd f₁ f₂ u φ h) : a = b := by
  rw [← cancel_mono (ι f₁ f₂ u φ h)]
  apply pullback.hom_ext <;> simpa
def lift (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂) (ht : t₁ ≫ f₁ = t₂ ≫ f₂) (d : T' ⟶ T)
    [IsSchemeTheoreticallyDominant d] (w : T' ⟶ U) (h₁ : d ≫ t₁ = w ≫ u) (h₂ : d ≫ t₂ = w ≫ φ) :
    T ⟶ graphClosure f₁ f₂ u φ h :=
  closureLift (graphMap f₁ f₂ u φ h) (pullback.lift t₁ t₂ ht) d w (by
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd, h₁, h₂])
section
variable (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂) (ht : t₁ ≫ f₁ = t₂ ≫ f₂) (d : T' ⟶ T)
  [IsSchemeTheoreticallyDominant d] (w : T' ⟶ U) (h₁ : d ≫ t₁ = w ≫ u) (h₂ : d ≫ t₂ = w ≫ φ)
@[reassoc (attr := simp)]
theorem lift_ι : lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ ≫ ι f₁ f₂ u φ h = pullback.lift t₁ t₂ ht :=
  closureLift_imageι _ _ _ _ _
@[reassoc (attr := simp)]
theorem lift_fst : lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ ≫ fst f₁ f₂ u φ h = t₁ := by
  rw [← ι_fst, lift_ι_assoc, pullback.lift_fst]
@[reassoc (attr := simp)]
theorem lift_snd : lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ ≫ snd f₁ f₂ u φ h = t₂ := by
  rw [← ι_snd, lift_ι_assoc, pullback.lift_snd]
@[reassoc (attr := simp)]
theorem comp_lift : d ≫ lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ = w ≫ incl f₁ f₂ u φ h :=
  comp_closureLift _ _ _ _ _
end
instance isProper_fst [IsProper f₂] : IsProper (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance
instance isProper_snd [IsProper f₁] : IsProper (snd f₁ f₂ u φ h) := by
  rw [← ι_snd]; infer_instance
instance isSeparated_fst [IsSeparated f₂] : IsSeparated (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance
instance isSeparated_snd [IsSeparated f₁] : IsSeparated (snd f₁ f₂ u φ h) := by
  rw [← ι_snd]; infer_instance
instance locallyOfFiniteType_fst [LocallyOfFiniteType f₂] :
    LocallyOfFiniteType (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance
instance quasiCompact_fst [QuasiCompact f₂] : QuasiCompact (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance
instance schemeDominant_fst [IsSchemeTheoreticallyDominant u] :
    IsSchemeTheoreticallyDominant (fst f₁ f₂ u φ h) :=
  have : IsSchemeTheoreticallyDominant (incl f₁ f₂ u φ h ≫ fst f₁ f₂ u φ h) := by simpa
  schemeDominant_of_comp (incl f₁ f₂ u φ h) _
instance isDominant_fst [IsDominant u] : IsDominant (fst f₁ f₂ u φ h) :=
  have : IsDominant (incl f₁ f₂ u φ h ≫ fst f₁ f₂ u φ h) := by simpa
  IsDominant.of_comp (incl f₁ f₂ u φ h) _
instance surjective_fst [IsDominant u] [IsProper f₂] : Surjective (fst f₁ f₂ u φ h) :=
  surjective_of_isDominant_of_isClosed_range _ (fst f₁ f₂ u φ h).isClosedMap.isClosed_range
theorem isPullback_incl [Flat u] [Mono u] [QuasiCompact u] [IsSeparated f₂] :
    IsPullback (𝟙 U) (incl f₁ f₂ u φ h) u (fst f₁ f₂ u φ h) := by
  let u' : pullback (u ≫ f₁) f₂ ⟶ pullback f₁ f₂ :=
    pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by simpa using pullback.condition)
  have hu₁ : u' ≫ pullback.fst f₁ f₂ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _
  have hu₂ : u' ≫ pullback.snd f₁ f₂ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have Hu : IsPullback (pullback.fst (u ≫ f₁) f₂) u' u (pullback.fst f₁ f₂) := by
    refine IsPullback.of_bot (h₃₁ := f₂) (v₂₁ := pullback.snd f₁ f₂) (v₂₂ := f₁) ?_ hu₁.symm
      (IsPullback.of_hasPullback f₁ f₂)
    rw [hu₂]
    exact IsPullback.of_hasPullback _ _
  have : Flat u' := MorphismProperty.of_isPullback Hu ‹_›
  have : Mono u' := (MorphismProperty.monomorphisms _).of_isPullback Hu.flip.flip ‹Mono u›
  let c : U ⟶ pullback (u ≫ f₁) f₂ := pullback.lift (𝟙 U) φ (by simpa using h)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = φ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have hc : c ≫ u' = graphMap f₁ f₂ u φ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu₁, reassoc_of% hc₁, graphMap_fst]
    · rw [Category.assoc, hu₂, hc₂, graphMap_snd]
  have H := (isPullback_toImage_of_isClosedImmersion _ c u' hc).paste_horiz Hu
  rw [hc₁] at H
  exact H
theorem isIso_fst_restrict_of_le [IsOpenImmersion u] [QuasiCompact u] [IsSeparated f₂]
    (V : Z₁.Opens) (hV : V ≤ u.opensRange) : IsIso (fst f₁ f₂ u φ h ∣_ V) := by
  let l : (V : Scheme.{u}) ⟶ U := IsOpenImmersion.lift u V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
  have hl : l ≫ u = V.ι := IsOpenImmersion.lift_fac _ _ _
  have H := (IsPullback.id_horiz l).paste_vert (isPullback_incl f₁ f₂ u φ h)
  rw [hl] at H
  have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict (fst f₁ f₂ u φ h) V) H
  rw [← e]
  infer_instance
instance isIso_fst_restrict [IsOpenImmersion u] [QuasiCompact u] [IsSeparated f₂] :
    IsIso (fst f₁ f₂ u φ h ∣_ u.opensRange) :=
  isIso_fst_restrict_of_le f₁ f₂ u φ h _ le_rfl
instance isIso_fst_restrict_opens (V : Z₁.Opens) (ψ : (V : Scheme.{u}) ⟶ Z₂)
    (hψ : V.ι ≫ f₁ = ψ ≫ f₂) [QuasiCompact V.ι] [IsSeparated f₂] :
    IsIso (fst f₁ f₂ V.ι ψ hψ ∣_ V) :=
  isIso_fst_restrict_of_le f₁ f₂ V.ι ψ hψ V (by simp)
end graphClosure
end Graph
section Examples
example : IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))).imageι :=
  (isIso_imageι_iff _).mpr ((schemeDominant_specMap_iff _).mpr (algebraMap ℤ ℚ).injective_int)
example :
    let j := Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := ℤ) (1 / 2 : ℚ)).toRingHom)
    Flat (j.imageι ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)))) ∧
      IsIntegral j.image ∧ ¬ IsIso j.imageι := by
  intro j
  refine ⟨flat_image_of_over_fractionField (K := ℚ) j _ (𝟙 _)
    (specZIsTerminal.hom_ext _ _), inferInstance, ?_⟩
  rw [isIso_imageι_iff, schemeDominant_specMap_iff]
  intro hinj
  have h0 : (2 * Polynomial.X - 1 : Polynomial ℤ) = 0 := by
    apply hinj
    simp [map_ofNat]
  simpa using congrArg (Polynomial.eval 0) h0
namespace GraphClosureExample
abbrev awayTwo : Type := Localization.Away (2 : ℤ√(-4))
def halfRoot : ℤ√(-1) →+* awayTwo :=
  Zsqrtd.lift ⟨algebraMap _ awayTwo (Zsqrtd.sqrtd : ℤ√(-4)) *
      IsLocalization.Away.invSelf (2 : ℤ√(-4)), by
    have h₁ := IsLocalization.Away.mul_invSelf (S := awayTwo) (2 : ℤ√(-4))
    have h₂ : algebraMap _ awayTwo (Zsqrtd.sqrtd : ℤ√(-4)) *
        algebraMap _ awayTwo (Zsqrtd.sqrtd : ℤ√(-4)) = -4 := by
      rw [← map_mul, Zsqrtd.dmuld]; simp [map_ofNat]
    rw [map_ofNat] at h₁
    push_cast
    linear_combination (IsLocalization.Away.invSelf (S := awayTwo) (2 : ℤ√(-4))) ^ 2 * h₂ -
      (2 * IsLocalization.Away.invSelf (S := awayTwo) (2 : ℤ√(-4)) + 1) * h₁⟩
abbrev str (d : ℤ) : Spec (.of (ℤ√d)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (ℤ√d)))
abbrev openPart : Spec (.of awayTwo) ⟶ Spec (.of (ℤ√(-4))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ℤ√(-4)) awayTwo))
abbrev partialMap : Spec (.of awayTwo) ⟶ Spec (.of (ℤ√(-1))) :=
  Spec.map (CommRingCat.ofHom halfRoot)
theorem comm : openPart ≫ str (-4) = partialMap ≫ str (-1) := specZIsTerminal.hom_ext _ _
example : Set.range (graphClosure.fst (𝟙 _) openPart openPart (𝟙 _) (by simp)) =
    Set.range openPart := by
  apply subset_antisymm
  · rw [← Category.comp_id (graphClosure.fst _ _ _ _ _), graphClosure.condition,
      Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · rintro _ ⟨x, rfl⟩
    exact ⟨graphClosure.incl (𝟙 _) openPart openPart (𝟙 _) (by simp) x, by
      rw [← Scheme.Hom.comp_apply, graphClosure.incl_fst]⟩
end GraphClosureExample
end Examples
end
end GlobalTheory


