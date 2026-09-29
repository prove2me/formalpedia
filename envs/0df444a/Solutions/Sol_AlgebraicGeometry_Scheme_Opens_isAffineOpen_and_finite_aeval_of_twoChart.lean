-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ead59545-1098-5e28-8d4e-c79757713508

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart.AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsLocallyNoetherian IsOpenImmersion.lift Scheme.Opens.topIso_inv Scheme.Opens.toScheme_presheaf_map HasAffineProperty SmoothOfRelativeDimension IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.resLE_appLE GeometricallyIntegral Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp IsProper.eq_valuativeCriterion Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyQuasiFinite IsFinite isAffine_of_isAffineHom IsSeparated.of_comp QuasiCompact Scheme.Pullback.range_fst IsAffine LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.Hom.map_appLE_assoc Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.Hom.appTop Scheme.toSpecΓ_appTop Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.topIso_hom Spec.map_base Scheme.Opens.ι_app_self germ_injective_of_isIntegral ValuativeCriterion.iff HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Spec.map_injective IsSeparated.valuativeCriterion locallyOfFiniteType_of_comp IsSeparated IsFinite.iff_isProper_and_isAffineHom Scheme.Spec_stalkClosedPointTo_fromSpecStalk toSpecΓ_SpecMap_ΓSpecIso_inv IsFinite.SpecMap_iff IsProper.of_valuativeCriterion IsAffineOpen IsNoetherian Scheme.Opens ValuativeCriterion.Existence Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE ValuativeCriterion Scheme.ΓSpecIso_naturality IsAffineHom Scheme.Opens.ι_appTop IsOpenImmersion.lift_fac IsFinite.of_isProper_of_locallyQuasiFinite Scheme.germ_stalkClosedPointTo toSpecΓ Scheme.Hom.appLE geometrically Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.isIntegral_pullback_Spec_field Scheme.Opens.finite_preimage_singleton_toSpecPolynomial"
p2m_open "AlgebraicGeometry"

variable {k : Type u} [CommRing k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι mem_basicOpen Opens.topIso_inv Opens.toScheme_presheaf_map germToFunctionField fromSpecStalk Opens.range_ι Hom Hom.resLE_appLE Γ Hom.germ_stalkMap_apply empty stalkClosedPointTo_comp topIso_hom SpecMap_stalkSpecializes_fromSpecStalk Pullback.range_fst topIso toSpecΓ_naturality Hom.map_appLE_assoc ΓSpecIso_inv_naturality Hom.appTop functionField toSpecΓ_appTop stalkClosedPointTo Opens.topIso_hom Opens.ι_app_self basicOpen Spec_stalkClosedPointTo_fromSpecStalk Opens Hom.appLE_map Hom.app_eq_appLE ΓSpecIso_naturality Opens.ι_appTop germ_stalkClosedPointTo Hom.appLE ΓSpecIso toSpecΓ Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom Opens.finite_preimage_singleton_toSpecPolynomial" namespace Opens p2m_export "AlgebraicGeometry.Scheme.Opens" "topIso_inv toScheme_presheaf_map toSpecΓ range_ι toSpecΓ_naturality toSpecΓ_appTop topIso_hom ι_app_self topIso ι ι_appTop ι_preimage_self finite_preimage_singleton_toSpecPolynomial" end Scheme.Opens
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

noncomputable abbrev Scheme.Opens.baseRingHom (U : C.Opens) : k →+* Γ((U : Scheme.{u}), ⊤) :=
  (U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

noncomputable abbrev Scheme.Opens.toSpecPolynomial (U : C.Opens) (s : Γ(C, U)) :
    (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
  (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s)))

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.toSpecPolynomial_comp_C (U : C.Opens) (s : Γ(C, U)) :
    Scheme.Opens.toSpecPolynomial c U s ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) =
      U.ι ≫ c := by
  simp only [Scheme.Opens.toSpecPolynomial, Category.assoc, ← Spec.map_comp]
  have h1 : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫ CommRingCat.ofHom
      (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ c).appTop := by
    ext a
    simp [Scheme.Opens.baseRingHom]
  refine (congrArg (fun m => (U : Scheme.{u}).toSpecΓ ≫ Spec.map m) h1).trans ?_
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

section general

open IsLocalRing

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι mem_basicOpen Opens.topIso_inv Opens.toScheme_presheaf_map germToFunctionField fromSpecStalk Opens.range_ι Hom Hom.resLE_appLE Γ Hom.germ_stalkMap_apply empty stalkClosedPointTo_comp topIso_hom SpecMap_stalkSpecializes_fromSpecStalk Pullback.range_fst topIso toSpecΓ_naturality Hom.map_appLE_assoc ΓSpecIso_inv_naturality Hom.appTop functionField toSpecΓ_appTop stalkClosedPointTo Opens.topIso_hom Opens.ι_app_self basicOpen Spec_stalkClosedPointTo_fromSpecStalk Opens Hom.appLE_map Hom.app_eq_appLE ΓSpecIso_naturality Opens.ι_appTop germ_stalkClosedPointTo Hom.appLE ΓSpecIso toSpecΓ Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom Opens.finite_preimage_singleton_toSpecPolynomial" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.comp_appTop' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop := rfl

p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.stalkClosedPointTo_germ_top {Y : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    (f : Spec R ⟶ Y) (t : Γ(Y, ⊤)) :
    (Scheme.stalkClosedPointTo f).hom (Y.presheaf.germ ⊤ (f.base (closedPoint R)) trivial t) =
      (Scheme.ΓSpecIso R).hom (f.appTop t) := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo f ⊤ trivial]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.comp_apply, TopologicalSpace.Opens.map_top, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.ι_app_self_apply {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, U)) :
    U.ι.app U s = (U : Scheme.{u}).presheaf.map (eqToHom U.ι_preimage_self).op (U.topIso.inv s) := by
  simp only [Scheme.Opens.ι_app_self, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
  erw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

end general

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.toSpecPolynomial_appTop_X (U : C.Opens) (s : Γ(C, U)) :
    (Scheme.Opens.toSpecPolynomial c U s).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X) = U.topIso.inv s := by
  have h := congrArg (fun φ => φ.hom X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h
  simp only [Scheme.Opens.toSpecPolynomial, Scheme.comp_appTop', Scheme.toSpecΓ_appTop,
    CommRingCat.comp_apply]
  erw [← h]
  exact CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(U, ⊤)) _

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.ΓSpecIso_appTop_topIso_inv_eq (U : C.Opens) (s : Γ(C, U))
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {i₁ : Spec (.of K) ⟶ (U : Scheme.{u})} {i₂ : Spec (.of R) ⟶ Spec (.of k[X])}
    (w : i₁ ≫ Scheme.Opens.toSpecPolynomial c U s =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) :
    (Scheme.ΓSpecIso (.of K)).hom (i₁.appTop (U.topIso.inv s)) =
      algebraMap R K ((Scheme.ΓSpecIso (.of R)).hom
        (i₂.appTop ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X))) := by
  have h1 : i₁.appTop ((Scheme.Opens.toSpecPolynomial c U s).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X)) =
      (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop
        (i₂.appTop ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.comp_appTop', w]
    rfl
  rw [Scheme.Opens.toSpecPolynomial_appTop_X] at h1
  rw [h1, ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (.of K)).hom, Scheme.ΓSpecIso_naturality,
    CommRingCat.comp_apply]
  rfl

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in
set_option maxHeartbeats 1600000 in
open IsLocalRing in

theorem Scheme.Opens.valuativeCriterion_existence_toSpecPolynomial_of_twoChart
    [IsProper c] (U V W : C.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hUVW : ∀ x : C, x ∈ U → x ∈ V → x ∈ W)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : W = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE hWU).op).hom f *
      (C.presheaf.map (homOfLE hWV).op).hom g = 1) :
    ValuativeCriterion.Existence (Scheme.Opens.toSpecPolynomial c U f) := by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  haveI : IsDomain (CommRingCat.of R) := ‹_›
  haveI : ValuationRing (CommRingCat.of R) := ‹_›
  letI : Field (CommRingCat.of K) := ‹_›
  set φ := Scheme.Opens.toSpecPolynomial c U f with hφ
  set πC := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) with hπC
  set α := Spec.map (CommRingCat.ofHom (algebraMap R K)) with hα

  have hvc : ValuativeCriterion c := by
    have h : IsProper c := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have w' : (i₁ ≫ U.ι) ≫ c = α ≫ (i₂ ≫ πC) := by
    rw [Category.assoc, ← Scheme.Opens.toSpecPolynomial_comp_C c U f, ← hφ, reassoc_of% w]
  obtain ⟨ℓ, hl₁, hl₂⟩ := (hvc.existence ⟨R, K, i₁ ≫ U.ι, i₂ ≫ πC, ⟨w'⟩⟩).exists_lift
  dsimp only at hl₁ hl₂
  set x₁ := ℓ.base (closedPoint R) with hx₁
  have hp₀U : (i₁ ≫ U.ι).base (closedPoint K) ∈ U := (i₁.base (closedPoint K)).2
  have h01 : (i₁ ≫ U.ι).base (closedPoint K) ⤳ x₁ := by
    rw [← hl₁]
    exact (specializes_closedPoint _).map ℓ.continuous

  have hF1 : Scheme.stalkClosedPointTo ℓ ≫ CommRingCat.ofHom (algebraMap R K) =
      C.presheaf.stalkSpecializes h01 ≫ Scheme.stalkClosedPointTo (i₁ ≫ U.ι) := by
    apply Spec.map_injective
    rw [← cancel_mono (C.fromSpecStalk x₁), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

  set r₀ : R := (Scheme.ΓSpecIso (.of R)).hom
    (i₂.appTop ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X)) with hr₀
  have hF3 : (Scheme.stalkClosedPointTo (i₁ ≫ U.ι)).hom (C.presheaf.germ U _ hp₀U f) =
      algebraMap R K r₀ := by
    rw [hr₀, ← Scheme.Opens.ΓSpecIso_appTop_topIso_inv_eq c U f w, Scheme.stalkClosedPointTo_comp]
    show (Scheme.stalkClosedPointTo i₁).hom ((U.ι.stalkMap (i₁.base (closedPoint K))).hom
      (C.presheaf.germ U (U.ι.base (i₁.base (closedPoint K))) hp₀U f)) = _
    rw [Scheme.Hom.germ_stalkMap_apply U.ι U (i₁.base (closedPoint K)) hp₀U f]
    rw [Scheme.Opens.ι_app_self_apply, TopCat.Presheaf.germ_res_apply,
      Scheme.stalkClosedPointTo_germ_top]

  have hx₁U : x₁ ∈ U := by
    have hx₁UV : x₁ ∈ U ⊔ V := by rw [hcov]; trivial
    rcases (TopologicalSpace.Opens.mem_sup.mp hx₁UV) with h | hx₁V
    · exact h

    have hgerm : IsUnit (C.presheaf.germ V x₁ hx₁V g) := by
      apply isUnit_of_map_unit (Scheme.stalkClosedPointTo ℓ).hom _
      refine isUnit_iff_exists_inv.mpr ⟨r₀, ?_⟩
      apply IsFractionRing.injective R K
      rw [map_mul, map_one]
      have e1 : algebraMap R K ((Scheme.stalkClosedPointTo ℓ).hom (C.presheaf.germ V x₁ hx₁V g)) =
          (Scheme.stalkClosedPointTo (i₁ ≫ U.ι)).hom
            (C.presheaf.stalkSpecializes h01 (C.presheaf.germ V x₁ hx₁V g)) := by
        have := congrArg (fun φ => φ.hom (C.presheaf.germ V x₁ hx₁V g)) hF1
        simp at this
        exact this

      have hp₀V : (i₁ ≫ U.ι).base (closedPoint K) ∈ V := h01.mem_open V.isOpen hx₁V
      have e2 : C.presheaf.stalkSpecializes h01 (C.presheaf.germ V x₁ hx₁V g) =
          C.presheaf.germ V _ hp₀V g := TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
      have e3 : C.presheaf.germ U _ hp₀U f * C.presheaf.germ V _ hp₀V g = 1 := by
        have hp₀UV : (i₁ ≫ U.ι).base (closedPoint K) ∈ W := hUVW _ hp₀U hp₀V
        rw [← TopCat.Presheaf.germ_res C.presheaf (homOfLE hWU) _ hp₀UV,
          ← TopCat.Presheaf.germ_res C.presheaf (homOfLE hWV) _ hp₀UV]
        simp only [CommRingCat.comp_apply]
        rw [← map_mul, hfg, map_one]
      rw [e1, e2, ← hF3, ← map_mul, mul_comm, e3, map_one]

    have : x₁ ∈ C.basicOpen g := (C.mem_basicOpen g x₁ hx₁V).mpr hgerm
    rw [← hUV] at this
    exact hWU this

  have hrange : Set.range ℓ.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ((specializes_closedPoint y).map ℓ.continuous).mem_open U.isOpen hx₁U
  have hl : IsOpenImmersion.lift U.ι ℓ hrange ≫ U.ι = ℓ := IsOpenImmersion.lift_fac _ _ _
  have h1 : α ≫ IsOpenImmersion.lift U.ι ℓ hrange = i₁ := by
    rw [← cancel_mono U.ι, Category.assoc, hl, hl₁]
  refine ⟨⟨⟨IsOpenImmersion.lift U.ι ℓ hrange, h1, ?_⟩⟩⟩
  have key : α ≫ (IsOpenImmersion.lift U.ι ℓ hrange ≫ φ) = α ≫ i₂ := by
    rw [← Category.assoc, h1, w]
  generalize IsOpenImmersion.lift U.ι ℓ hrange ≫ φ = m at key ⊢
  obtain ⟨m, rfl⟩ := Spec.map_surjective m
  obtain ⟨n, rfl⟩ := Spec.map_surjective i₂
  rw [hα, ← Spec.map_comp, ← Spec.map_comp] at key
  have key' := Spec.map_injective key
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
  apply IsFractionRing.injective R K
  have := congrArg (fun g => g.hom p) key'
  simpa using this

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.isProper_toSpecPolynomial_of_twoChart
    [IsProper c] (U V W : C.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hUVW : ∀ x : C, x ∈ U → x ∈ V → x ∈ W)
    (hU : IsAffineOpen U) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : W = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE hWU).op).hom f *
      (C.presheaf.map (homOfLE hWV).op).hom g = 1) :
    IsProper (Scheme.Opens.toSpecPolynomial c U f) := by
  set φ := Scheme.Opens.toSpecPolynomial c U f with hφ
  have htri := Scheme.Opens.toSpecPolynomial_comp_C c U f
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI : QuasiCompact φ := inferInstance
  haveI : LocallyOfFiniteType (φ ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    rw [hφ, htri]; infer_instance
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
  haveI : IsSeparated φ := inferInstance
  refine IsProper.of_valuativeCriterion φ (ValuativeCriterion.iff.mpr ⟨?_, IsSeparated.valuativeCriterion φ⟩)
  exact Scheme.Opens.valuativeCriterion_existence_toSpecPolynomial_of_twoChart c U V W hWU hWV hUVW f g
    hcov hUV hfg

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.finite_eval₂RingHom_of_twoChart
    [IsProper c] (U V W : C.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hUVW : ∀ x : C, x ∈ U → x ∈ V → x ∈ W)
    (hU : IsAffineOpen U) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : W = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE hWU).op).hom f *
      (C.presheaf.map (homOfLE hWV).op).hom g = 1) :
    (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv f)).Finite := by
  haveI := Scheme.Opens.isProper_toSpecPolynomial_of_twoChart c U V W hWU hWV hUVW hU f g hcov hUV hfg
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI : IsAffineHom (Scheme.Opens.toSpecPolynomial c U f) := inferInstance
  have hfin : IsFinite (Scheme.Opens.toSpecPolynomial c U f) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

  have hfin' : IsFinite (Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv f)))) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsFinite (U : Scheme.{u}).toSpecΓ _).mp hfin
  exact (IsFinite.SpecMap_iff _).mp hfin'

end AlgebraicGeometry

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsLocallyNoetherian IsOpenImmersion.lift Scheme.Opens.topIso_inv Scheme.Opens.toScheme_presheaf_map HasAffineProperty SmoothOfRelativeDimension IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.resLE_appLE GeometricallyIntegral Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp IsProper.eq_valuativeCriterion Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyQuasiFinite IsFinite isAffine_of_isAffineHom IsSeparated.of_comp QuasiCompact Scheme.Pullback.range_fst IsAffine LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.Hom.map_appLE_assoc Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.Hom.appTop Scheme.toSpecΓ_appTop Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.topIso_hom Spec.map_base Scheme.Opens.ι_app_self germ_injective_of_isIntegral ValuativeCriterion.iff HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Spec.map_injective IsSeparated.valuativeCriterion locallyOfFiniteType_of_comp IsSeparated IsFinite.iff_isProper_and_isAffineHom Scheme.Spec_stalkClosedPointTo_fromSpecStalk toSpecΓ_SpecMap_ΓSpecIso_inv IsFinite.SpecMap_iff IsProper.of_valuativeCriterion IsAffineOpen IsNoetherian Scheme.Opens ValuativeCriterion.Existence Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE ValuativeCriterion Scheme.ΓSpecIso_naturality IsAffineHom Scheme.Opens.ι_appTop IsOpenImmersion.lift_fac IsFinite.of_isProper_of_locallyQuasiFinite Scheme.germ_stalkClosedPointTo toSpecΓ Scheme.Hom.appLE geometrically Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.isIntegral_pullback_Spec_field Scheme.Opens.finite_preimage_singleton_toSpecPolynomial"
p2m_open "AlgebraicGeometry"

variable {k : Type u} [CommRing k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.ι_appTop_comp_topIso_hom {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE le_top).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  erw [← Functor.map_comp]
  rfl

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.topIso_hom_comp_baseRingHom (U : C.Opens) :
    U.topIso.hom.hom.comp (Scheme.Opens.baseRingHom c U) =
      (Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap := by
  ext r
  change U.topIso.hom.hom ((U.ι ≫ c).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)) =
    (c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)
  rw [Scheme.comp_appTop', CommRingCat.comp_apply, ← CommRingCat.comp_apply _ U.topIso.hom,
    Scheme.Opens.ι_appTop_comp_topIso_hom, Scheme.Hom.appLE, CommRingCat.comp_apply]
  rfl

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.finite_aeval_of_twoChart
    [IsProper c] (U V W : C.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hUVW : ∀ x : C, x ∈ U → x ∈ V → x ∈ W)
    (hU : IsAffineOpen U) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : W = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE hWU).op).hom f *
      (C.presheaf.map (homOfLE hWV).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : k[X] →ₐ[k] Γ(C, U)).toRingHom.Finite := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have h := Scheme.Opens.finite_eval₂RingHom_of_twoChart c U V W hWU hWV hUVW hU f g hcov hUV hfg
  have hiso : (U.topIso.hom.hom : Γ((U : Scheme.{u}), ⊤) →+* Γ(C, U)).Finite :=
    RingHom.Finite.of_surjective _ (fun y => ⟨U.topIso.inv.hom y, by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl⟩)
  have hcomp := hiso.comp h
  convert hcomp using 1
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · change (Polynomial.aeval f : k[X] →ₐ[k] Γ(C, U)) (Polynomial.C r) = _
    rw [Polynomial.aeval_C, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      ← RingHom.comp_apply, Scheme.Opens.topIso_hom_comp_baseRingHom]
  · change (Polynomial.aeval f : k[X] →ₐ[k] Γ(C, U)) Polynomial.X = _
    rw [Polynomial.aeval_X, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      ← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl

end AlgebraicGeometry

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsLocallyNoetherian IsOpenImmersion.lift Scheme.Opens.topIso_inv Scheme.Opens.toScheme_presheaf_map HasAffineProperty SmoothOfRelativeDimension IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.resLE_appLE GeometricallyIntegral Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp IsProper.eq_valuativeCriterion Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyQuasiFinite IsFinite isAffine_of_isAffineHom IsSeparated.of_comp QuasiCompact Scheme.Pullback.range_fst IsAffine LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.Hom.map_appLE_assoc Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.Hom.appTop Scheme.toSpecΓ_appTop Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.topIso_hom Spec.map_base Scheme.Opens.ι_app_self germ_injective_of_isIntegral ValuativeCriterion.iff HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Spec.map_injective IsSeparated.valuativeCriterion locallyOfFiniteType_of_comp IsSeparated IsFinite.iff_isProper_and_isAffineHom Scheme.Spec_stalkClosedPointTo_fromSpecStalk toSpecΓ_SpecMap_ΓSpecIso_inv IsFinite.SpecMap_iff IsProper.of_valuativeCriterion IsAffineOpen IsNoetherian Scheme.Opens ValuativeCriterion.Existence Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE ValuativeCriterion Scheme.ΓSpecIso_naturality IsAffineHom Scheme.Opens.ι_appTop IsOpenImmersion.lift_fac IsFinite.of_isProper_of_locallyQuasiFinite Scheme.germ_stalkClosedPointTo toSpecΓ Scheme.Hom.appLE geometrically Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.isIntegral_pullback_Spec_field Scheme.Opens.finite_preimage_singleton_toSpecPolynomial"
p2m_open "AlgebraicGeometry"

variable {k : Type u} [CommRing k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.isProper_toSpecPolynomial_of_twoChart' [IsNoetherianRing k]
    [IsProper c] (U V W : C.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hUVW : ∀ x : C, x ∈ U → x ∈ V → x ∈ W)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : W = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE hWU).op).hom f *
      (C.presheaf.map (homOfLE hWV).op).hom g = 1) :
    IsProper (Scheme.Opens.toSpecPolynomial c U f) := by
  set φ := Scheme.Opens.toSpecPolynomial c U f with hφ
  have htri := Scheme.Opens.toSpecPolynomial_comp_C c U f
  haveI : CompactSpace C :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := c)).mp inferInstance
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  haveI : IsNoetherian C := ⟨⟩
  haveI : CompactSpace (U : Scheme.{u}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set C))
  haveI : QuasiCompact φ := inferInstance
  haveI : LocallyOfFiniteType (φ ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    rw [hφ, htri]; infer_instance
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
  haveI : IsSeparated (φ ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    rw [hφ, htri]; infer_instance
  haveI : IsSeparated φ := IsSeparated.of_comp φ
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
  refine IsProper.of_valuativeCriterion φ (ValuativeCriterion.iff.mpr ⟨?_, IsSeparated.valuativeCriterion φ⟩)
  exact Scheme.Opens.valuativeCriterion_existence_toSpecPolynomial_of_twoChart c U V W hWU hWV hUVW f g
    hcov hUV hfg

section BaseChangeSquare

variable {k' : Type u} [CommRing k'] (ρ : k →+* k')

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

noncomputable def Scheme.Opens.bcSection (U : C.Opens) (f : Γ(C, U)) :
    Γ(pullback c (Spec.map (CommRingCat.ofHom ρ)), (pullback.fst c (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ U) :=
  ((pullback.fst c (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ U).topIso.hom.hom
    (((pullback.fst c (Spec.map (CommRingCat.ofHom ρ))).resLE U _ le_rfl).appTop.hom (U.topIso.inv.hom f))

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.resLE_toSpecPolynomial (U : C.Opens) (f : Γ(C, U)) :
    (pullback.fst c (Spec.map (CommRingCat.ofHom ρ))).resLE U _ le_rfl ≫
        Scheme.Opens.toSpecPolynomial c U f =
      Scheme.Opens.toSpecPolynomial (pullback.snd c (Spec.map (CommRingCat.ofHom ρ)))
          ((pullback.fst c (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ U) (Scheme.Opens.bcSection c ρ U f) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ρ)) := by
  set ι := pullback.fst c (Spec.map (CommRingCat.ofHom ρ)) with hι
  set c' := pullback.snd c (Spec.map (CommRingCat.ofHom ρ)) with hc'
  set r := ι.resLE U (ι ⁻¹ᵁ U) le_rfl with hr
  have hsq : r ≫ U.ι ≫ c = (ι ⁻¹ᵁ U).ι ≫ c' ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Category.assoc, hr, Scheme.Hom.resLE_comp_ι, Category.assoc, hι, pullback.condition]
  simp only [Scheme.Opens.toSpecPolynomial]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality r, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  suffices key : r.appTop.hom.comp (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv.hom f)) =
      (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c' (ι ⁻¹ᵁ U))
        ((ι ⁻¹ᵁ U).topIso.inv.hom (Scheme.Opens.bcSection c ρ U f))).comp (Polynomial.mapRingHom ρ) by
    congr 2
    apply CommRingCat.hom_ext
    simp [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at key ⊢
    exact key
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  ·
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
    change r.appTop.hom ((U.ι ≫ c).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) =
      ((ι ⁻¹ᵁ U).ι ≫ c').appTop.hom ((Scheme.ΓSpecIso (.of k')).inv.hom (ρ a))
    have hnat : (Scheme.ΓSpecIso (.of k')).inv.hom (ρ a) =
        (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
      have := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact this
    rw [hnat]
    change ((U.ι ≫ c).appTop ≫ r.appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom a) =
      ((Spec.map (CommRingCat.ofHom ρ)).appTop ≫ ((ι ⁻¹ᵁ U).ι ≫ c').appTop).hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom a)
    rw [← Scheme.comp_appTop', ← Scheme.comp_appTop', Category.assoc, hsq]
  ·
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    change r.appTop.hom (U.topIso.inv.hom f) = (ι ⁻¹ᵁ U).topIso.inv.hom (Scheme.Opens.bcSection c ρ U f)
    rw [Scheme.Opens.bcSection, ← CommRingCat.comp_apply _ (ι ⁻¹ᵁ U).topIso.inv, Iso.hom_inv_id]
    rfl

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.topIso_inv_resLE_appTop_topIso_hom {X Y : Scheme.{u}} (ι : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (ι.resLE U (ι ⁻¹ᵁ U) le_rfl).appTop ≫ (ι ⁻¹ᵁ U).topIso.hom = ι.app U := by
  rw [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.resLE_appLE]
  erw [Scheme.Hom.map_appLE_assoc]
  erw [Scheme.Hom.appLE_map]
  rw [Scheme.Hom.appLE_eq_app]

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.bcSection_eq (U : C.Opens) (f : Γ(C, U)) :
    Scheme.Opens.bcSection c ρ U f = ((pullback.fst c (Spec.map (CommRingCat.ofHom ρ))).app U).hom f := by
  have := congrArg (fun φ => φ.hom f)
    (Scheme.Opens.topIso_inv_resLE_appTop_topIso_hom (pullback.fst c (Spec.map (CommRingCat.ofHom ρ))) U)
  simpa [Scheme.Opens.bcSection] using this

end BaseChangeSquare

theorem SpecMap_mapRingHom_injective_of_quotient (I : Ideal k) [I.IsPrime] :
    Function.Injective (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k (FractionRing (k ⧸ I)))))).base := by
  rw [IsScalarTower.algebraMap_eq k (k ⧸ I) (FractionRing (k ⧸ I)), ← Polynomial.mapRingHom_comp]
  rw [Spec.map_base]
  change Function.Injective (PrimeSpectrum.comap ((Polynomial.mapRingHom (algebraMap (k ⧸ I)
    (FractionRing (k ⧸ I)))).comp (Polynomial.mapRingHom (algebraMap k (k ⧸ I)))))
  rw [PrimeSpectrum.comap_comp]
  refine Function.Injective.comp ?_ ?_
  · exact PrimeSpectrum.comap_injective_of_surjective _
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  · letI : Algebra (Polynomial (k ⧸ I)) (Polynomial (FractionRing (k ⧸ I))) :=
      Polynomial.algebra (k ⧸ I) (FractionRing (k ⧸ I))
    haveI : IsLocalization (Submonoid.map Polynomial.C (nonZeroDivisors (k ⧸ I)))
        (Polynomial (FractionRing (k ⧸ I))) := Polynomial.isLocalization _ _
    have : (Polynomial.mapRingHom (algebraMap (k ⧸ I) (FractionRing (k ⧸ I)))) =
        algebraMap (Polynomial (k ⧸ I)) (Polynomial (FractionRing (k ⧸ I))) := rfl
    rw [this]
    exact PrimeSpectrum.localization_comap_injective _ (Submonoid.map Polynomial.C (nonZeroDivisors (k ⧸ I)))

end AlgebraicGeometry

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsLocallyNoetherian IsOpenImmersion.lift Scheme.Opens.topIso_inv Scheme.Opens.toScheme_presheaf_map HasAffineProperty SmoothOfRelativeDimension IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.resLE_appLE GeometricallyIntegral Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp IsProper.eq_valuativeCriterion Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyQuasiFinite IsFinite isAffine_of_isAffineHom IsSeparated.of_comp QuasiCompact Scheme.Pullback.range_fst IsAffine LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.Hom.map_appLE_assoc Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.Hom.appTop Scheme.toSpecΓ_appTop Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.topIso_hom Spec.map_base Scheme.Opens.ι_app_self germ_injective_of_isIntegral ValuativeCriterion.iff HasAffineProperty.iff_of_isAffine LocallyQuasiFinite.of_finite_preimage_singleton Spec.map_injective IsSeparated.valuativeCriterion locallyOfFiniteType_of_comp IsSeparated IsFinite.iff_isProper_and_isAffineHom Scheme.Spec_stalkClosedPointTo_fromSpecStalk toSpecΓ_SpecMap_ΓSpecIso_inv IsFinite.SpecMap_iff IsProper.of_valuativeCriterion IsAffineOpen IsNoetherian Scheme.Opens ValuativeCriterion.Existence Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE ValuativeCriterion Scheme.ΓSpecIso_naturality IsAffineHom Scheme.Opens.ι_appTop IsOpenImmersion.lift_fac IsFinite.of_isProper_of_locallyQuasiFinite Scheme.germ_stalkClosedPointTo toSpecΓ Scheme.Hom.appLE geometrically Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.isIntegral_pullback_Spec_field Scheme.Opens.finite_preimage_singleton_toSpecPolynomial"
p2m_open "AlgebraicGeometry"

open IsLocalRing

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

abbrev fibreField (y : PrimeSpectrum R) : Type u := FractionRing (R ⧸ y.asIdeal)

theorem mem_range_SpecMap_fibreField (y : PrimeSpectrum R) :
    (y : Spec (CommRingCat.of R)) ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap R (fibreField y)))).base := by
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  change PrimeSpectrum.comap (algebraMap R (fibreField y)) ⟨⊥, Ideal.isPrime_bot⟩ = y
  ext1
  change Ideal.comap (algebraMap R (fibreField y)) ⊥ = y.asIdeal
  rw [← RingHom.ker_eq_comap_bot, IsScalarTower.algebraMap_eq R (R ⧸ y.asIdeal) (fibreField y),
    ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _),
    ← RingHom.ker_eq_comap_bot, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

theorem transcendental_germToFunctionField_of_sections {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (cK : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) [Nonempty U] (s : Γ(X, U))
    (hs : letI := Scheme.TwoAffineOpenCover.algebraOfHom cK U; Transcendental K s) :
    letI := (AlgebraicCurve.baseToFunctionField cK).toAlgebra
    Transcendental K ((X.germToFunctionField U).hom s) := by
  letI A1 := Scheme.TwoAffineOpenCover.algebraOfHom cK U
  letI := (AlgebraicCurve.baseToFunctionField cK).toAlgebra
  let θ : Γ(X, U) →ₐ[K] X.functionField :=
    { (X.germToFunctionField U).hom with
      commutes' := fun k => by
        change (X.germToFunctionField U).hom ((cK.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom k)) =
          (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (cK.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom k))
        rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
        change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.germ U (genericPoint X) _).hom _ = _
        rw [TopCat.Presheaf.germ_res]
        rfl }
  have hθ : Function.Injective θ := germ_injective_of_isIntegral X _ _
  intro halg
  apply hs
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, hθ ?_⟩
  rw [← Polynomial.aeval_algHom_apply θ s p, map_zero]
  exact hp

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_of_le [IsNoetherianRing R]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V W : C.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hUVW : ∀ x : C, x ∈ U → x ∈ V → x ∈ W)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : W = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE hWU).op).hom f *
      (C.presheaf.map (homOfLE hWV).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) :
    IsAffineOpen U ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
       (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.Finite) := by
  haveI hprop := Scheme.Opens.isProper_toSpecPolynomial_of_twoChart' c U V W hWU hWV hUVW f g hcov hUV hfg
  set φ := Scheme.Opens.toSpecPolynomial c U f with hφ

  have hqf : LocallyQuasiFinite φ := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ (fun p => ?_)

    set y : PrimeSpectrum R := (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))).base p with hy
    set κ := fibreField y
    set ρ : R →+* κ := algebraMap R κ with hρ
    set ξ := Spec.map (CommRingCat.ofHom ρ) with hξ
    set ι := pullback.fst c ξ with hι
    set c' := pullback.snd c ξ with hc'
    set U' := ι ⁻¹ᵁ U with hU'
    set r := ι.resLE U U' le_rfl with hr
    haveI : IsIntegral (pullback c ξ) := SmoothProperCurve.isIntegral_pullback_Spec_field R c ξ
    set φ' := Scheme.Opens.toSpecPolynomial c' U' (Scheme.Opens.bcSection c ρ U f) with hφ'
    set πX := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ρ)) with hπX
    have hsq : r ≫ φ = φ' ≫ πX := Scheme.Opens.resLE_toSpecPolynomial c ρ U f

    have hlift : ∀ u : (U : Scheme.{u}), φ.base u = p → ∃ u' : (U' : Scheme.{u}), r.base u' = u := by
      intro u hu
      have hcu : c.base (U.ι.base u) = y := by
        have key : (Scheme.Opens.toSpecPolynomial c U f ≫
            Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))).base u = (U.ι ≫ c).base u := by
          rw [Scheme.Opens.toSpecPolynomial_comp_C c U f]
        change (U.ι ≫ c).base u = (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))).base p
        rw [← key, ← hu]
        rfl
      have hmem : U.ι.base u ∈ Set.range ι.base := by
        rw [hι, Scheme.Pullback.range_fst]
        show c.base (U.ι.base u) ∈ Set.range ξ.base
        rw [hcu]; exact mem_range_SpecMap_fibreField y
      obtain ⟨x', hx'⟩ := hmem
      have hx'U : x' ∈ U' := by show ι.base x' ∈ U; rw [hx']; exact u.2
      refine ⟨⟨x', hx'U⟩, ?_⟩
      apply U.ι.isOpenEmbedding.injective
      change (r ≫ U.ι).base ⟨x', hx'U⟩ = U.ι.base u
      rw [hr, Scheme.Hom.resLE_comp_ι]
      exact hx'
    by_cases hne : Nonempty U'
    ·
      haveI := hne
      have hs : letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
          Transcendental κ ((pullback c ξ).germToFunctionField U' (Scheme.Opens.bcSection c ρ U f)) := by
        rw [Scheme.Opens.bcSection_eq]
        exact transcendental_germToFunctionField_of_sections c' U' _ (hft κ)
      have hQ : ∀ p', (φ'.base ⁻¹' {p'}).Finite := fun p' =>
        Scheme.Opens.finite_preimage_singleton_toSpecPolynomial c' U'
          (Scheme.Opens.bcSection c ρ U f) hs p'
      have hS : (πX.base ⁻¹' {p}).Finite :=
        Set.Subsingleton.finite fun a ha b hb =>
          SpecMap_mapRingHom_injective_of_quotient y.asIdeal (ha.trans hb.symm)
      refine ((hS.biUnion fun p' _ => hQ p').image r.base).subset ?_
      intro u hu
      obtain ⟨u', rfl⟩ := hlift u hu
      refine ⟨u', Set.mem_biUnion (x := φ'.base u') ?_ rfl, rfl⟩
      change (φ' ≫ πX).base u' = p
      rw [← hsq]
      exact hu
    ·
      convert Set.finite_empty
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hu
      obtain ⟨u', -⟩ := hlift u hu
      exact hne ⟨⟨u'.1, u'.2⟩⟩
  haveI : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hUaff : IsAffine (U : Scheme.{u}) := isAffine_of_isAffineHom φ
  exact ⟨hUaff, Scheme.Opens.finite_aeval_of_twoChart c U V W hWU hWV hUVW hUaff f g hcov hUV hfg⟩

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_impl [IsNoetherianRing R]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) :
    IsAffineOpen U ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
       (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.Finite) :=
  Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_of_le c U V (U ⊓ V) inf_le_left inf_le_right
    (fun _ hu hv => ⟨hu, hv⟩) f g hcov hUV hfg hft

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right_impl [IsNoetherianRing R]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hVU : U ⊓ V = C.basicOpen f)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) :
    IsAffineOpen V ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
       (Polynomial.aeval g : R[X] →ₐ[R] Γ(C, V)).toRingHom.Finite) :=
  Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_of_le c V U (U ⊓ V) inf_le_right inf_le_left
    (fun _ hv hu => ⟨hu, hv⟩) g f (by rw [sup_comm]; exact hcov) hVU (by rw [mul_comm]; exact hfg) hft

end AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart.AlgebraicGeometry _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) :
    IsAffineOpen U ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
       (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.Finite) :=
  AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_impl c U V f g hcov hUV hfg hft

end S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart (solution)
