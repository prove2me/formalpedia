-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Opens.isProper_toSpecPolynomial_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cc33d74a-89b5-5a2c-92c1-f2bd77311bfa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal

set_option maxHeartbeats 1600000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal.AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian IsOpenImmersion.lift Scheme.Opens.topIso_inv Scheme.Opens.toScheme_presheaf_map HasAffineProperty IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp IsProper.eq_valuativeCriterion Scheme.SpecMap_stalkSpecializes_fromSpecStalk IsSeparated.of_comp QuasiCompact LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.ι_app_self ValuativeCriterion.iff HasAffineProperty.iff_of_isAffine Spec.map_injective IsSeparated.valuativeCriterion locallyOfFiniteType_of_comp IsSeparated Scheme.Spec_stalkClosedPointTo_fromSpecStalk toSpecΓ_SpecMap_ΓSpecIso_inv IsProper.of_valuativeCriterion IsNoetherian Scheme.Opens ValuativeCriterion.Existence ValuativeCriterion Scheme.ΓSpecIso_naturality IsOpenImmersion.lift_fac Scheme.germ_stalkClosedPointTo toSpecΓ Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Opens.topIso_inv Opens.toScheme_presheaf_map germToFunctionField fromSpecStalk Opens.range_ι Hom Γ Hom.germ_stalkMap_apply stalkClosedPointTo_comp SpecMap_stalkSpecializes_fromSpecStalk topIso toSpecΓ_naturality ΓSpecIso_inv_naturality functionField toSpecΓ_appTop stalkClosedPointTo Opens.ι_app_self Spec_stalkClosedPointTo_fromSpecStalk Opens ΓSpecIso_naturality germ_stalkClosedPointTo ΓSpecIso toSpecΓ" namespace Opens p2m_export "AlgebraicGeometry.Scheme.Opens" "topIso_inv toScheme_presheaf_map toSpecΓ range_ι toSpecΓ_naturality toSpecΓ_appTop ι_app_self topIso ι ι_preimage_self" end Scheme.Opens
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

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Opens.topIso_inv Opens.toScheme_presheaf_map germToFunctionField fromSpecStalk Opens.range_ι Hom Γ Hom.germ_stalkMap_apply stalkClosedPointTo_comp SpecMap_stalkSpecializes_fromSpecStalk topIso toSpecΓ_naturality ΓSpecIso_inv_naturality functionField toSpecΓ_appTop stalkClosedPointTo Opens.ι_app_self Spec_stalkClosedPointTo_fromSpecStalk Opens ΓSpecIso_naturality germ_stalkClosedPointTo ΓSpecIso toSpecΓ" end Scheme
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
open IsLocalRing in

theorem Scheme.Opens.valuativeCriterion_existence_toSpecPolynomial
    [IsIntegral C] [IsProper c] (hval : ∀ x : C, ValuationRing (C.presheaf.stalk x))
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U) :
    ValuativeCriterion.Existence (Scheme.Opens.toSpecPolynomial c U s) := by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  haveI : IsDomain (CommRingCat.of R) := ‹_›
  haveI : ValuationRing (CommRingCat.of R) := ‹_›
  letI : Field (CommRingCat.of K) := ‹_›
  set φ := Scheme.Opens.toSpecPolynomial c U s with hφ
  set πC := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) with hπC
  set α := Spec.map (CommRingCat.ofHom (algebraMap R K)) with hα

  have hvc : ValuativeCriterion c := by
    have h : IsProper c := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have w' : (i₁ ≫ U.ι) ≫ c = α ≫ (i₂ ≫ πC) := by
    rw [Category.assoc, ← Scheme.Opens.toSpecPolynomial_comp_C c U s, ← hφ, reassoc_of% w]
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
  have hF3 : (Scheme.stalkClosedPointTo (i₁ ≫ U.ι)).hom (C.presheaf.germ U _ hp₀U s) =
      algebraMap R K r₀ := by
    rw [hr₀, ← Scheme.Opens.ΓSpecIso_appTop_topIso_inv_eq c U s w, Scheme.stalkClosedPointTo_comp]
    show (Scheme.stalkClosedPointTo i₁).hom ((U.ι.stalkMap (i₁.base (closedPoint K))).hom
      (C.presheaf.germ U (U.ι.base (i₁.base (closedPoint K))) hp₀U s)) = _
    rw [Scheme.Hom.germ_stalkMap_apply U.ι U (i₁.base (closedPoint K)) hp₀U s]
    rw [Scheme.Opens.ι_app_self_apply, TopCat.Presheaf.germ_res_apply,
      Scheme.stalkClosedPointTo_germ_top]

  have hx₁U : x₁ ∈ U := by
    apply hU
    haveI := hval x₁
    rcases ValuationRing.isInteger_or_isInteger (C.presheaf.stalk x₁) (C.germToFunctionField U s)
      with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha⟩
    by_cases hf0 : C.germToFunctionField U s = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    suffices hu : IsUnit a by
      obtain ⟨b, hab⟩ := hu.exists_right_inv
      refine ⟨b, ?_⟩
      have e := congrArg (algebraMap (C.presheaf.stalk x₁) C.functionField) hab
      rw [map_mul, map_one, ha] at e
      rw [← mul_inv_cancel_left₀ hf0 (algebraMap _ _ b), e, mul_one]
    apply isUnit_of_map_unit (Scheme.stalkClosedPointTo ℓ).hom a
    refine isUnit_iff_exists_inv.mpr ⟨r₀, ?_⟩
    apply IsFractionRing.injective R K
    rw [map_mul, map_one]
    have e1 : algebraMap R K ((Scheme.stalkClosedPointTo ℓ).hom a) =
        (Scheme.stalkClosedPointTo (i₁ ≫ U.ι)).hom (C.presheaf.stalkSpecializes h01 a) := by
      have := congrArg (fun g => g.hom a) hF1
      simp at this
      exact this
    have e2 : (C.presheaf.stalkSpecializes h01).hom a * C.presheaf.germ U _ hp₀U s = 1 := by
      apply IsFractionRing.injective (C.presheaf.stalk ((i₁ ≫ U.ι).base (closedPoint K)))
        C.functionField
      rw [map_mul, map_one]
      have e3 : algebraMap (C.presheaf.stalk ((i₁ ≫ U.ι).base (closedPoint K))) C.functionField
          ((C.presheaf.stalkSpecializes h01).hom a) =
          algebraMap (C.presheaf.stalk x₁) C.functionField a := by
        change (C.presheaf.stalkSpecializes h01 ≫ C.presheaf.stalkSpecializes _).hom a = _
        rw [TopCat.Presheaf.stalkSpecializes_comp]
        rfl
      have e4 : algebraMap (C.presheaf.stalk ((i₁ ≫ U.ι).base (closedPoint K))) C.functionField
          (C.presheaf.germ U _ hp₀U s) = C.germToFunctionField U s := by
        change (C.presheaf.germ U _ hp₀U ≫ C.presheaf.stalkSpecializes _).hom s = _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
      rw [e3, e4, ha, inv_mul_cancel₀ hf0]
    rw [e1, ← hF3, ← map_mul, e2, map_one]

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

theorem Scheme.Opens.isProper_toSpecPolynomial_of_maximal'
    [IsIntegral C] [IsProper c] (hval : ∀ x : C, ValuationRing (C.presheaf.stalk x))
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U) :
    IsProper (Scheme.Opens.toSpecPolynomial c U s) := by
  set φ := Scheme.Opens.toSpecPolynomial c U s with hφ
  have htri := Scheme.Opens.toSpecPolynomial_comp_C c U s

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
  exact Scheme.Opens.valuativeCriterion_existence_toSpecPolynomial c hval U s hU

end AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (hval : ∀ x : C, ValuationRing (C.presheaf.stalk x))
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U) :
    IsProper ((U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))) :=
  AlgebraicGeometry.Scheme.Opens.isProper_toSpecPolynomial_of_maximal' c hval U s hU

end S_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal (solution)
