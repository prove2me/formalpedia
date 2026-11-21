-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_iff_of_surjective_closed_immersion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T18:46:32.758268+00:00
-- url     : https://prove2.me/submissions/267f8156-0182-4683-8ae5-3aff862c7630

import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.MorphismProperty.CommaSites
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Ring

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponKummerSequence
universe u
def underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

instance continuous_underlying (X : Scheme.{u}) :
    (underlying X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology := by
  have hle : Scheme.precoverage (@Etale.{u}) ≤ (MorphismProperty.precoverage (@Etale.{u})) :=
    inf_le_right
  have hc := MorphismProperty.isContinuous_comap_forget (S := X) (P := @Etale)
    (Scheme.precoverage @Etale) hle
  rw [MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _ hle] at hc
  letI : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) := hc
  exact Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _


end PhilipponKummerSequence

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite


namespace PhilipponEtaleBaseChangeComparison

universe u
variable {X Y : Scheme.{u}}

/-- Base change on the categories underlying the small étale sites. -/
abbrev baseChange (f : Y ⟶ X) : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.pullback (@Etale) ⊤ f

/-- Pullback along an étale arrow commutes with base change. -/
theorem map_isPullback (f : Y ⟶ X) {U V : X.Etale} (g : U ⟶ V) :
    IsPullback (pullback.fst U.hom f) ((baseChange f).map g).left g.left
      (pullback.fst V.hom f) := by
  have h₁ : g.left ≫ V.hom = U.hom := MorphismProperty.Over.w g
  have h₂ : ((baseChange f).map g).left ≫ pullback.snd V.hom f = pullback.snd U.hom f := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback V.hom f)
  · simpa only [h₁, h₂] using IsPullback.of_hasPullback U.hom f
  · symm
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst]

/-- Pullback along an arbitrary morphism preserves small étale covering sieves. -/
theorem coverPreserving (f : Y ⟶ X) :
    CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology (baseChange f) where
  cover_preserve {V S} h := by
    rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at h
    rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
      Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range] at h ⊢
    intro w
    obtain ⟨g, z, hz⟩ := h (pullback.fst V.hom f w)
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (map_isPullback f g.obj.hom) z w hz
    exact ⟨g, t, ht⟩

/-- Base change along a surjection preserves and reflects covering sieves.
This part does not need an equivalence of the underlying categories. -/
theorem covering_iff (f : Y ⟶ X) [Surjective f] {V : X.Etale} (S : Sieve V) :
    S.functorPushforward (baseChange f) ∈ Y.smallEtaleTopology _ ↔
      S ∈ X.smallEtaleTopology _ := by
  refine ⟨?_, (coverPreserving f).cover_preserve⟩
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
    Scheme.ofArrows_mem_smallEtaleTopology_iff, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range]
  intro h v
  obtain ⟨w, hw⟩ := (show Function.Surjective (pullback.fst V.hom f) from
    (inferInstance : Surjective (pullback.fst V.hom f)).surj) v
  obtain ⟨g, z, hz⟩ := h w
  refine ⟨g, pullback.fst g.obj.left.hom f z, ?_⟩
  have hcomm := congrArg (fun a : (_ : Scheme) ⟶ (_ : Scheme) => a z)
    (map_isPullback f g.obj.hom).w
  exact hcomm.trans ((congrArg (pullback.fst V.hom f) hz).trans hw)

instance baseChange_isContinuous (f : Y ⟶ X) :
    (baseChange f).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology := by
  letI : PreservesFiniteLimits (baseChange f) := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  have : RepresentablyFlat (baseChange f) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving f)

end PhilipponEtaleBaseChangeComparison

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
universe u
/-- The empty étale object has a unique section of any abelian sheaf. -/
theorem subsingleton_sections_of_isEmpty {X : Scheme.{u}} {W : X.Etale}
    (hW : IsEmpty W.left) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Subsingleton (F.obj.obj (op W)) := by
  let V : Empty → X.Etale := Empty.elim
  let p (i : Empty) : V i ⟶ W := Empty.elim i
  have hCover : Sieve.ofArrows V p ∈ X.smallEtaleTopology W :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr (Set.ext fun x => (hW.false x).elim)
  have hBot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Empty.elim i
  refine ⟨fun x y => ?_⟩
  have hs := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ hBot).isSeparatedFor.ext
  intro _ _ h
  exact h.elim

end AlgebraicGeometry.Scheme

end

section

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Polynomial
open scoped TensorProduct


namespace PhilipponEtaleThickeningLifts

universe u

private theorem lift_standardEtale
    {C C₀ : Type u} [CommRing C] [CommRing C₀] [Algebra C C₀] (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type u) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by
  classical
  obtain ⟨P₀⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := C₀) (S := S₀)
  rcases subsingleton_or_nontrivial C₀ with hC₀ | hC₀
  ·
    haveI : Subsingleton S₀ := Module.subsingleton C₀ S₀
    refine ⟨C, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    exact AlgEquiv.ofBijective ((Algebra.ofId C₀ S₀).comp (Algebra.TensorProduct.rid C C₀ C₀).toAlgHom)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

  set φ : C →+* C₀ := algebraMap C C₀ with hφ
  obtain ⟨f, hf, -, hfm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (f := φ) ((mem_lifts _).mpr (map_surjective φ hC P₀.f)) P₀.monic_f
  obtain ⟨p₁, p₂, n, hP⟩ := P₀.cond
  obtain ⟨g, hg⟩ := map_surjective φ hC P₀.g
  obtain ⟨q₁, hq₁⟩ := map_surjective φ hC p₁
  obtain ⟨q₂, hq₂⟩ := map_surjective φ hC p₂
  let P : StandardEtalePair C :=
    { f := f, monic_f := hfm, g := g * (derivative f * q₁ + f * q₂), cond := ⟨g * q₁, g * q₂, 1, by ring⟩ }
  have hPf : P.f.map φ = P₀.f := hf
  have hPg : P.g.map φ = P₀.g ^ (n + 1) := by
    show (g * (derivative f * q₁ + f * q₂)).map φ = P₀.g ^ (n + 1)
    simp only [Polynomial.map_mul, Polynomial.map_add, ← Polynomial.derivative_map, hf, hg, hq₁, hq₂, hP]
    ring

  letI : Algebra C S₀ := ((algebraMap C₀ S₀).comp φ).toAlgebra
  haveI : IsScalarTower C C₀ S₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have key : ∀ (T : Type u) [CommRing T] [Algebra C₀ T] [Algebra C T] [IsScalarTower C C₀ T] (t : T),
      P.HasMap t ↔ P₀.HasMap t := by
    intro T _ _ _ _ t
    simp only [StandardEtalePair.HasMap]
    rw [← aeval_map_algebraMap C₀ t P.f, ← aeval_map_algebraMap C₀ t P.g, ← hφ, hPf, hPg, map_pow,
      isUnit_pow_iff (Nat.succ_ne_zero n)]
  have h1 : P.HasMap P₀.x := (key S₀ P₀.x).mpr P₀.hasMap
  have h2' : P.HasMap ((1 : C₀) ⊗ₜ[C] P.X) :=
    (StandardEtalePair.hasMap_X (P := P)).map
      (Algebra.TensorProduct.includeRight (R := C) (A := C₀) (B := P.Ring))
  have h2 : P₀.HasMap ((1 : C₀) ⊗ₜ[C] P.X) := (key (C₀ ⊗[C] P.Ring) _).mp h2'
  let F : C₀ ⊗[C] P.Ring →ₐ[C₀] S₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId C₀ S₀) (P.lift P₀.x h1) (fun _ _ => .all _ _)
  let G : S₀ →ₐ[C₀] C₀ ⊗[C] P.Ring := (P₀.lift ((1 : C₀) ⊗ₜ[C] P.X) h2).comp P₀.equivRing.toAlgHom
  have hF : F ((1 : C₀) ⊗ₜ[C] P.X) = P₀.x := by
    simp [F, Algebra.TensorProduct.lift_tmul, StandardEtalePair.lift_X]
  have hG : G P₀.x = (1 : C₀) ⊗ₜ[C] P.X := by
    simp [G, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom F G ?_ ?_⟩⟩
  · apply P₀.hom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hG, hF]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply StandardEtalePair.hom_ext
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        AlgHom.id_apply, hF, hG]

theorem exists_local_model
    {X X₀ Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] (q₀ : Y₀ ⟶ X₀) [Etale q₀] (y : Y₀) :
    ∃ (V₀ : Y₀.Opens) (_ : y ∈ V₀) (V : Scheme.{u}) (qV : V ⟶ X) (_ : Etale qV) (jV : (V₀ : Scheme.{u}) ⟶ V),
      IsPullback jV (V₀.ι ≫ q₀) qV i := by
  classical

  obtain ⟨U, hUa, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show i (q₀ y) ∈ (⊤ : X.Opens) from trivial)
  replace hUa : IsAffineOpen U := hUa

  have hU₀a : IsAffineOpen (i ⁻¹ᵁ U) := hUa.preimage i

  obtain ⟨W, hWa, hyW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y₀.isBasis_affineOpens)
    (show y ∈ q₀ ⁻¹ᵁ (i ⁻¹ᵁ U) from hxU)
  replace hWa : IsAffineOpen W := hWa

  letI algA : Algebra Γ(X, U) Γ(X₀, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI algB : Algebra Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) := (q₀.appLE (i ⁻¹ᵁ U) W hWle).hom.toAlgebra
  have ha : Function.Surjective (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)) := by
    show Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective U hUa
  have hEt : Algebra.Etale Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) := Etale.etale_appLE q₀ hU₀a hWa hWle
  haveI := hEt.formallyEtale
  haveI := hEt.finitePresentation

  set p : PrimeSpectrum Γ(Y₀, W) := hWa.primeIdealOf ⟨y, hyW⟩ with hp
  obtain ⟨g, hgp, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := Γ(X₀, i ⁻¹ᵁ U)) p.asIdeal
  have hV₀a : IsAffineOpen (Y₀.basicOpen g) := hWa.basicOpen g
  have hV₀le : Y₀.basicOpen g ≤ q₀ ⁻¹ᵁ (i ⁻¹ᵁ U) := (Y₀.basicOpen_le g).trans hWle
  have hyV₀ : y ∈ Y₀.basicOpen g := by
    have h1 : hWa.fromSpec p = y := hWa.fromSpec_primeIdealOf ⟨y, hyW⟩
    rw [← h1]
    show p ∈ hWa.fromSpec ⁻¹ᵁ Y₀.basicOpen g
    rw [hWa.fromSpec_preimage_basicOpen]
    exact hgp
  letI algS₀ : Algebra Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g) :=
    (q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le).hom.toAlgebra
  haveI : IsScalarTower Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) Γ(Y₀, Y₀.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show (q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le).hom r =
        (Y₀.presheaf.map (homOfLE (Y₀.basicOpen_le g)).op).hom ((q₀.appLE (i ⁻¹ᵁ U) W hWle).hom r)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  haveI : IsLocalization.Away g Γ(Y₀, Y₀.basicOpen g) := hWa.isLocalization_basicOpen g
  haveI : Algebra.IsStandardEtale Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g) :=
    Algebra.IsStandardEtale.of_equiv
      ((IsLocalization.algEquiv (.powers g) (Localization.Away g) Γ(Y₀, Y₀.basicOpen g)).restrictScalars
        Γ(X₀, i ⁻¹ᵁ U))

  obtain ⟨S, _, _, hS, ⟨e⟩⟩ :=
    lift_standardEtale ha
      Γ(Y₀, Y₀.basicOpen g)
  have hSe : (algebraMap Γ(X, U) S).Etale := RingHom.etale_algebraMap.mpr inferInstance
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S))) := HasRingHomProperty.Spec_iff.mpr hSe
  let ψ : S →+* Γ(Y₀, Y₀.basicOpen g) :=
    e.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := Γ(X, U)) (A := Γ(X₀, i ⁻¹ᵁ U)) (B := S))
  refine ⟨Y₀.basicOpen g, hyV₀, Spec (.of S),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ hUa.fromSpec, inferInstance,
    hV₀a.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩

  have top : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)))) := by
    have H := (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)))).flip
    refine H.of_iso
      (pullbackSpecIso Γ(X, U) Γ(X₀, i ⁻¹ᵁ U) S ≪≫ Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← pullbackSpecIso_hom_snd]
      congr 2
      ext x
      symm
      change e.symm (e (Algebra.TensorProduct.includeRight x)) = Algebra.TensorProduct.includeRight x
      exact e.symm_apply_apply _
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← pullbackSpecIso_hom_fst]
      congr 2
      ext x
      symm
      change e.symm (algebraMap _ _ x) = Algebra.TensorProduct.includeLeftRingHom x
      rw [e.symm.commutes x]
      rfl
  have bot : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U))))
      hU₀a.fromSpec hUa.fromSpec i := by
    have e1 : CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)) = i.appLE U (i ⁻¹ᵁ U) le_rfl := rfl
    rw [e1]
    have comm : Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl) ≫ hUa.isoSpec.inv = hU₀a.isoSpec.inv ≫ (i ∣_ U) := by
      rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι,
        ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec]
    have sq : IsPullback (Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl)) hU₀a.isoSpec.inv hUa.isoSpec.inv (i ∣_ U) :=
      IsPullback.of_vert_isIso ⟨comm⟩
    have := sq.paste_vert (isPullback_morphismRestrict i U)
    simpa only [IsAffineOpen.isoSpec_inv_ι] using this
  have big := top.paste_vert bot
  refine big.of_iso hV₀a.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  have e2 : CommRingCat.ofHom (algebraMap Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g)) =
      q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le := rfl
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
  rw [e2, IsAffineOpen.SpecMap_appLE_fromSpec q₀ hU₀a hV₀a hV₀le, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]

end PhilipponEtaleThickeningLifts

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison


namespace PhilipponEtaleClosedPushforward

universe u
variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- Direct image of an étale abelian sheaf by a morphism of schemes. -/
def pushforward : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (baseChange i).sheafPushforwardContinuous _ _ _

instance : (pushforward i).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (pushforward i) := by
  let e := (baseChange i).sheafPushforwardContinuousCompSheafToPresheafIso
    AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology
  have : PreservesFiniteLimits
      (pushforward i ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Étale neighborhoods over the closed subscheme can be refined at each
point by pullbacks of étale neighborhoods over the original scheme. -/
theorem exists_neighborhood_lift [IsClosedImmersion i]
    {V : X.Etale} {W : Z.Etale} (g : W ⟶ (baseChange i).obj V) (w : W.left) :
    ∃ (U : X.Etale) (a : U ⟶ V) (b : (baseChange i).obj U ⟶ W)
      (z : ((baseChange i).obj U).left), b ≫ g = (baseChange i).map a ∧ b.left z = w := by
  let k := pullback.fst V.hom i
  have : IsClosedImmersion k := inferInstanceAs (IsClosedImmersion (pullback.fst V.hom i))
  have : Etale g.left := inferInstance
  obtain ⟨D, hw, T, q, hq, j, hp⟩ :=
    PhilipponEtaleThickeningLifts.exists_local_model k g.left w
  let U := Scheme.Etale.mk (q ≫ V.hom)
  let a : U ⟶ V := MorphismProperty.Over.homMk q rfl trivial
  let sq := map_isPullback i a
  let e := hp.isoIsPullback _ _ sq
  have hmap : e.inv ≫ (D.ι ≫ g.left) = ((baseChange i).map a).left :=
    hp.isoIsPullback_inv_snd _ _ sq
  have hg : (D.ι ≫ g.left) ≫ ((baseChange i).obj V).hom = D.ι ≫ W.hom :=
    (Category.assoc _ _ _).trans (congrArg (D.ι ≫ ·) (MorphismProperty.Over.w g))
  let b : (baseChange i).obj U ⟶ W := MorphismProperty.Over.homMk (e.inv ≫ D.ι) (by
    calc
      (e.inv ≫ D.ι) ≫ W.hom = e.inv ≫ (D.ι ≫ W.hom) := Category.assoc _ _ _
      _ = e.inv ≫ ((D.ι ≫ g.left) ≫ ((baseChange i).obj V).hom) :=
        congrArg (e.inv ≫ ·) hg.symm
      _ = ((baseChange i).map a).left ≫ ((baseChange i).obj V).hom :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmap)
      _ = _ := MorphismProperty.Over.w ((baseChange i).map a)) trivial
  refine ⟨U, a, b, e.hom ⟨w, hw⟩, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change (e.inv ≫ D.ι) ≫ g.left = _
    rw [Category.assoc, hmap]
  · change (e.inv ≫ D.ι) (e.hom ⟨w, hw⟩) = w
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    rfl

private theorem covers_iff_at_points {B : Scheme.{u}} {V : B.Etale} (R : Sieve V) :
    R ∈ B.smallEtaleTopology V ↔
      ∀ x : V.left, ∃ (W : B.Etale) (a : W ⟶ V) (w : W.left), R a ∧ a.left w = x := by
  have h := Scheme.ofArrows_mem_smallEtaleTopology_iff
    (fun (g : R.arrows.category) => g.obj.hom)
  rw [Sieve.ofArrows_category] at h
  rw [h]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range]
  refine ⟨fun hc x => ?_, fun hc x => ?_⟩
  · obtain ⟨g, w, hw⟩ := hc x
    exact ⟨g.obj.left, g.obj.hom, w, g.property, hw⟩
  · obtain ⟨W, a, w, ha, hw⟩ := hc x
    exact ⟨⟨Over.mk a, ha⟩, w, hw⟩

private theorem exists_empty_neighborhood [IsClosedImmersion i]
    (V : X.Etale) (x : V.left) (hx : x ∉ Set.range (pullback.fst V.hom i)) :
    ∃ (U : X.Etale) (a : U ⟶ V) (y : U.left),
      IsEmpty ((baseChange i).obj U).left ∧ a.left y = x := by
  let k := pullback.fst V.hom i
  have : IsClosedImmersion k := inferInstanceAs (IsClosedImmersion (pullback.fst V.hom i))
  let D : V.left.Opens := ⟨(Set.range k)ᶜ, k.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U := Scheme.Etale.mk (D.ι ≫ V.hom)
  let a : U ⟶ V := MorphismProperty.Over.homMk D.ι rfl trivial
  refine ⟨U, a, ⟨x, hx⟩, ⟨fun z => ?_⟩, rfl⟩
  let y : D := pullback.fst U.hom i z
  have e := congrArg (fun s : ((baseChange i).obj U).left ⟶ V.left => s z)
    (map_isPullback i a).w
  exact y.property ⟨((baseChange i).map a).left z, e.symm⟩

/-- Pushforward along a closed immersion preserves epimorphisms of abelian
sheaves on the small étale site. -/
theorem epi_pushforward [IsClosedImmersion i]
    {F G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G) [Epi a] :
    Epi ((pushforward i).map a) := by
  have : Sheaf.IsLocallySurjective a :=
    (Sheaf.isLocallySurjective_iff_epi' (J := Z.smallEtaleTopology)
      AddCommGrpCat.{u} a).mpr inferInstance
  apply (Sheaf.isLocallySurjective_iff_epi' (J := X.smallEtaleTopology)
    AddCommGrpCat.{u} ((pushforward i).map a)).mp
  constructor
  intro V s
  apply (covers_iff_at_points _).mpr
  intro x
  by_cases hx : x ∈ Set.range (pullback.fst V.hom i)
  · obtain ⟨y, hy⟩ := hx
    have hs : Presheaf.imageSieve a.hom (U := (baseChange i).obj V) s ∈
        Z.smallEtaleTopology ((baseChange i).obj V) :=
      Presheaf.imageSieve_mem Z.smallEtaleTopology a.hom (U := op ((baseChange i).obj V)) s
    obtain ⟨W, b, w, ⟨t, ht⟩, hw⟩ := (covers_iff_at_points _).mp hs y
    obtain ⟨U, e, d, z, he, hz⟩ := exists_neighborhood_lift i b w
    refine ⟨U, e, pullback.fst U.hom i z, ⟨F.obj.map d.op t, ?_⟩, ?_⟩
    · change a.hom.app _ (F.obj.map d.op t) = G.obj.map ((baseChange i).map e).op s
      rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
        ← G.obj.map_comp, ← op_comp, he]
    · have h := congrArg (fun k : ((baseChange i).obj U).left ⟶ V.left => k z)
        (map_isPullback i e).w
      have hmap := congrArg (fun k : (baseChange i).obj U ⟶ (baseChange i).obj V => k.left z) he
      change b.left (d.left z) = ((baseChange i).map e).left z at hmap
      have hv := congrArg (pullback.fst V.hom i) (hmap.symm.trans
        ((congrArg b.left hz).trans hw))
      exact (h.trans hv).trans hy
  · obtain ⟨U, e, y, hU, hy⟩ := exists_empty_neighborhood i V x hx
    have hG := Scheme.subsingleton_sections_of_isEmpty hU G
    refine ⟨U, e, y, ⟨0, hG.elim _ _⟩, hy⟩

instance [IsClosedImmersion i] : PreservesFiniteColimits (pushforward i) := by
  have : (pushforward i).PreservesEpimorphisms := ⟨fun a => epi_pushforward i a⟩
  have : (pushforward i).PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Direct image along a closed immersion is exact on the small étale site. -/
theorem map_shortExact [IsClosedImmersion i]
    {S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})} (hS : S.ShortExact) :
    (S.map (pushforward i)).ShortExact :=
  hS.map_of_exact (pushforward i)

end PhilipponEtaleClosedPushforward

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleConstantDegreeZero

universe u
variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- Continuous functions with values in the discrete coefficient group form
an étale sheaf by restriction of the fpqc sheaf of continuous functions. -/
def continuousSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ((PhilipponKummerSequence.underlying X).sheafPushforwardContinuous AddCommGrpCat
    X.smallEtaleTopology Scheme.etaleTopology).obj
    ⟨continuousMapPresheafAb A, (isSheaf_fpqcTopology_continuousMapPresheafAb A).of_le
      (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)⟩

private def constantMap : (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A) ⟶
    (continuousSheaf X A).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := fun a => ContinuousMap.const W.unop.left a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality := by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    apply ContinuousMap.ext
    intro x
    rfl

private theorem constantMap_locallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W a b hab
  by_cases h : a = b
  · subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact X.smallEtaleTopology.top_mem _
  · have hW : IsEmpty W.unop.left := ⟨fun x => h (congrArg (fun f : C(W.unop.left, A) => f x) hab)⟩
    let V : Fin 0 → X.Etale := fun _ => W.unop
    let r : ∀ i, V i ⟶ W.unop := fun _ => 𝟙 W.unop
    have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W.unop :=
      (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr (Set.eq_univ_of_forall fun x => isEmptyElim x)
    apply X.smallEtaleTopology.superset_covering _ hcover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Fin.elim0 i

private theorem constantMap_locallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W s
  change C(W.left, A) at s
  let U (a : A) : W.left.Opens := ⟨s ⁻¹' {a}, (isOpen_discrete {a}).preimage s.continuous⟩
  let V (a : A) := Scheme.Etale.mk ((U a).ι ≫ W.hom)
  let r (a : A) : V a ⟶ W := MorphismProperty.Over.homMk (U a).ι rfl
  have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨s x, ⟨⟨x, rfl⟩, rfl⟩⟩
  apply X.smallEtaleTopology.superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨a⟩
  refine ⟨a, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact x.property.symm

/-- For discrete coefficients, sheafifying constant functions gives the
small étale sheaf of continuous functions. -/
def constantSheafIso : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of A) ≅ continuousSheaf X A := by
  let J := X.smallEtaleTopology
  let G := presheafToSheaf J AddCommGrpCat.{u}
  have h := (J.W_iff_isLocallyBijective (constantMap X A)).mpr
    ⟨constantMap_locallyInjective X A, constantMap_locallySurjective X A⟩
  let : IsIso (G.map (constantMap X A)) := (J.W_iff _).mp h
  exact (asIso (G.map (constantMap X A))).trans (sheafificationIso (continuousSheaf X A)).symm

end PhilipponEtaleConstantDegreeZero

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (continuousSheaf)


namespace PhilipponEtaleClosedCover

universe u
variable {X Y Z : Scheme.{u}}
variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private def precompose (f : Y ⟶ Z) : C(Z, A) →+ C(Y, A) where
  toFun h := h.comp ⟨f, f.continuous⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem projection_naturality (f : Y ⟶ X) {U V : X.Etale} (g : U ⟶ V) :
    ((baseChange f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

/-- Restriction of continuous coefficient functions to the pullback of a
scheme morphism. -/
def restriction (i : Y ⟶ X) :
    continuousSheaf X A ⟶ (pushforward i).obj (continuousSheaf Y A) :=
  ⟨{
    app W := AddCommGrpCat.ofHom (precompose A (pullback.fst W.unop.hom i))
    naturality {U V} f := by
      apply ConcreteCategory.hom_ext
      intro s
      change C(U.unop.left, A) at s
      apply ContinuousMap.ext
      intro x
      change s (f.unop.left (pullback.fst V.unop.hom i x)) =
        s (pullback.fst U.unop.hom i (((baseChange i).map f.unop).left x))
      exact congrArg s (congrArg (fun k : (_ : Scheme) ⟶ (_ : Scheme) => k x)
        (projection_naturality i f.unop).symm)
  }⟩

end PhilipponEtaleClosedCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteLimitSubsite

universe w v v' u u'

private def Shape : Bool → Type
  | false => Discrete PEmpty.{1}
  | true => WalkingCospan

private instance (b : Bool) : Small.{w} (Shape b) := by
  cases b <;> dsimp [Shape] <;> infer_instance

private instance (b : Bool) : Category.{0} (Shape b) := by
  cases b <;> dsimp [Shape] <;> infer_instance

private instance (b : Bool) : LocallySmall.{w} (Shape b) := by
  cases b <;> dsimp [Shape] <;> infer_instance

variable {C : Type u} [Category.{v} C]

/-- Closure of a collection of objects under isomorphisms, a terminal
object and pullbacks. -/
def closure (P : ObjectProperty C) : ObjectProperty C :=
  P.limitsClosure Shape

theorem le_closure (P : ObjectProperty C) : P ≤ closure P := P.le_limitsClosure Shape

instance (P : ObjectProperty C) [LocallySmall.{w} C] [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} (closure P) :=
  inferInstanceAs (ObjectProperty.EssentiallySmall.{w} (P.limitsClosure Shape))

private instance (P : ObjectProperty C) :
    (closure P).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  P.instIsClosedUnderLimitsOfShapeLimitsClosure Shape false

private instance (P : ObjectProperty C) :
    (closure P).IsClosedUnderLimitsOfShape WalkingCospan :=
  P.instIsClosedUnderLimitsOfShapeLimitsClosure Shape true

instance (P : ObjectProperty C) [HasTerminal C] :
    HasTerminal (closure P).FullSubcategory := by infer_instance

instance (P : ObjectProperty C) [HasPullbacks C] :
    HasPullbacks (closure P).FullSubcategory := by infer_instance

instance (P : ObjectProperty C) [HasFiniteLimits C] :
    HasFiniteLimits (closure P).FullSubcategory :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance (P : ObjectProperty C) [HasFiniteLimits C] :
    PreservesFiniteLimits (closure P).ι :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

variable {D : Type u'} [Category.{v'} D]

theorem closure_maps {P : ObjectProperty C} {Q : ObjectProperty D} (F : C ⥤ D)
    [PreservesFiniteLimits F] (h : P ≤ Q.inverseImage F) :
    closure P ≤ (closure Q).inverseImage F := by
  have (b : Bool) : ((closure Q).inverseImage F).IsClosedUnderLimitsOfShape (Shape b) := by
    cases b <;> dsimp only [Shape] <;> infer_instance
  letI : (closure Q).IsClosedUnderIsomorphisms :=
    inferInstanceAs ((Q.limitsClosure Shape).IsClosedUnderIsomorphisms)
  exact ObjectProperty.limitsClosure_le (h.trans (fun _ hq => le_closure Q _ hq))

/-- A finite-limit-preserving functor acts on the small closure if it maps
the chosen generating objects into the target generating collection. -/
def restrict {P : ObjectProperty C} {Q : ObjectProperty D} (F : C ⥤ D)
    [PreservesFiniteLimits F] (h : P ≤ Q.inverseImage F) :
    (closure P).FullSubcategory ⥤ (closure Q).FullSubcategory :=
  (closure Q).lift ((closure P).ι ⋙ F) (fun U => closure_maps F h _ U.property)

instance {P : ObjectProperty C} {Q : ObjectProperty D} [HasFiniteLimits C] [HasFiniteLimits D]
    (F : C ⥤ D) [PreservesFiniteLimits F] (h : P ≤ Q.inverseImage F) :
    PreservesFiniteLimits (restrict F h) := by
  have : PreservesFiniteLimits (restrict F h ⋙ (closure Q).ι) :=
    show PreservesFiniteLimits ((closure P).ι ⋙ F) from comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (closure Q).ι

end PhilipponFiniteLimitSubsite

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponFiniteLimitSubsite
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleSmallSite

universe u
variable (X : Scheme.{u})

private def affineObjects : ObjectProperty X.Etale := fun U => IsAffine U.left

private theorem affine_in_image (U : X.Etale) (h : affineObjects X U) :
    (Scheme.AffineEtale.Spec X).essImage U := by
  letI : IsAffine U.left := h
  let e := U.left.isoSpec
  let T := Scheme.AffineEtale.mk (e.inv ≫ U.hom)
  exact ⟨T, ⟨MorphismProperty.Over.isoMk e.symm rfl⟩⟩

private instance : ObjectProperty.EssentiallySmall.{u} (affineObjects X) :=
  ObjectProperty.EssentiallySmall.of_le (affine_in_image X)

private abbrev objects := closure (affineObjects X)

/-- A universe-`u` model of a full dense subsite of the small étale site.
The subsite contains all affine étale objects and is closed under finite limits. -/
def Site : Type u := SmallModel.{u} (objects X).FullSubcategory

instance : SmallCategory (Site X) :=
  inferInstanceAs (SmallCategory (SmallModel.{u} (objects X).FullSubcategory))

private def model : (objects X).FullSubcategory ≌ Site X :=
  equivSmallModel.{u} (objects X).FullSubcategory

private instance : HasFiniteLimits (Site X) where
  out _ _ _ := Adjunction.hasLimitsOfShape_of_equivalence (model X).inverse

private abbrev incl : Site X ⥤ X.Etale := (model X).inverse ⋙ (objects X).ι

private theorem has_cover (V : X.Etale) :
    ∃ (I : Type u) (U : I → Site X) (g : ∀ j, (incl X).obj (U j) ⟶ V),
      Sieve.ofArrows (fun j => (incl X).obj (U j)) g ∈ X.smallEtaleTopology V := by
  let A := V.left.affineCover
  let W (j : A.I₀) := Scheme.Etale.mk (A.f j ≫ V.hom)
  let B (j : A.I₀) : (objects X).FullSubcategory :=
    ⟨W j, le_closure _ _ (inferInstanceAs (IsAffine (A.X j)))⟩
  let U (j : A.I₀) := (model X).functor.obj (B j)
  let e (j : A.I₀) := (objects X).ι.mapIso ((model X).unitIso.app (B j)).symm
  let h (j : A.I₀) : W j ⟶ V := MorphismProperty.Over.homMk (A.f j) rfl trivial
  let g (j : A.I₀) : (incl X).obj (U j) ⟶ V := (e j).hom ≫ h j
  refine ⟨A.I₀, U, g, (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  obtain ⟨j, y, rfl⟩ := A.exists_eq x
  let E := (Scheme.Etale.forget X ⋙ Over.forget X).mapIso (e j)
  obtain ⟨z, hz⟩ := E.hom.homeomorph.surjective y
  exact Set.mem_iUnion.mpr ⟨j, ⟨z, congrArg (A.f j) hz⟩⟩

private instance : (incl X).IsCoverDense X.smallEtaleTopology where
  is_cover V := by
    obtain ⟨I, U, g, hg⟩ := has_cover X V
    refine X.smallEtaleTopology.superset_covering ?_ hg
    rintro W _ ⟨T, a, _, ⟨j⟩, rfl⟩
    exact (Sieve.coverByImage (incl X) V).downward_closed
      (Presieve.in_coverByImage (incl X) (g j)) a

private def topology : GrothendieckTopology (Site X) :=
  (incl X).inducedTopology X.smallEtaleTopology

private theorem sheafify_small {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} := by infer_instance

private instance (priority := 2000) : HasSheafify (topology X) AddCommGrpCat.{u} :=
  sheafify_small (topology X)

private instance : (incl X).IsDenseSubsite (topology X) X.smallEtaleTopology :=
  inferInstanceAs ((incl X).IsDenseSubsite
    ((incl X).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)

private instance : (incl X).IsOneHypercoverDense.{u} (topology X) X.smallEtaleTopology :=
  Functor.IsOneHypercoverDense.of_hasPullbacks (has_cover X)

private abbrev abelianSheaves := Sheaf (topology X) AddCommGrpCat.{u}

private abbrev bigSheaves := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private def restrictSheaves : bigSheaves X ⥤ abelianSheaves X :=
  (incl X).sheafPushforwardContinuous _ _ _

private instance : (restrictSheaves X).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense (incl X) (topology X)
    X.smallEtaleTopology AddCommGrpCat.{u}

variable {X} {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

private instance finiteLimits_baseChange : PreservesFiniteLimits (baseChange i) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ i))

private instance finiteLimits_etale (Y : Scheme.{u}) : HasFiniteLimits Y.Etale :=
  inferInstanceAs (HasFiniteLimits (MorphismProperty.Over (@Etale) ⊤ Y))

private theorem affine_baseChange :
    affineObjects X ≤ (affineObjects Z).inverseImage (baseChange i) := by
  intro U hU
  have : IsAffine ((𝟭 Scheme).obj U.left) := hU
  change IsAffine (pullback U.hom i)
  exact isAffine_of_isAffineHom (pullback.fst U.hom i)

private def restrictBaseChange :
    (objects X).FullSubcategory ⥤ (objects Z).FullSubcategory :=
  restrict (baseChange i) (affine_baseChange i)

private instance : PreservesFiniteLimits (restrictBaseChange i) :=
  inferInstanceAs (PreservesFiniteLimits (restrict (baseChange i) (affine_baseChange i)))

private def smallBaseChange : Site X ⥤ Site Z :=
  (model X).inverse ⋙ restrictBaseChange i ⋙ (model Z).functor

private instance : PreservesFiniteLimits (smallBaseChange i) := by
  have : PreservesFiniteLimits (restrictBaseChange i ⋙ (model Z).functor) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

private def changeInclIso : smallBaseChange i ⋙ incl Z ≅ incl X ⋙ baseChange i :=
  NatIso.ofComponents
    (fun U => (objects Z).ι.mapIso
      ((model Z).unitIso.app ((restrictBaseChange i).obj ((model X).inverse.obj U))).symm)
    (fun g => by
      simp only [Functor.comp_map, Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp]
      apply congrArg
      exact (model Z).unitIso.inv.naturality ((restrictBaseChange i).map ((model X).inverse.map g)))

private theorem coverPreserving_of_iso {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} (e : F ≅ G) (hF : CoverPreserving J K F) : CoverPreserving J K G where
  cover_preserve {U S} hS := by
    apply K.superset_covering _ (K.pullback_stable (e.inv.app U) (hF.cover_preserve hS))
    rintro W a ⟨V, g, b, hg, hb⟩
    refine ⟨V, g, b ≫ e.hom.app V, hg, ?_⟩
    rw [Category.assoc, ← e.hom.naturality, ← Category.assoc, ← hb, Category.assoc]
    simp

private instance : (smallBaseChange i).IsContinuous (topology X) (topology Z) := by
  have : RepresentablyFlat (smallBaseChange i) := flat_of_preservesFiniteLimits _
  apply Functor.isContinuous_iff_coverPreserving.mpr
  constructor
  intro V S hS
  rw [← (incl Z).functorPushforward_mem_iff (topology Z) Z.smallEtaleTopology,
    ← Sieve.functorPushforward_comp]
  have H : CoverPreserving (topology X) Z.smallEtaleTopology (incl X ⋙ baseChange i) := by
    constructor
    intro W R hR
    rw [Sieve.functorPushforward_comp]
    exact (PhilipponEtaleBaseChangeComparison.coverPreserving i).cover_preserve
      (((incl X).functorPushforward_mem_iff (topology X) X.smallEtaleTopology).mpr hR)
  exact (coverPreserving_of_iso (changeInclIso i).symm H).cover_preserve hS

private def smallPushforward : abelianSheaves Z ⥤ abelianSheaves X :=
  (smallBaseChange i).sheafPushforwardContinuous _ _ _

private def changeSheavesIso :
    PhilipponEtaleClosedPushforward.pushforward i ⋙ restrictSheaves X ≅
      restrictSheaves Z ⋙ smallPushforward i := by
  letI := Functor.isContinuous_comp (smallBaseChange i) (incl Z)
    (topology X) (topology Z) Z.smallEtaleTopology
  exact Functor.sheafPushforwardContinuousComp' (changeInclIso i).symm _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

private instance smallKan (P : (Site X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallBaseChange i).op.HasLeftKanExtension P := by
  have (U : (Site Z)ᵒᵖ) :
      HasColimitsOfShape (CostructuredArrow (smallBaseChange i).op U) AddCommGrpCat.{u} :=
    inferInstance
  infer_instance

private abbrev smallLan : ((Site X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
    ((Site Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (smallBaseChange i).op.lan

private def smallPullback : abelianSheaves X ⥤ abelianSheaves Z := by
  let F : abelianSheaves X ⥤ ((Site X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    sheafToPresheaf (topology X) AddCommGrpCat.{u}
  let G : ((Site Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ abelianSheaves Z :=
    presheafToSheaf (topology Z) AddCommGrpCat.{u}
  exact F ⋙ smallLan i ⋙ G

private def smallAdjunction : smallPullback i ⊣ smallPushforward i :=
  (((smallBaseChange i).op.lanAdjunction AddCommGrpCat.{u}).comp
    (sheafificationAdjunction (topology Z) AddCommGrpCat.{u})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (topology X) AddCommGrpCat.{u}) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

private instance : PreservesFiniteLimits (smallPullback i) := by
  have : RepresentablyFlat (smallBaseChange i) := flat_of_preservesFiniteLimits _
  have : ReflectsLimits (forget AddCommGrpCat.{u}) := reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits (smallLan i) :=
    lan_preservesFiniteLimits_of_flat (C := Site X) (D := Site Z) _ (smallBaseChange i)
  have : PreservesFiniteLimits (smallLan i ⋙ presheafToSheaf (topology Z) AddCommGrpCat.{u}) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

private def pullbackSheaves : bigSheaves X ⥤ bigSheaves Z :=
  (restrictSheaves X ⋙ smallPullback i) ⋙ (restrictSheaves Z).asEquivalence.inverse

private instance : PreservesFiniteLimits (pullbackSheaves i) := by
  have : PreservesFiniteLimits (restrictSheaves X ⋙ smallPullback i) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

private def pushforwardIso :
    restrictSheaves Z ⋙ smallPushforward i ⋙ (restrictSheaves X).asEquivalence.inverse ≅
      PhilipponEtaleClosedPushforward.pushforward i :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (changeSheavesIso i).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictSheaves X).asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor _

private def pullbackAdjunction :
    pullbackSheaves i ⊣ PhilipponEtaleClosedPushforward.pushforward i :=
  Adjunction.ofNatIsoRight
    (((restrictSheaves X).asEquivalence.toAdjunction.comp (smallAdjunction i)).comp
      (restrictSheaves Z).asEquivalence.symm.toAdjunction)
    (pushforwardIso i)

/-- Direct image by a closed immersion carries injective étale abelian
sheaves to injective étale abelian sheaves. -/
instance : (PhilipponEtaleClosedPushforward.pushforward i).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (pullbackAdjunction i)

end PhilipponEtaleSmallSite

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponExtComparison

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {Q : C} {P : D} (p : P ⟶ R.obj Q)

/-- Apply an exact functor to Ext, then precompose with the comparison map. -/
def comparison (M : C) (n : ℕ) : Ext Q M n →+ Ext P (R.obj M) n :=
  ((Ext.mk₀ p).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom Q M n)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

private theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

private theorem comparison_post {M N : C} (a : M ⟶ N) (n : ℕ) (x : Ext Q M n) :
    comparison R p N n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (comparison R p M n x).comp (Ext.mk₀ (R.map a)) (add_zero n) := by
  rw [comparison_comp, Ext.mapExactFunctor_mk₀]

/-- A Hom comparison extends to all Ext degrees when the exact functor
also preserves injectives. -/
theorem comparison_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (h : ∀ M : C, Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (n : ℕ) (M : C) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero =>
      have hz : (comparison R p M 0 : Ext Q M 0 → Ext P (R.obj M) 0) =
          fun x => Ext.mk₀ (p ≫ R.map (Ext.addEquiv₀ x)) := by
        funext x
        obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Q M).surjective x
        rw [show Ext.addEquiv₀ (Ext.mk₀ a) = a from Ext.addEquiv₀.apply_symm_apply a]
        exact comparison_mk₀ R p a
      rw [hz]
      exact (Ext.mk₀_bijective _ _).comp ((h M).comp Ext.addEquiv₀.bijective)
  | succ n ih =>
      let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M))
        (cokernel.condition (Injective.ι M))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι M) }
      have hSR := hS.map_of_exact R
      have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
      have : Injective (S.map R).X₂ := R.injective_obj_of_injective ‹Injective S.X₂›
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x
          (Ext.eq_zero_of_injective _) (n₀ := n) rfl
        have hzero : (comparison R p S.X₃ n y).comp hSR.extClass rfl = 0 := by
          rw [← comparison_boundary R p hS n y, hy]
          exact hx'
        obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₃ P hSR _ rfl hzero
        obtain ⟨z, hz⟩ := (ih S.X₂).surjective z'
        have hyz : z.comp (Ext.mk₀ S.g) (add_zero n) = y := (ih S.X₃).injective (by
          rw [comparison_post, hz]
          exact hz')
        rw [← hy, ← hyz, Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      · intro x'
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x'
          (Ext.eq_zero_of_injective _) (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

end PhilipponExtComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtaleClosedCohomology

universe u
variable {X Z : Scheme.{u}} (i : Z ⟶ X)

private abbrev terminal (Y : Scheme.{u}) : Y.Etale := Scheme.Etale.mk (𝟙 Y)

private def isTerminal (Y : Scheme.{u}) : IsTerminal (terminal Y) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal

private def terminalIso : (baseChange i).obj (terminal X) ≅ terminal Z := by
  have : PreservesFiniteLimits (baseChange i) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ i))
  exact (IsTerminal.isTerminalObj (baseChange i) _ (isTerminal X)).uniqueUpToIso (isTerminal Z)

private abbrev constantIntegers (Y : Scheme.{u}) :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

private def constantSections (Y : Scheme.{u}) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (constantIntegers Y ⟶ F) ≃ F.obj.obj (op (terminal Y)) :=
  ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} (isTerminal Y)).homEquiv _ _).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

private theorem constantSections_map {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
    (a : F ⟶ G) (s : constantIntegers Y ⟶ F) :
    constantSections Y G (s ≫ a) = a.hom.app (op (terminal Y)) (constantSections Y F s) := by
  unfold constantSections
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} (isTerminal Y)).homEquiv _ _ (s ≫ a)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private def comparisonArrow : constantIntegers X ⟶ (pushforward i).obj (constantIntegers Z) :=
  (constantSections X ((pushforward i).obj (constantIntegers Z))).symm
    ((constantIntegers Z).obj.map (terminalIso i).hom.op
      (constantSections Z (constantIntegers Z) (𝟙 _)))

private theorem comparisonArrow_bijective (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (fun a : constantIntegers Z ⟶ F => comparisonArrow i ≫ (pushforward i).map a) := by
  let e := constantSections X ((pushforward i).obj F)
  let d := (F.obj.mapIso (terminalIso i).op).addCommGroupIsoToAddEquiv
  let c := constantSections Z F
  have h : (fun a : constantIntegers Z ⟶ F => comparisonArrow i ≫ (pushforward i).map a) =
      e.symm ∘ d ∘ c := by
    funext a
    apply e.injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    change constantSections X ((pushforward i).obj F)
        (comparisonArrow i ≫ (pushforward i).map a) = F.obj.map (terminalIso i).hom.op (c a)
    rw [constantSections_map]
    unfold comparisonArrow
    rw [Equiv.apply_symm_apply]
    change a.hom.app _ ((constantIntegers Z).obj.map (terminalIso i).hom.op _) = _
    rw [NatTrans.naturality_apply, ← constantSections_map, Category.id_comp]
  rw [h]
  exact e.symm.bijective.comp (d.bijective.comp c.bijective)

/-- Direct image along a closed immersion preserves cohomology in every degree. -/
def cohomologyEquiv [IsClosedImmersion i]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    F.H q ≃+ ((pushforward i).obj F).H q := by
  exact AddEquiv.ofBijective
    (PhilipponExtComparison.comparison (pushforward i) (comparisonArrow i) F q)
    (PhilipponExtComparison.comparison_bijective (pushforward i) (comparisonArrow i)
      (comparisonArrow_bijective i) q F)

end PhilipponEtaleClosedCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleClosedCohomology (cohomologyEquiv)
open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso)


namespace PhilipponEtaleClosedConstant

universe u
variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [Surjective i]
  (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private instance isIso_restriction : IsIso (restriction A i) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let p := pullback.fst W.unop.hom i
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst W.unop.hom i))
  have : Surjective p := inferInstanceAs (Surjective (pullback.fst W.unop.hom i))
  let e := p.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective p.surjective
  let r : C(W.unop.left, A) → C(↥(pullback W.unop.hom i), A) :=
    fun s => s.comp ⟨p, p.continuous⟩
  change Function.Bijective r
  constructor
  · intro f g h
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, rfl⟩ := p.surjective x
    exact congrArg (fun s : C(↥(pullback W.unop.hom i), A) => s y) h
  · intro f
    refine ⟨f.comp ⟨e.symm, e.symm.continuous⟩, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact congrArg f (e.symm_apply_apply y)

/-- Constant étale cohomology is invariant under a surjective closed
immersion. This comparison uses the homeomorphism on every étale object
and the closed-immersion cohomology comparison. -/
def constantCohomologyEquiv (q : ℕ) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).H q ≃+
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).H q := by
  let eX := (Sheaf.functorH X.smallEtaleTopology q).mapIso
    (constantSheafIso X A ≪≫ asIso (restriction A i))
  let eY := (Sheaf.functorH Y.smallEtaleTopology q).mapIso (constantSheafIso Y A)
  exact eX.addCommGroupIsoToAddEquiv.trans
    ((cohomologyEquiv i (continuousSheaf Y A) q).symm.trans eY.addCommGroupIsoToAddEquiv.symm)

end PhilipponEtaleClosedConstant

end

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso)

theorem solution
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [Surjective i]
    (A : Type u) [AddCommGroup A] (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) ↔ Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) := by 
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact (PhilipponEtaleClosedConstant.constantCohomologyEquiv i A q).toEquiv.finite_iff

end
