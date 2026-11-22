-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T07:16:00.394943+00:00
-- url     : https://prove2.me/submissions/c08ab459-04bb-4106-864d-f5e959dd5fa2

import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Data.Finite.Sigma
import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_integral_zariski_refinement_of_surjective_etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponIntegralEtaleRefinement
universe u
variable {A B S T : Scheme.{u}}
def LocallyFactorsThrough (f : A ⟶ S) (g : B ⟶ S) : Prop :=
  ∀ a : A, ∃ (W : Scheme.{u}) (i : W ⟶ A), IsOpenImmersion i ∧ a ∈ Set.range i ∧
    ∃ h : W ⟶ B, h ≫ g = i ≫ f

theorem LocallyFactorsThrough.precomp {f : A ⟶ S} {g : B ⟶ S}
    (hf : LocallyFactorsThrough f g) (r : T ⟶ A) : LocallyFactorsThrough (r ≫ f) g := by
  intro t
  obtain ⟨W, i, hi, ht, h, hh⟩ := hf (r t)
  have hp : t ∈ Set.range (pullback.fst r i) := by
    rw [Scheme.Pullback.range_fst]
    exact ht
  refine ⟨_, pullback.fst r i, inferInstance, hp, pullback.snd r i ≫ h, ?_⟩
  rw [Category.assoc, hh, pullback.condition_assoc]

theorem LocallyFactorsThrough.postcomp {f : A ⟶ S} {g : B ⟶ S}
    (hf : LocallyFactorsThrough f g) (r : S ⟶ T) :
    LocallyFactorsThrough (f ≫ r) (g ≫ r) := by
  intro a
  obtain ⟨W, i, hi, ha, h, hh⟩ := hf a
  exact ⟨W, i, hi, ha, h, by rw [← Category.assoc, hh, Category.assoc]⟩

end PhilipponIntegralEtaleRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponIntegralEtaleRefinement (LocallyFactorsThrough)

noncomputable section

namespace PhilipponEtaleRefinementLimit

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {S X : Scheme.{u}}
  (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
  (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (k : i ⟶ j), IsAffineHom (D.map k)]
  [∀ i : I, QuasiSeparatedSpace (D.obj i)]

omit [IsCofiltered I] [∀ {i j : I} (k : i ⟶ j), IsAffineHom (D.map k)]
  [∀ i : I, QuasiSeparatedSpace (D.obj i)] in
private theorem base_naturality {i j : I} (k : i ⟶ j) :
    D.map k ≫ t.app j = t.app i :=
  (t.naturality k).trans (Category.comp_id _)

include hc in
private theorem exists_open_factor_near (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (h : LocallyFactorsThrough p f) (x : c.pt) :
    ∃ (i : I) (V : (D.obj i).Opens), c.π.app i x ∈ V ∧
      ∃ g : V.toScheme ⟶ X, g ≫ f = V.ι ≫ t.app i := by
  obtain ⟨W, a, ha, hx, b, hb⟩ := h x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUa⟩ := c.pt.isBasis_affineOpens.exists_subset_of_mem_open
    hx a.isOpenEmbedding.isOpenMap.isOpen_range
  obtain ⟨i, V, hV, hVU⟩ := exists_isAffineOpen_preimage_eq D c hc U hU
  let C := opensCone D c i V
  let E := opensDiagram D i V
  let τ : E ⟶ (Functor.const (Over i)).obj S :=
    opensDiagramι D i V ≫ (Over.forget i).whiskerLeft t
  let U' := c.π.app i ⁻¹ᵁ V
  have hSubset : Set.range U'.ι ⊆ Set.range a := by
    rw [Scheme.Opens.range_ι, show U' = U from hVU]
    exact hUa
  let r := IsOpenImmersion.lift a U'.ι hSubset
  let g : C.pt ⟶ X := r ≫ b
  have hg : g ≫ f = U'.ι ≫ p := by
    rw [show g = r ≫ b from rfl, Category.assoc, hb, ← Category.assoc,
      IsOpenImmersion.lift_fac]
  have hτ : C.π ≫ τ = (Functor.const _).map (g ≫ f) := by
    ext j
    change C.π.app j ≫ ((D.map j.hom ⁻¹ᵁ V).ι ≫ t.app j.left) = g ≫ f
    rw [hg, ← Category.assoc, show C.π.app j ≫ (D.map j.hom ⁻¹ᵁ V).ι =
      U'.ι ≫ c.π.app j.left from Scheme.Hom.resLE_comp_ι _ _, Category.assoc, hp]
  have (j : Over i) : IsAffine (E.obj j) := hV.preimage (D.map j.hom)
  have (j : Over i) : CompactSpace (E.obj j) := inferInstance
  have (j : Over i) : QuasiSeparatedSpace (E.obj j) := inferInstance
  have {j k : Over i} (φ : j ⟶ k) : IsAffineHom (E.map φ) :=
    inferInstanceAs (IsAffineHom ((opensDiagram D i V).map φ))
  obtain ⟨j, d, _, hd⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation E τ f C
      (isLimitOpensCone D c hc i V) g hτ
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ V, ?_, d, hd⟩
  change (c.π.app j.left ≫ D.map j.hom) x ∈ V
  rw [c.w]
  change x ∈ U'
  rwa [show U' = U from hVU]

include hc in
/-- A Zariski-local factorization through a locally finitely presented
morphism descends to one stage of an inverse system of qcqs schemes with
affine transition maps. -/
theorem exists_locallyFactorsThrough_of_limit [∀ i : I, CompactSpace (D.obj i)]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (h : LocallyFactorsThrough p f) :
    ∃ j, LocallyFactorsThrough (t.app j) f := by
  classical
  have near (x : c.pt) := exists_open_factor_near D t c hc f p hp h x
  choose i V hx g hg using near
  let U (x : c.pt) : c.pt.Opens := c.π.app (i x) ⁻¹ᵁ V x
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set c.pt))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let J := F.image i
  let j := IsCofiltered.inf J ∅
  let a (x : ↥F) : j ⟶ i x.val :=
    IsCofiltered.infTo J ∅ (Finset.mem_image_of_mem i x.property)
  let W (x : ↥F) : (D.obj j).Opens := D.map (a x) ⁻¹ᵁ V x.val
  have hW : c.π.app j ⁻¹ᵁ (⨆ x, W x) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
    change c.π.app j x ∈ ⨆ y, W y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ?_⟩
    change (c.π.app j ≫ D.map (a ⟨y, hy⟩)) x ∈ V y
    rw [c.w]
    exact hxy
  obtain ⟨k, m, hm⟩ := exists_map_eq_top D c hc _ hW
  refine ⟨k, fun x => ?_⟩
  have hmem : D.map m x ∈ ⨆ y, W y := hm.ge (Set.mem_univ x)
  obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  let P : (D.obj k).Opens := D.map (m ≫ a y) ⁻¹ᵁ V y.val
  have hx' : x ∈ P := by
    change D.map (m ≫ a y) x ∈ V y.val
    rw [D.map_comp, Scheme.Hom.comp_apply]
    exact hy
  let r := D.map (m ≫ a y) ∣_ V y.val
  refine ⟨P.toScheme, P.ι, inferInstance, ⟨⟨x, hx'⟩, rfl⟩, r ≫ g y.val, ?_⟩
  rw [Category.assoc, hg, ← Category.assoc r, show r ≫ (V y.val).ι =
    P.ι ≫ D.map (m ≫ a y) from morphismRestrict_ι _ _, Category.assoc, base_naturality]

include hc in
/-- If a surjective cover is a cofiltered limit of finite schemes over the
base, any Zariski-local factorization descends to a finite surjective stage. -/
theorem exists_finite_refinement_of_limit [SpectralSpace S] [∀ i : I, IsFinite (t.app i)]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (p : c.pt ⟶ S) [Surjective p]
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (h : LocallyFactorsThrough p f) :
    ∃ (P : Scheme.{u}) (q : P ⟶ S), IsFinite q ∧ Surjective q ∧
      LocallyFactorsThrough q f := by
  have (i : I) : CompactSpace (D.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (Y := S) (t.app i)
  obtain ⟨j, hj⟩ := exists_locallyFactorsThrough_of_limit D t c hc f p hp h
  refine ⟨D.obj j, t.app j, inferInstance, ⟨fun y => ?_⟩, hj⟩
  obtain ⟨x, hx⟩ := (inferInstance : Surjective p).surj y
  exact ⟨c.π.app j x, (congrArg (fun α : c.pt ⟶ S => α x) (hp j)).trans hx⟩

end PhilipponEtaleRefinementLimit


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponIntegralEtaleRefinement (LocallyFactorsThrough)

noncomputable section

namespace PhilipponEtaleRefinementAffine

universe u

section Algebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

private abbrev stage (s : Finset A) := Algebra.adjoin R (s : Set A)

/-- The rings generated by finite subsets of an algebra form a directed
diagram with inclusion as transition maps. -/
private def finiteSubalgebraDiagram : Finset A ⥤ CommRingCat.{u} where
  obj s := CommRingCat.of (stage R A s)
  map h := CommRingCat.ofHom (Subalgebra.inclusion
    (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom h)))).toRingHom
  map_id s := by ext x; rfl
  map_comp f g := by ext x; rfl

private def finiteSubalgebraCocone : Cocone (finiteSubalgebraDiagram R A) where
  pt := CommRingCat.of A
  ι.app s := CommRingCat.ofHom (stage R A s).val.toRingHom
  ι.naturality _ _ f := by ext x; rfl

private def structureMaps : (Functor.const (Finset A)).obj (CommRingCat.of R) ⟶
    finiteSubalgebraDiagram R A where
  app s := CommRingCat.ofHom (algebraMap R (stage R A s))
  naturality _ _ f := by ext x; rfl

private def finiteSubalgebraIsColimit : IsColimit (finiteSubalgebraCocone R A) := by
  classical
  let F := finiteSubalgebraDiagram R A
  let forgetRing := forget CommRingCat.{u}
  have : ReflectsColimit F forgetRing := reflectsColimit_of_reflectsIsomorphisms F forgetRing
  apply isColimitOfReflects forgetRing
  apply Types.FilteredColimit.isColimitOf
  · intro a
    let s : Finset A := {a}
    refine ⟨s, ⟨a, Algebra.subset_adjoin ?_⟩, rfl⟩
    simp [s]
  · intro s t a b h
    let v := s ∪ t
    have hs : s ≤ v := Finset.subset_union_left
    have ht : t ≤ v := Finset.subset_union_right
    refine ⟨v, homOfLE hs, homOfLE ht, ?_⟩
    exact Subtype.ext h

end Algebra

/-- A Zariski-local factorization over an affine base descends to the
spectrum of a finitely generated subalgebra. -/
theorem exists_fg_subalgebra_refinement
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (h : LocallyFactorsThrough (Spec.map (CommRingCat.ofHom (algebraMap R A))) f) :
    ∃ C : Subalgebra R A, C.FG ∧
      LocallyFactorsThrough (Spec.map (CommRingCat.ofHom (algebraMap R C))) f := by
  classical
  let F := finiteSubalgebraDiagram R A
  let D := F.op ⋙ Scheme.Spec
  let T := (finiteSubalgebraCocone R A).op
  let c := Scheme.Spec.mapCone T
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) :=
    { app := fun i => Spec.map ((structureMaps R A).app i.unop)
      naturality := fun i j g => by
        change Spec.map (F.map g.unop) ≫ Spec.map ((structureMaps R A).app j.unop) =
          Spec.map ((structureMaps R A).app i.unop) ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1 }
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (finiteSubalgebraIsColimit R A).op
  have {i j : (Finset A)ᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map (F.map g.unop)))
  have (i : (Finset A)ᵒᵖ) : QuasiSeparatedSpace (D.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (stage R A i.unop))))
  have (i : (Finset A)ᵒᵖ) : CompactSpace (D.obj i) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum (stage R A i.unop)))
  have hp (i : (Finset A)ᵒᵖ) : c.π.app i ≫ t.app i =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map ((finiteSubalgebraCocone R A).ι.app i.unop) ≫
      Spec.map ((structureMaps R A).app i.unop) = _
    rw [← Spec.map_comp]
    congr 1
  obtain ⟨i, hi⟩ :=
    PhilipponEtaleRefinementLimit.exists_locallyFactorsThrough_of_limit D t c hc f _ hp h
  exact ⟨stage R A i.unop, Subalgebra.fg_def.mpr ⟨_, i.unop.finite_toSet, rfl⟩, hi⟩

end PhilipponEtaleRefinementAffine

set_option autoImplicit false

open scoped Pointwise

namespace PhilipponIntegralSubalgebraLocalization

section ChangeBase

variable {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra R' S'] [IsScalarTower R R' S']

/-- After extending scalars, the image of a generated subalgebra and
the image of its generators generate the same subalgebra. -/
theorem adjoin_image_adjoin (f : S →ₐ[R] S') (s : Set S) :
    Algebra.adjoin R' (f '' (Algebra.adjoin R s : Set S)) = Algebra.adjoin R' (f '' s) := by
  apply le_antisymm
  · let B := Algebra.adjoin R' (f '' s)
    have hB : Algebra.adjoin R s ≤ (B.restrictScalars R).comap f :=
      Algebra.adjoin_le (fun x hx => Algebra.subset_adjoin (Set.mem_image_of_mem _ hx))
    apply Algebra.adjoin_le
    rintro _ ⟨x, hx, rfl⟩
    exact hB hx
  · exact Algebra.adjoin_mono (Set.image_mono Algebra.subset_adjoin)

/-- Finitely generated subalgebras stay finitely generated after
applying a map and adjoining the new base ring. -/
theorem fg_adjoin_image (f : S →ₐ[R] S') (C : Subalgebra R S) (hC : C.FG) :
    (Algebra.adjoin R' (f '' (C : Set S))).FG := by
  obtain ⟨s, hs, h⟩ := Subalgebra.fg_def.mp hC
  refine Subalgebra.fg_def.mpr ⟨f '' s, hs.image f, ?_⟩
  rw [← h, adjoin_image_adjoin]

end ChangeBase

section RingMaps

variable {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R' S']
  (a : R →+* R') (f : S →+* S')
  (h : ∀ r : R, f (algebraMap R S r) = algebraMap R' S' (a r))

include h in
/-- Scalar-compatible ring maps preserve generation after adjoining the
new coefficient ring. -/
theorem adjoin_ringHom_image_adjoin (s : Set S) :
    Algebra.adjoin R' (f '' (Algebra.adjoin R s : Set S)) = Algebra.adjoin R' (f '' s) := by
  let : Algebra R R' := a.toAlgebra
  let : Algebra R S' := ((algebraMap R' S').comp a).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  let g : S →ₐ[R] S' := ⟨f, h⟩
  exact adjoin_image_adjoin g s

include h in
theorem fg_adjoin_ringHom_image (C : Subalgebra R S) (hC : C.FG) :
    (Algebra.adjoin R' (f '' (C : Set S))).FG := by
  obtain ⟨s, hs, hGen⟩ := Subalgebra.fg_def.mp hC
  refine Subalgebra.fg_def.mpr ⟨f '' s, hs.image f, ?_⟩
  rw [← hGen, adjoin_ringHom_image_adjoin a f h]

end RingMaps

section Localization

variable {R S R' S' : Type*}
  [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R S'] [Algebra R' S']
  [IsScalarTower R S S'] [IsScalarTower R R' S']
  (M : Submonoid R) [IsLocalization M R'] [IsLocalization (M.map (algebraMap R S)) S']

omit [IsLocalization (M.map (algebraMap R S)) S'] in
private theorem map_mem_adjoin_of_smul_mem (C : Subalgebra R S) (x : S)
    (m : M) (hm : m • x ∈ C) :
    algebraMap S S' x ∈ Algebra.adjoin R' (algebraMap S S' '' (C : Set S)) := by
  let A := Algebra.adjoin R' (algebraMap S S' '' (C : Set S))
  obtain ⟨e, he⟩ := IsLocalization.map_units R' m
  have h1 : algebraMap S S' (m • x) ∈ A :=
    Algebra.subset_adjoin (Set.mem_image_of_mem _ hm)
  have h2 : algebraMap R' S' (↑e⁻¹ : R') ∈ A := A.algebraMap_mem _
  have he' : algebraMap S S' (m • x) = algebraMap R' S' (↑e : R') * algebraMap S S' x := by
    rw [Submonoid.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S,
      IsScalarTower.algebraMap_apply R R', ← he]
  refine (show algebraMap R' S' (↑e⁻¹ : R') * algebraMap S S' (m • x) =
      algebraMap S S' x by rw [he', ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]) ▸
    A.mul_mem h2 h1

/-- A section belongs to a localized subalgebra exactly when some
denominator multiple belongs to the original subalgebra. -/
theorem mem_localized_adjoin_iff (C : Subalgebra R S) (x : S) :
    algebraMap S S' x ∈ Algebra.adjoin R' (algebraMap S S' '' (C : Set S)) ↔
      ∃ m : M, m • x ∈ C := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := multiple_mem_adjoin_of_mem_localization_adjoin M R' _ _ hx
    let f := IsScalarTower.toAlgHom R S S'
    have hAdjoin : Algebra.adjoin R (algebraMap S S' '' (C : Set S)) = C.map f := by
      change Algebra.adjoin R (f '' (C : Set S)) = C.map f
      rw [Algebra.adjoin_image, Algebra.adjoin_eq]
    rw [hAdjoin] at hm
    obtain ⟨y, hy, hxy⟩ := Subalgebra.mem_map.mp hm
    have hEq : algebraMap S S' y = algebraMap S S' (m • x) := by
      change algebraMap S S' y = (m : R) • algebraMap S S' x at hxy
      change algebraMap S S' y = algebraMap S S' ((m : R) • x)
      simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S] using hxy
    obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists (M.map (algebraMap R S)) S').mp hEq
    obtain ⟨n, hn, heq⟩ := d.property
    refine ⟨⟨n, hn⟩ * m, ?_⟩
    change (n * (m : R)) • x ∈ C
    rw [mul_smul, Algebra.smul_def]
    have hd' : algebraMap R S n * y = algebraMap R S n * ((m : R) • x) := by
      change (d : S) * y = (d : S) * ((m : R) • x) at hd
      rwa [← heq] at hd
    rw [← hd']
    exact C.mul_mem (C.algebraMap_mem n) hy
  · rintro ⟨m, hm⟩
    exact map_mem_adjoin_of_smul_mem M C x m hm

/-- The subalgebra generated by the image of `C` over the localized
base ring, with its natural map from `C`. -/
abbrev localizedSubalgebra (C : Subalgebra R S) : Subalgebra R' S' :=
  Algebra.adjoin R' (algebraMap S S' '' (C : Set S))

def localizedSubalgebraMap (C : Subalgebra R S) :
    C →+* localizedSubalgebra (R' := R') (S' := S') C where
  toFun x := ⟨algebraMap S S' x.val, Algebra.subset_adjoin (Set.mem_image_of_mem _ x.property)⟩
  map_one' := Subtype.ext (map_one (algebraMap S S'))
  map_mul' x y := Subtype.ext (map_mul (algebraMap S S') x.val y.val)
  map_zero' := Subtype.ext (map_zero (algebraMap S S'))
  map_add' x y := Subtype.ext (map_add (algebraMap S S') x.val y.val)

/-- The base change of a subalgebra to a localization is the localization
of the subalgebra itself, including when the ambient map has a kernel. -/
theorem isLocalization_localizedSubalgebra (C : Subalgebra R S) :
    letI := (localizedSubalgebraMap (R' := R') (S' := S') C).toAlgebra
    IsLocalization (M.map (algebraMap R C)) (localizedSubalgebra (R' := R') (S' := S') C) := by
  let L := localizedSubalgebra (R' := R') (S' := S') C
  let : Algebra C L := (localizedSubalgebraMap (R' := R') (S' := S') C).toAlgebra
  change IsLocalization (M.map (algebraMap R C)) L
  refine (isLocalization_iff (M.map (algebraMap R C)) L).mpr ⟨?_, ?_, ?_⟩
  · intro d
    obtain ⟨m, hm, hmd⟩ := d.property
    obtain ⟨e, he⟩ := IsLocalization.map_units R' (⟨m, hm⟩ : M)
    have hd : algebraMap C L d = algebraMap R' L (↑e : R') := by
      apply Subtype.ext
      change algebraMap S S' ((d.val : C) : S) = algebraMap R' S' (↑e : R')
      rw [← hmd]
      change algebraMap S S' (algebraMap R S m) = algebraMap R' S' (↑e : R')
      rw [← IsScalarTower.algebraMap_apply R S, IsScalarTower.algebraMap_apply R R', ← he]
    exact hd.symm ▸ e.isUnit.map (algebraMap R' L)
  · intro z
    obtain ⟨m, hm⟩ := multiple_mem_adjoin_of_mem_localization_adjoin M R' _ z.val z.property
    let f := IsScalarTower.toAlgHom R S S'
    have hf : Algebra.adjoin R (algebraMap S S' '' (C : Set S)) = C.map f := by
      change Algebra.adjoin R (f '' (C : Set S)) = C.map f
      rw [Algebra.adjoin_image, Algebra.adjoin_eq]
    rw [hf] at hm
    obtain ⟨y, hy, he⟩ := Subalgebra.mem_map.mp hm
    let d : M.map (algebraMap R C) := ⟨algebraMap R C (m : R), ⟨m, m.property, rfl⟩⟩
    refine ⟨(⟨y, hy⟩, d), Subtype.ext ?_⟩
    change z.val * algebraMap S S' (algebraMap R S (m : R)) = algebraMap S S' y
    change algebraMap S S' y = (m : R) • z.val at he
    rw [← IsScalarTower.algebraMap_apply R S, mul_comm, ← Algebra.smul_def]
    exact he.symm
  · intro x y he
    have hxy : algebraMap S S' x.val = algebraMap S S' y.val :=
      congrArg Subtype.val he
    obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists (M.map (algebraMap R S)) S').mp hxy
    obtain ⟨m, hm, hd'⟩ := d.property
    refine ⟨⟨algebraMap R C m, ⟨m, hm, rfl⟩⟩, Subtype.ext ?_⟩
    change algebraMap R S m * x.val = algebraMap R S m * y.val
    rwa [hd']

/-- A specified subalgebra on the localized chart has the localization
algebra structure as soon as it is generated by the restricted sections. -/
theorem isLocalization_of_eq_localizedSubalgebra (C : Subalgebra R S)
    (D : Subalgebra R' S') [A : Algebra C D]
    (hD : localizedSubalgebra (R' := R') (S' := S') C = D)
    (hMap : ∀ x : C, (algebraMap C D x).val = algebraMap S S' x.val) :
    IsLocalization (M.map (algebraMap R C)) D := by
  subst D
  let B : Algebra C (localizedSubalgebra (R' := R') (S' := S') C) :=
    (localizedSubalgebraMap (R' := R') (S' := S') C).toAlgebra
  have h : A = B := Algebra.algebra_ext _ _ (fun x => Subtype.ext (hMap x))
  rw [h]
  exact isLocalization_localizedSubalgebra M C

end Localization

section FiniteFamily

variable {ι R S : Type*} [Finite ι] [CommRing R] [CommRing S] [Algebra R S]
  {R' S' : ι → Type*} [∀ i, CommRing (R' i)] [∀ i, CommRing (S' i)]
  [∀ i, Algebra R (R' i)] [∀ i, Algebra S (S' i)] [∀ i, Algebra R (S' i)]
  [∀ i, Algebra (R' i) (S' i)] [∀ i, IsScalarTower R S (S' i)]
  [∀ i, IsScalarTower R (R' i) (S' i)]
  (r : ι → R) [∀ i, IsLocalization.Away (r i) (R' i)]
  [∀ i, IsLocalization.Away (algebraMap R S (r i)) (S' i)]

omit [Finite ι] in
/-- Membership in a subalgebra can be checked after localization on a
principal open cover of the base. -/
theorem mem_iff_mem_on_principal_cover (hSpan : Ideal.span (Set.range r) = ⊤)
    (C : Subalgebra R S) (x : S) :
    x ∈ C ↔ ∀ i, algebraMap S (S' i) x ∈
      localizedSubalgebra (R' := R' i) (S' := S' i) C := by
  constructor
  · exact fun hx i => Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  · intro h
    change x ∈ C.toSubmodule
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hSpan
    intro a
    obtain ⟨i, hi⟩ := a.property
    have hLoc : IsLocalization ((Submonoid.powers (r i)).map (algebraMap R S)) (S' i) := by
      rw [Submonoid.map_powers]
      infer_instance
    obtain ⟨m, hm⟩ := (mem_localized_adjoin_iff (R' := R' i)
      (Submonoid.powers (r i)) C x).mp (h i)
    obtain ⟨n, hn⟩ := m.property
    refine ⟨n, ?_⟩
    change r i ^ n = (m : R) at hn
    change (a.val ^ n) • x ∈ C
    change (m : R) • x ∈ C at hm
    rwa [← hi, hn]

/-- Finitely generated subalgebras on finitely many principal opens of an
affine scheme extend simultaneously when membership on each overlap can be
cleared by a power of the corresponding denominator. -/
theorem exists_fg_subalgebra_of_compatible_localizations
    (C : ∀ i, Subalgebra (R' i) (S' i)) (hfg : ∀ i, (C i).FG)
    (hCompat : ∀ i j (x : S), algebraMap S (S' i) x ∈ C i →
      ∃ n : ℕ, algebraMap S (S' j) ((r i) ^ n • x) ∈ C j) :
    ∃ D : Subalgebra R S, D.FG ∧ ∀ i,
      Algebra.adjoin (R' i) (algebraMap S (S' i) '' (D : Set S)) = C i := by
  classical
  let K : Subalgebra R S := ⨅ i,
    ((C i).restrictScalars R).comap (IsScalarTower.toAlgHom R S (S' i))
  have memK (x : S) : x ∈ K ↔ ∀ i, algebraMap S (S' i) x ∈ C i :=
    Algebra.mem_iInf
  let := Fintype.ofFinite ι
  have clear (i : ι) (x : S) (hx : algebraMap S (S' i) x ∈ C i) :
      ∃ n : ℕ, (r i) ^ n • x ∈ K := by
    choose n hn using fun j => hCompat i j x hx
    let N := Finset.univ.sup n
    refine ⟨N, (memK _).mpr fun j => ?_⟩
    have hle : n j ≤ N := Finset.le_sup (Finset.mem_univ j)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have hmem := ((C j).restrictScalars R).smul_mem (hn j) ((r i) ^ k)
    change (r i) ^ k • algebraMap S (S' j) ((r i) ^ (n j) • x) ∈ C j at hmem
    rw [hk, Nat.add_comm (n j), pow_add, mul_smul]
    simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S] using hmem
  have localNumerator (i : ι) (z : S' i) (hz : z ∈ C i) :
      ∃ x ∈ K, ∃ n : ℕ, algebraMap S (S' i) x = (r i) ^ n • z := by
    obtain ⟨⟨x, m⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S (r i))) z
    obtain ⟨d, hd⟩ := m.property
    have hm : (m : S) = algebraMap R S ((r i) ^ d) := hd.symm.trans (by rw [map_pow])
    have he : algebraMap S (S' i) x = (r i) ^ d • z := by
      calc
        _ = z * algebraMap S (S' i) (m : S) := hx.symm
        _ = (r i) ^ d • z := by
          rw [hm, ← IsScalarTower.algebraMap_apply R S, Algebra.smul_def, mul_comm z]
    have hxC : algebraMap S (S' i) x ∈ C i := by
      rw [he]
      exact ((C i).restrictScalars R).smul_mem hz _
    obtain ⟨n, hn⟩ := clear i x hxC
    refine ⟨(r i) ^ n • x, hn, n + d, ?_⟩
    calc
      _ = (r i) ^ n • algebraMap S (S' i) x := by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S]
      _ = (r i) ^ (n + d) • z := by rw [he, smul_smul, ← pow_add]
  choose s hs hgen using fun i => Subalgebra.fg_def.mp (hfg i)
  let G := Σ i, ↥(s i)
  have (i : ι) : Finite ↥(s i) := (hs i).to_subtype
  have : Finite G := inferInstanceAs (Finite (Σ i, ↥(s i)))
  have hsg (a : G) : a.2.val ∈ C a.1 := hgen a.1 ▸ Algebra.subset_adjoin a.2.property
  choose a ha n hn using fun g : G => localNumerator g.1 g.2.val (hsg g)
  let D := Algebra.adjoin R (Set.range a)
  have hD : D ≤ K := Algebra.adjoin_le (by rintro _ ⟨g, rfl⟩; exact ha g)
  refine ⟨D, Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩, fun i => ?_⟩
  let A := Algebra.adjoin (R' i) (algebraMap S (S' i) '' (D : Set S))
  refine le_antisymm (Algebra.adjoin_le ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (memK _).mp (hD hx) i
  · rw [← hgen i]
    apply Algebra.adjoin_le
    intro z hz
    let g : G := ⟨i, ⟨z, hz⟩⟩
    have hmem : algebraMap S (S' i) (a g) ∈ A :=
      Algebra.subset_adjoin ⟨a g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
    have he : algebraMap S (S' i) (a g) = (r i) ^ (n g) • z := hn g
    let m : Submonoid.powers (r i) := ⟨(r i) ^ (n g), ⟨n g, rfl⟩⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (R' i) m
    have he' : algebraMap S (S' i) (a g) = algebraMap (R' i) (S' i) (↑u : R' i) * z := by
      rw [he, Algebra.smul_def, IsScalarTower.algebraMap_apply R (R' i)]
      congr 2
      exact hu.symm
    have hm := A.mul_mem (A.algebraMap_mem (↑u⁻¹ : R' i)) hmem
    rwa [he', ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at hm

end FiniteFamily

end PhilipponIntegralSubalgebraLocalization


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.AffineZariskiSite

noncomputable section

namespace PhilipponFiniteRelativeSpec

universe u

abbrev StructureRings (Y : Scheme.{u}) :=
  (toOpensFunctor Y).op ⋙ Y.presheaf

abbrev PreimageRings {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (toOpensFunctor Y).op ⋙ f.base _* X.presheaf

abbrev structureToPreimage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StructureRings Y ⟶ PreimageRings f :=
  (toOpensFunctor Y).op.whiskerLeft f.c

/-- An algebra given on affine opens with the standard localization
isomorphisms on principal opens. -/
structure AffineAlgebra (Y : Scheme.{u}) where
  rings : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}
  unit : StructureRings Y ⟶ rings
  coequifibered : unit.Coequifibered

namespace AffineAlgebra

variable {X Y : Scheme.{u}} (A : AffineAlgebra Y)

abbrev glueData := relativeGluingData A.coequifibered

instance : (A.glueData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  A.glueData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

abbrev spec : Scheme.{u} := A.glueData.glued

abbrev π : A.spec ⟶ Y := A.glueData.toBase

abbrev ι (U : Y.AffineZariskiSite) : Spec (A.rings.obj (op U)) ⟶ A.spec :=
  colimit.ι A.glueData.functor U

@[reassoc]
theorem ι_π (U : Y.AffineZariskiSite) :
    A.ι U ≫ A.π = Spec.map (A.unit.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

theorem preimage (U : Y.AffineZariskiSite) :
    A.π ⁻¹ᵁ U.1 = (A.ι U).opensRange := by
  simpa using A.glueData.toBase_preimage_eq_opensRange_ι U

/-- The preimage of an affine open is canonically the corresponding
affine chart of the relative spectrum. -/
theorem isPullback_chart (U : Y.AffineZariskiSite) :
    IsPullback (Spec.map (A.unit.app (op U)) ≫ U.2.isoSpec.inv)
      (A.ι U) U.1.ι A.π :=
  A.glueData.isPullback_natTrans_ι_toBase U

/-- Finite algebras on affine charts give a finite relative spectrum. -/
theorem isFinite_π (h : ∀ U, (A.unit.app (op U)).hom.Finite) : IsFinite A.π := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (𝒰 := directedCover Y)
  intro U
  let B := Spec.map (A.unit.app (op U)) ≫ U.2.isoSpec.inv
  have : IsFinite (Spec.map (A.unit.app (op U))) := (IsFinite.SpecMap_iff _).mpr (h U)
  have hB : IsFinite B := inferInstanceAs (IsFinite (Spec.map (A.unit.app (op U)) ≫ _))
  let e := (A.isPullback_chart U).flip.isoPullback
  have he : e.hom ≫ pullback.snd A.π U.1.ι = B :=
    (A.isPullback_chart U).flip.isoPullback_hom_snd
  change IsFinite (pullback.snd A.π U.1.ι)
  rw [show pullback.snd A.π U.1.ι = e.inv ≫ B from ((Iso.inv_comp_eq e).mpr he.symm).symm]
  infer_instance

/-- A local factorization on the relative spectrum may be checked on its
charts over any affine open cover of the base. -/
theorem locallyFactorsThrough_π {I : Type*} (U : I → Y.AffineZariskiSite)
    (hCov : ∀ y : Y, ∃ i, y ∈ (U i).1) (g : X ⟶ Y)
    (h : ∀ i, PhilipponIntegralEtaleRefinement.LocallyFactorsThrough
      (Spec.map (A.unit.app (op (U i))) ≫ (U i).2.fromSpec) g) :
    PhilipponIntegralEtaleRefinement.LocallyFactorsThrough A.π g := by
  intro x
  obtain ⟨i, hi⟩ := hCov (A.π x)
  have hxi : x ∈ Set.range (A.ι (U i)) := by
    change x ∈ (A.ι (U i)).opensRange
    rw [← A.preimage]
    exact hi
  obtain ⟨z, hz⟩ := hxi
  obtain ⟨W, j, hj, ⟨w, hw⟩, b, hb⟩ := h i z
  refine ⟨W, j ≫ A.ι (U i), inferInstance, ⟨w, ?_⟩, b, ?_⟩
  · rw [Scheme.Hom.comp_apply, hw, hz]
  · rw [hb, Category.assoc, A.ι_π]

variable (f : X ⟶ Y)

/-- The map from a scheme to the relative spectrum of an algebra mapping
into its ring of functions over each affine open of the base. -/
def lift (φ : A.rings ⟶ PreimageRings f) : X ⟶ A.spec :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U =>
      (pullbackRestrictIsoRestrict f U.1).hom ≫ (f ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (φ.app (op U)) ≫ A.ι U) (fun {U V : Y.AffineZariskiSite} k => by
      have hk : (pullbackRestrictIsoRestrict f U.1).inv ≫
          Scheme.Cover.trans ((directedCover Y).pullback₁ f) k ≫
          (pullbackRestrictIsoRestrict f V.1).hom =
            X.homOfLE (f.preimage_mono (toOpens_mono k.1.1)) := by
        rw [← cancel_mono (Scheme.Opens.ι _)]
        simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
      rw [← Iso.inv_comp_eq, reassoc_of% hk, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
        ← Spec.map_comp_assoc]
      change _ = (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (φ.app (op U)) ≫
        colimit.ι A.glueData.functor U
      rw [← colimit.w A.glueData.functor k]
      change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (φ.app (op V) ≫ (PreimageRings f).map k.op) ≫
          A.ι V =
        (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (φ.app (op U)) ≫ Spec.map (A.rings.map k.op) ≫ A.ι V
      rw [← Spec.map_comp_assoc]
      exact congrArg (fun m => (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map m ≫ A.ι V) (φ.naturality k.op).symm)

@[reassoc]
theorem opens_ι_lift (φ : A.rings ⟶ PreimageRings f) (U : Y.AffineZariskiSite) :
    (f ⁻¹ᵁ U.1).ι ≫ A.lift f φ =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (φ.app (op U)) ≫ A.ι U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ A.lift f φ
  · congr 1
    simp
  delta lift
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

@[reassoc]
theorem lift_π (φ : A.rings ⟶ PreimageRings f) (hφ : A.unit ≫ φ = structureToPreimage f) :
    A.lift f φ ≫ A.π = f := by
  apply Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom))
  intro U
  refine (A.opens_ι_lift_assoc f φ U A.π).trans ?_
  rw [A.ι_π, ← Spec.map_comp_assoc]
  have hU : A.unit.app (op U) ≫ φ.app (op U) = f.app U.1 :=
    congrArg (fun η => η.app (op U)) hφ
  rw [hU]
  simp
  rfl

end AffineAlgebra

end PhilipponFiniteRelativeSpec


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.AffineZariskiSite
open PhilipponFiniteRelativeSpec
open PhilipponIntegralSubalgebraLocalization
  (isLocalization_of_eq_localizedSubalgebra mem_iff_mem_on_principal_cover
    adjoin_ringHom_image_adjoin fg_adjoin_ringHom_image)

noncomputable section

namespace PhilipponFiniteSubalgebraSchemes

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

abbrev AffineSubalgebra (U : Y.AffineZariskiSite) :=
  letI := (f.app U.1).hom.toAlgebra
  Subalgebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)

abbrev restrictSections {U V : Y.AffineZariskiSite} (k : U ⟶ V) :
    Γ(X, f ⁻¹ᵁ V.1) ⟶ Γ(X, f ⁻¹ᵁ U.1) :=
  (PreimageRings f).map k.op

/-- Restrict ambient sections along an arbitrary inclusion of opens. -/
abbrev restrictSectionsLE {U V : Y.Opens} (h : U ≤ V) :
    Γ(X, f ⁻¹ᵁ V) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  X.presheaf.map (homOfLE (f.preimage_mono h)).op

theorem restrictSectionsLE_comp {U V W : Y.Opens} (h : U ≤ V) (k : V ≤ W) :
    restrictSectionsLE f k ≫ restrictSectionsLE f h = restrictSectionsLE f (h.trans k) := by
  rw [← Functor.map_comp]
  rfl

theorem restrictSectionsLE_algebraMap {U V : Y.Opens} (h : U ≤ V) (r : Γ(Y, V)) :
    restrictSectionsLE f h (f.app V r) = f.app U (Y.presheaf.map (homOfLE h).op r) :=
  (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) r).symm

namespace AffineSubalgebra

variable {f} {U V W : Y.AffineZariskiSite}

/-- Restriction of an affine subalgebra to a smaller affine open,
including the scalars on the smaller open among its generators. -/
def restrict (C : AffineSubalgebra f V) (h : U.1 ≤ V.1) : AffineSubalgebra f U :=
  letI := (f.app U.1).hom.toAlgebra
  Algebra.adjoin Γ(Y, U.1) (restrictSectionsLE f h '' (C : Set Γ(X, f ⁻¹ᵁ V.1)))

theorem restrict_mem (C : AffineSubalgebra f V) (h : U.1 ≤ V.1)
    {x : Γ(X, f ⁻¹ᵁ V.1)} (hx : x ∈ C) :
    restrictSectionsLE f h x ∈ C.restrict (U := U) h := by
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)

@[simp]
theorem restrict_refl (C : AffineSubalgebra f U) : C.restrict (U := U) le_rfl = C := by
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  have hId : restrictSectionsLE f (U := U.1) le_rfl = 𝟙 Γ(X, f ⁻¹ᵁ U.1) :=
    X.presheaf.map_id _
  unfold restrict
  rw [hId]
  change Algebra.adjoin Γ(Y, U.1) (id '' (C : Set Γ(X, f ⁻¹ᵁ U.1))) = C
  rw [Set.image_id, Algebra.adjoin_eq]

theorem restrict_comp (C : AffineSubalgebra f W) (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    (C.restrict (U := V) k).restrict (U := U) h = C.restrict (U := U) (h.trans k) := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  unfold restrict
  have hh := adjoin_ringHom_image_adjoin
    (Y.presheaf.map (homOfLE h).op).hom (restrictSectionsLE f h).hom
    (restrictSectionsLE_algebraMap f h)
    (restrictSectionsLE f k '' (C : Set Γ(X, f ⁻¹ᵁ W.1)))
  change Algebra.adjoin Γ(Y, U.1) (restrictSectionsLE f h ''
    (Algebra.adjoin Γ(Y, V.1) (restrictSectionsLE f k '' (C : Set Γ(X, f ⁻¹ᵁ W.1))) : Set _)) = _
  rw [hh, Set.image_image]
  have hEq : (fun x => (restrictSectionsLE f h).hom (restrictSectionsLE f k x)) =
      (restrictSectionsLE f (h.trans k) : Γ(X, f ⁻¹ᵁ W.1) → Γ(X, f ⁻¹ᵁ U.1)) := by
    funext x
    change restrictSectionsLE f h (restrictSectionsLE f k x) = restrictSectionsLE f (h.trans k) x
    simp only [← CommRingCat.comp_apply, restrictSectionsLE_comp]
  rw [hEq]

/-- Finite generation of an affine subalgebra over the base sections. -/
abbrev IsFinitelyGenerated (C : AffineSubalgebra f V) : Prop :=
  letI := (f.app V.1).hom.toAlgebra
  C.FG

theorem restrict_fg (C : AffineSubalgebra f V) (h : U.1 ≤ V.1)
    (hC : C.IsFinitelyGenerated) : (C.restrict (U := U) h).IsFinitelyGenerated := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  exact fg_adjoin_ringHom_image (Y.presheaf.map (homOfLE h).op).hom (restrictSectionsLE f h).hom
    (restrictSectionsLE_algebraMap f h) C hC

end AffineSubalgebra

/-- Subalgebras of the rings of sections of an affine morphism, with
compatible restrictions and generation by restriction on principal opens. -/
structure SubalgebraFamily where
  atOpen : ∀ U : Y.AffineZariskiSite, AffineSubalgebra f U
  restrict_mem : ∀ {U V : Y.AffineZariskiSite} (k : U ⟶ V)
    (x : Γ(X, f ⁻¹ᵁ V.1)), x ∈ atOpen V →
      restrictSections f k x ∈ atOpen U
  basicOpen : ∀ (U : Y.AffineZariskiSite) (r : Γ(Y, U.1)),
    let V := U.basicOpen r
    letI := (f.app V.1).hom.toAlgebra
    Algebra.adjoin Γ(Y, V.1)
        (restrictSections f (homOfLE (U.basicOpen_le r)) '' (atOpen U : Set Γ(X, f ⁻¹ᵁ U.1))) =
      atOpen V

namespace SubalgebraFamily

variable {f} (C : SubalgebraFamily f)

def rings : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (C.atOpen U.unop)
  map k := CommRingCat.ofHom (((PreimageRings f).map k).hom.restrict _ _
    (fun x hx => C.restrict_mem k.unop x hx))
  map_id U := by
    ext x
    change (PreimageRings f).map (𝟙 U) x.val = x.val
    simp
  map_comp k l := by
    ext x
    change (PreimageRings f).map (k ≫ l) x.val =
      (PreimageRings f).map l ((PreimageRings f).map k x.val)
    simp

def inclusion : C.rings ⟶ PreimageRings f where
  app U :=
    letI := (f.app U.unop.1).hom.toAlgebra
    CommRingCat.ofHom (C.atOpen U.unop).val.toRingHom
  naturality _ _ k := by ext x; rfl

def unit : StructureRings Y ⟶ C.rings where
  app U :=
    letI := (f.app U.unop.1).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop.1) (C.atOpen U.unop))
  naturality U V k := by
    ext x
    exact Subtype.ext (congrArg (fun m => m x) (f.naturality ((toOpensFunctor Y).op.map k)))

theorem unit_inclusion : C.unit ≫ C.inclusion = structureToPreimage f := by
  apply NatTrans.ext
  funext U
  ext x
  rfl

private theorem coequifibered [IsAffineHom f] : C.unit.Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V := U.basicOpen r
  let k : op U ⟶ op V := (homOfLE (U.basicOpen_le r)).op
  let R := Γ(Y, U.1)
  let S := Γ(X, f ⁻¹ᵁ U.1)
  let R' := Γ(Y, V.1)
  let S' := Γ(X, f ⁻¹ᵁ V.1)
  let : Algebra R S := (f.app U.1).hom.toAlgebra
  let : Algebra R' S' := (f.app V.1).hom.toAlgebra
  let : Algebra R R' := (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra S S' :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  let : Algebra R S' := (f.appLE U.1 (f ⁻¹ᵁ V.1) (f.preimage_mono (Y.basicOpen_le r))).hom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' S' := .of_algebraMap_eq' (by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE, Scheme.AffineZariskiSite.basicOpen, V])
  have : IsLocalization.Away r R' := U.2.isLocalization_basicOpen _
  have hLocal : IsLocalization.Away ((algebraMap R S) r) S' := by
    let : Algebra S Γ(X, X.basicOpen (f.app U.1 r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst, S, S', V]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact (U.2.preimage f).isLocalization_basicOpen _
  have : IsLocalization ((Submonoid.powers r).map (algebraMap R S)) S' := by
    rw [Submonoid.map_powers]
    exact hLocal
  let : Algebra (C.atOpen U) (C.atOpen V) := (C.rings.map k).hom.toAlgebra
  have he : Algebra.adjoin R' (algebraMap S S' '' (C.atOpen U : Set _)) = C.atOpen V :=
    C.basicOpen U r
  have hl := isLocalization_of_eq_localizedSubalgebra (R := R) (S := S) (R' := R') (S' := S')
    (Submonoid.powers r) (C.atOpen U) (C.atOpen V) he (fun x => rfl)
  rw [Submonoid.map_powers] at hl
  exact hl

/-- A compatible family gives an affine algebra to which relative
spectrum gluing applies. -/
def affineAlgebra [IsAffineHom f] : AffineAlgebra Y :=
  ⟨C.rings, C.unit, C.coequifibered⟩

/-- Module-finiteness on each affine chart produces a finite factorization
of the original morphism. -/
theorem exists_finite_factorization [IsAffineHom f]
    (h : ∀ U : Y.AffineZariskiSite, (C.unit.app (op U)).hom.Finite) :
    ∃ (P : Scheme.{u}) (g : X ⟶ P) (p : P ⟶ Y), g ≫ p = f ∧ IsFinite p :=
  ⟨C.affineAlgebra.spec, C.affineAlgebra.lift f C.inclusion, C.affineAlgebra.π,
    C.affineAlgebra.lift_π f C.inclusion C.unit_inclusion, C.affineAlgebra.isFinite_π h⟩

end SubalgebraFamily

namespace AffineSubalgebra

variable {f}

/-- Membership in an affine subalgebra can be checked on a principal
open cover by restricting the subalgebra to those opens. -/
theorem mem_iff_on_principal_cover [IsAffineHom f] (U : Y.AffineZariskiSite)
    (D : AffineSubalgebra f U)
    {I : Type*} (r : I → Γ(Y, U.1)) (hCov : (⨆ i, Y.basicOpen (r i)) = U.1)
    (x : Γ(X, f ⁻¹ᵁ U.1)) :
    x ∈ D ↔ ∀ i, restrictSectionsLE f (Y.basicOpen_le (r i)) x ∈
      D.restrict (U := U.basicOpen (r i)) (Y.basicOpen_le (r i)) := by
  let R := Γ(Y, U.1)
  let S := Γ(X, f ⁻¹ᵁ U.1)
  let R' (i : I) := Γ(Y, Y.basicOpen (r i))
  let S' (i : I) := Γ(X, f ⁻¹ᵁ Y.basicOpen (r i))
  let : Algebra R S := (f.app U.1).hom.toAlgebra
  let (i : I) : Algebra R (R' i) := (Y.presheaf.map (homOfLE (Y.basicOpen_le (r i))).op).hom.toAlgebra
  let (i : I) : Algebra (R' i) (S' i) := (f.app (Y.basicOpen (r i))).hom.toAlgebra
  let inst (i : I) : Algebra S (S' i) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le (r i)))).op).hom.toAlgebra
  let (i : I) : Algebra R (S' i) :=
    (f.appLE U.1 _ (f.preimage_mono (Y.basicOpen_le (r i)))).hom.toAlgebra
  have (i : I) : IsScalarTower R S (S' i) := .of_algebraMap_eq' rfl
  have (i : I) : IsScalarTower R (R' i) (S' i) := .of_algebraMap_eq' (by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE])
  have (i : I) : IsLocalization.Away (r i) (R' i) := U.2.isLocalization_basicOpen _
  have (i : I) : IsLocalization.Away ((algebraMap R S) (r i)) (S' i) := by
    let : Algebra S Γ(X, X.basicOpen (f.app U.1 (r i))) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst, S, S']
    rw! (castMode := .all) [f.preimage_basicOpen (r i)]
    exact (U.2.preimage f).isLocalization_basicOpen _
  have hRange : (⨆ a : Set.range r, Y.basicOpen a.val) = (⨆ i, Y.basicOpen (r i)) := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨_, i, rfl⟩
      exact le_iSup (fun j : I => Y.basicOpen (r j)) i
    · exact iSup_le fun i => le_iSup (fun a : Set.range r => Y.basicOpen a.val) ⟨r i, ⟨i, rfl⟩⟩
  have hSpan : Ideal.span (Set.range r) = ⊤ :=
    U.2.iSup_basicOpen_eq_self_iff.mp (hRange.trans hCov)
  exact mem_iff_mem_on_principal_cover (R' := fun i => ↥(R' i)) (S' := fun i => ↥(S' i)) r hSpan D x

theorem eq_of_restrict_eq_on_principal_cover [IsAffineHom f] (U : Y.AffineZariskiSite)
    {I : Type*} (r : I → Γ(Y, U.1)) (hCov : (⨆ i, Y.basicOpen (r i)) = U.1)
    (B D : AffineSubalgebra f U) (h : ∀ i,
      B.restrict (U := U.basicOpen (r i)) (Y.basicOpen_le (r i)) =
        D.restrict (U := U.basicOpen (r i)) (Y.basicOpen_le (r i))) :
    B = D := by
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  ext x
  rw [mem_iff_on_principal_cover U B r hCov, mem_iff_on_principal_cover U D r hCov]
  exact forall_congr' fun i => by rw [h i]

end AffineSubalgebra

namespace SubalgebraFamily

variable {f} (C : SubalgebraFamily f)

/-- A section of the ambient affine algebra belongs to a compatible
family if its restrictions do so on a principal open cover. -/
theorem mem_iff_on_principal_cover [IsAffineHom f] (U : Y.AffineZariskiSite)
    {I : Type*} (r : I → Γ(Y, U.1)) (hCov : (⨆ i, Y.basicOpen (r i)) = U.1)
    (x : Γ(X, f ⁻¹ᵁ U.1)) :
    x ∈ C.atOpen U ↔
      ∀ i, restrictSections f (homOfLE (U.basicOpen_le (r i))) x ∈ C.atOpen (U.basicOpen (r i)) := by
  refine (AffineSubalgebra.mem_iff_on_principal_cover U (C.atOpen U) r hCov x).trans ?_
  exact forall_congr' fun i => by
    rw [show (C.atOpen U).restrict (U := U.basicOpen (r i)) (Y.basicOpen_le (r i)) = _
      from C.basicOpen U (r i)]
    rfl

end SubalgebraFamily

end PhilipponFiniteSubalgebraSchemes


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFiniteSubalgebraSchemes
open PhilipponIntegralSubalgebraLocalization
  (mem_localized_adjoin_iff exists_fg_subalgebra_of_compatible_localizations)

noncomputable section

namespace PhilipponCompatibleSubalgebraCover

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

private theorem isLocalization_ambient_basicOpen (U : Y.AffineZariskiSite) (r : Γ(Y, U.1)) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (restrictSectionsLE f (Y.basicOpen_le r)).hom.toAlgebra
    IsLocalization.Away (algebraMap Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (restrictSectionsLE f (Y.basicOpen_le r)).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app U.1 r)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
  dsimp +instances [restrictSectionsLE]
  rw! (castMode := .all) [f.preimage_basicOpen r]
  exact (U.2.preimage f).isLocalization_basicOpen _

/-- A section in the restricted subalgebra on a principal open lies in
the original subalgebra after multiplying by a power of the denominator. -/
theorem exists_pow_of_mem_restrict_basicOpen (U : Y.AffineZariskiSite)
    (C : AffineSubalgebra f U) (r : Γ(Y, U.1)) (x : Γ(X, f ⁻¹ᵁ U.1))
    (hx : restrictSectionsLE f (Y.basicOpen_le r) x ∈
      C.restrict (U := U.basicOpen r) (Y.basicOpen_le r)) :
    letI := (f.app U.1).hom.toAlgebra
    ∃ n : ℕ, r ^ n • x ∈ C := by
  let R := Γ(Y, U.1)
  let S := Γ(X, f ⁻¹ᵁ U.1)
  let R' := Γ(Y, Y.basicOpen r)
  let S' := Γ(X, f ⁻¹ᵁ Y.basicOpen r)
  let : Algebra R S := (f.app U.1).hom.toAlgebra
  let : Algebra R' S' := (f.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra R R' := (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let : Algebra S S' := (restrictSectionsLE f (Y.basicOpen_le r)).hom.toAlgebra
  let : Algebra R S' := (f.appLE U.1 _ (f.preimage_mono (Y.basicOpen_le r))).hom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' S' := .of_algebraMap_eq' (by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE])
  have : IsLocalization.Away r R' := U.2.isLocalization_basicOpen _
  have : IsLocalization ((Submonoid.powers r).map (algebraMap R S)) S' := by
    rw [Submonoid.map_powers]
    exact isLocalization_ambient_basicOpen f U r
  obtain ⟨m, hm⟩ := (mem_localized_adjoin_iff (R' := R') (S' := S')
    (Submonoid.powers r) C x).mp hx
  obtain ⟨n, hn⟩ := m.property
  refine ⟨n, ?_⟩
  change r ^ n = (m : R) at hn
  change (m : R) • x ∈ C at hm
  rwa [hn]

omit [IsAffineHom f] in
private theorem mem_restriction_of_pow (U V : Y.AffineZariskiSite) (h : V.1 ≤ U.1)
    (r : Γ(Y, U.1)) (x : Γ(X, f ⁻¹ᵁ U.1)) (C : AffineSubalgebra f V) (n : ℕ)
    (hn : letI := (f.app V.1).hom.toAlgebra
      (Y.presheaf.map (homOfLE h).op r) ^ n • restrictSectionsLE f h x ∈ C) :
    letI := (f.app U.1).hom.toAlgebra
    restrictSectionsLE f h (r ^ n • x) ∈ C := by
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  change restrictSectionsLE f h (r ^ n • x) ∈ C
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul,
    restrictSectionsLE_algebraMap, map_pow] at hn ⊢
  exact hn

/-- Finitely generated subalgebras on finitely many principal opens of
an affine chart extend to that chart if their restrictions agree on
overlaps. The principal opens can cover a proper subset of the chart. -/
theorem exists_fg_subalgebra_restrict_eq (U : Y.AffineZariskiSite)
    {I : Type*} [Finite I] (r : I → Γ(Y, U.1))
    (C : ∀ i, AffineSubalgebra f (U.basicOpen (r i)))
    (hFG : ∀ i, (C i).IsFinitelyGenerated)
    (hCompat : ∀ (i j : I) (W : Y.AffineZariskiSite)
      (hi : W.1 ≤ (U.basicOpen (r i)).1) (hj : W.1 ≤ (U.basicOpen (r j)).1),
      (C i).restrict (U := W) hi = (C j).restrict (U := W) hj) :
    ∃ D : AffineSubalgebra f U, D.IsFinitelyGenerated ∧
      ∀ i, D.restrict (U := U.basicOpen (r i)) (Y.basicOpen_le (r i)) = C i := by
  let R := Γ(Y, U.1)
  let S := Γ(X, f ⁻¹ᵁ U.1)
  let R' (i : I) := Γ(Y, Y.basicOpen (r i))
  let S' (i : I) := Γ(X, f ⁻¹ᵁ Y.basicOpen (r i))
  let : Algebra R S := (f.app U.1).hom.toAlgebra
  let (i : I) : Algebra R (R' i) := (Y.presheaf.map (homOfLE (Y.basicOpen_le (r i))).op).hom.toAlgebra
  let (i : I) : Algebra (R' i) (S' i) := (f.app (Y.basicOpen (r i))).hom.toAlgebra
  let (i : I) : Algebra S (S' i) := (restrictSectionsLE f (Y.basicOpen_le (r i))).hom.toAlgebra
  let (i : I) : Algebra R (S' i) :=
    (f.appLE U.1 _ (f.preimage_mono (Y.basicOpen_le (r i)))).hom.toAlgebra
  have (i : I) : IsScalarTower R S (S' i) := .of_algebraMap_eq' rfl
  have (i : I) : IsScalarTower R (R' i) (S' i) := .of_algebraMap_eq' (by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE])
  have (i : I) : IsLocalization.Away (r i) (R' i) := U.2.isLocalization_basicOpen _
  have (i : I) : IsLocalization.Away (algebraMap R S (r i)) (S' i) :=
    isLocalization_ambient_basicOpen f U (r i)
  apply exists_fg_subalgebra_of_compatible_localizations
    (R' := fun i => ↥(R' i)) (S' := fun i => ↥(S' i)) r C hFG
  intro i j x hx
  let V := U.basicOpen (r j)
  let jU : V.1 ≤ U.1 := Y.basicOpen_le (r j)
  let iU : (U.basicOpen (r i)).1 ≤ U.1 := Y.basicOpen_le (r i)
  let a : Γ(Y, V.1) := Y.presheaf.map (homOfLE jU).op (r i)
  let W := V.basicOpen a
  let Wj : W.1 ≤ V.1 := Y.basicOpen_le a
  have Wi : W.1 ≤ (U.basicOpen (r i)).1 := by
    change Y.basicOpen (Y.presheaf.map (homOfLE jU).op (r i)) ≤ Y.basicOpen (r i)
    rw [Scheme.basicOpen_res]
    exact inf_le_right
  have hmem : restrictSectionsLE f Wj (restrictSectionsLE f jU x) ∈
      (C j).restrict (U := W) Wj := by
    rw [← hCompat i j W Wi Wj, ← CommRingCat.comp_apply, restrictSectionsLE_comp f Wj jU]
    rw [show Wj.trans jU = Wi.trans iU from Subsingleton.elim _ _, ← restrictSectionsLE_comp f Wi iU,
      CommRingCat.comp_apply]
    exact AffineSubalgebra.restrict_mem _ _ hx
  obtain ⟨n, hn⟩ := exists_pow_of_mem_restrict_basicOpen f V (C j) a
    (restrictSectionsLE f jU x) hmem
  exact ⟨n, mem_restriction_of_pow f U V jU (r i) x (C j) n hn⟩

end PhilipponCompatibleSubalgebraCover


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponIntegralEtaleRefinement (LocallyFactorsThrough)
open PhilipponFiniteSubalgebraSchemes

noncomputable section

namespace PhilipponFiniteGlobalRefinement

universe u

variable {P X Y : Scheme.{u}}

/-- The intersection of two affine opens in a quasi-separated scheme
has a finite cover by opens principal in both charts. -/
theorem exists_finite_common_principal_cover [QuasiSeparatedSpace Y]
    (U V : Y.AffineZariskiSite) :
    ∃ (I : Type u) (_ : Finite I) (a : I → Γ(Y, U.1)) (b : I → Γ(Y, V.1)),
      (∀ i, Y.basicOpen (a i) = Y.basicOpen (b i)) ∧ (⨆ i, Y.basicOpen (a i)) = U.1 ⊓ V.1 := by
  classical
  let W := U.1 ⊓ V.1
  have cover (x : W) : ∃ (a : Γ(Y, U.1)) (b : Γ(Y, V.1)),
      Y.basicOpen a = Y.basicOpen b ∧ x.val ∈ Y.basicOpen a :=
    exists_basicOpen_le_affine_inter U.2 V.2 x.val x.property
  choose a b hEq hx using cover
  have hCompact : IsCompact (W : Set Y) :=
    U.2.isCompact.inter_of_isOpen V.2.isCompact U.1.isOpen V.1.isOpen
  have hCover : (W : Set Y) ⊆ ⋃ x : W, (Y.basicOpen (a x) : Set Y) :=
    fun x hxW => Set.mem_iUnion.mpr ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩
  obtain ⟨F, hF⟩ := hCompact.elim_finite_subcover (fun x => (Y.basicOpen (a x) : Set Y))
    (fun x => (Y.basicOpen (a x)).isOpen) hCover
  refine ⟨↥F, inferInstance, fun i => a i.val, fun i => b i.val, fun i => hEq i.val,
    le_antisymm (iSup_le fun i => ?_) ?_⟩
  · exact le_inf (Y.basicOpen_le _) ((hEq i.val).le.trans (Y.basicOpen_le _))
  · intro x hxW
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF hxW)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩

private abbrev FGAt (p : P ⟶ Y) (U : Y.AffineZariskiSite) (C : AffineSubalgebra p U) : Prop :=
  letI := (p.app U.1).hom.toAlgebra
  C.FG

private def chartMap (p : P ⟶ Y) (U : Y.AffineZariskiSite) (C : AffineSubalgebra p U) :
    Spec (CommRingCat.of C) ⟶ Y :=
  letI := (p.app U.1).hom.toAlgebra
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U.1) C)) ≫ U.2.fromSpec

/-- On every affine chart of the base the local factorization can be
realized using a finitely generated subalgebra of the original cover. -/
theorem exists_fg_subalgebra_of_locallyFactorsThrough
    (p : P ⟶ Y) [IsAffineHom p] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (h : LocallyFactorsThrough p f) (U : Y.AffineZariskiSite) :
    ∃ C : AffineSubalgebra p U, FGAt p U C ∧ LocallyFactorsThrough (chartMap p U C) f := by
  let a := U.2.fromSpec
  let b := Spec.map (p.app U.1)
  let t := (U.2.preimage p).fromSpec
  have hbt : b ≫ a = t ≫ p := by
    simpa only [a, b, t, Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec p U.2 (U.2.preimage p) le_rfl)
  let e := pullback.snd f a
  have : LocallyOfFinitePresentation e :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f a))
  have hLocal : LocallyFactorsThrough b e := by
    have hh := LocallyFactorsThrough.precomp h t
    rw [← hbt] at hh
    intro x
    obtain ⟨W, i, hi, hx, g, hg⟩ := hh x
    let m := pullback.lift g (i ≫ b) (hg.trans (Category.assoc _ _ _).symm)
    exact ⟨W, i, hi, hx, m, pullback.lift_snd _ _ _⟩
  let : Algebra Γ(Y, U.1) Γ(P, p ⁻¹ᵁ U.1) := (p.app U.1).hom.toAlgebra
  obtain ⟨C, hFG, hC⟩ := PhilipponEtaleRefinementAffine.exists_fg_subalgebra_refinement e hLocal
  refine ⟨C, hFG, fun x => ?_⟩
  obtain ⟨W, i, hi, hx, l, hl⟩ := hC x
  refine ⟨W, i, hi, hx, l ≫ pullback.fst f a, ?_⟩
  change (l ≫ pullback.fst f a) ≫ f = i ≫ (_ ≫ a)
  rw [Category.assoc, pullback.condition, ← Category.assoc, hl, Category.assoc]

private theorem isFinite_unit_of_fg (p : P ⟶ Y) [IsIntegralHom p]
    (C : SubalgebraFamily p) (U : Y.AffineZariskiSite) (h : FGAt p U (C.atOpen U)) :
    (C.unit.app (op U)).hom.Finite := by
  let : Algebra Γ(Y, U.1) Γ(P, p ⁻¹ᵁ U.1) := (p.app U.1).hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, U.1) Γ(P, p ⁻¹ᵁ U.1) :=
    algebraMap_isIntegral_iff.mp (p.isIntegral_app U.1 U.2)
  have : Algebra.IsIntegral Γ(Y, U.1) (C.atOpen U) :=
    Algebra.IsIntegral.of_injective (C.atOpen U).val Subtype.val_injective
  have : Algebra.FiniteType Γ(Y, U.1) (C.atOpen U) :=
    (C.atOpen U).fg_iff_finiteType.mp h
  have hFin : Module.Finite Γ(Y, U.1) (C.atOpen U) := Algebra.IsIntegral.finite
  change (algebraMap Γ(Y, U.1) (C.atOpen U)).Finite
  exact RingHom.finite_algebraMap.mpr hFin

private theorem locallyFactorsThrough_of_subalgebra_le (p : P ⟶ Y) (f : X ⟶ Y)
    (U : Y.AffineZariskiSite) {B C : AffineSubalgebra p U} (h : B ≤ C)
    (hB : LocallyFactorsThrough (chartMap p U B) f) :
    LocallyFactorsThrough (chartMap p U C) f := by
  let : Algebra Γ(Y, U.1) Γ(P, p ⁻¹ᵁ U.1) := (p.app U.1).hom.toAlgebra
  let r := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)
  have hr : r ≫ chartMap p U B = chartMap p U C := by
    dsimp only [r, chartMap]
    rw [← Spec.map_comp_assoc]
    congr 2
  exact hr ▸ LocallyFactorsThrough.precomp hB r

/-- Simultaneous extension of finitely generated subalgebras on an affine
cover suffices to obtain a finite refinement over the entire base. -/
theorem exists_finite_refinement_of_subalgebra_extension
    (p : P ⟶ Y) [IsIntegralHom p] [Surjective p]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (h : LocallyFactorsThrough p f)
    {I : Type*} (U : I → Y.AffineZariskiSite) (hCov : ∀ y : Y, ∃ i, y ∈ (U i).1)
    (hExtend : ∀ B : ∀ i, AffineSubalgebra p (U i), (∀ i, FGAt p (U i) (B i)) →
      ∃ C : SubalgebraFamily p, (∀ V, FGAt p V (C.atOpen V)) ∧ ∀ i, B i ≤ C.atOpen (U i)) :
    ∃ (Q : Scheme.{u}) (q : Q ⟶ Y), IsFinite q ∧ Surjective q ∧ LocallyFactorsThrough q f := by
  classical
  choose B hB hloc using fun i => exists_fg_subalgebra_of_locallyFactorsThrough p f h (U i)
  obtain ⟨C, hFG, hIncl⟩ := hExtend B hB
  let A := C.affineAlgebra
  let r := A.lift p C.inclusion
  have hr : r ≫ A.π = p := A.lift_π p C.inclusion C.unit_inclusion
  refine ⟨A.spec, A.π, A.isFinite_π (fun V => isFinite_unit_of_fg p C V (hFG V)),
    ⟨fun y => ?_⟩, A.locallyFactorsThrough_π U hCov f (fun i => ?_)⟩
  · obtain ⟨x, hx⟩ := (inferInstance : Surjective p).surj y
    exact ⟨r x, (congrArg (fun v : P ⟶ Y => v x) hr).trans hx⟩
  · exact locallyFactorsThrough_of_subalgebra_le p f (U i) (hIncl i) (hloc i)

end PhilipponFiniteGlobalRefinement


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.AffineZariskiSite
open TopologicalSpace (Opens)
open PhilipponFiniteSubalgebraSchemes

noncomputable section

namespace PhilipponCompatibleSubalgebraAtlas

universe u

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Values on the affine charts of an atlas agree when restricted to
any common affine subchart. -/
def Compatible {I : Type u} (V : I → Y.AffineZariskiSite)
    (B : ∀ i, AffineSubalgebra f (V i)) : Prop :=
  ∀ (i j : I) (W : Y.AffineZariskiSite) (hi : W.1 ≤ (V i).1) (hj : W.1 ≤ (V j).1),
    (B i).restrict (U := W) hi = (B j).restrict (U := W) hj

private theorem exists_principal_overlap_cover [QuasiSeparatedSpace Y]
    (U : Y.AffineZariskiSite) {I : Type u} [Finite I] (V : I → Y.AffineZariskiSite) :
    ∃ (J : Type u) (_ : Finite J) (a : J → I) (r : J → Γ(Y, U.1)),
      (∀ j, Y.basicOpen (r j) ≤ (V (a j)).1) ∧
        (⨆ j, Y.basicOpen (r j)) = U.1 ⊓ (⨆ i, (V i).1) := by
  classical
  choose J hJ s t he hcov using fun i =>
    PhilipponFiniteGlobalRefinement.exists_finite_common_principal_cover U (V i)
  have (i : I) : Finite (J i) := hJ i
  let K := Σ i, J i
  let r (j : K) := s j.1 j.2
  have hb (j : K) : Y.basicOpen (r j) ≤ (V j.1).1 :=
    (he j.1 j.2).le.trans (Y.basicOpen_le _)
  refine ⟨K, inferInstanceAs (Finite (Σ i, J i)), Sigma.fst, r, hb, le_antisymm ?_ ?_⟩
  · exact iSup_le fun j => le_inf (Y.basicOpen_le _) ((hb j).trans (le_iSup (fun i => (V i).1) j.1))
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx.2
    have hxi : x ∈ ⨆ j, Y.basicOpen (s i j) := by
      rw [hcov i]
      exact ⟨hx.1, hi⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxi
    exact Opens.mem_iSup.mpr ⟨⟨i, j⟩, hj⟩

private theorem cover_by_restrictions {U W : Y.AffineZariskiSite} (hWU : W.1 ≤ U.1)
    {I J : Type u} {V : I → Y.AffineZariskiSite} (r : J → Γ(Y, U.1))
    (hr : (⨆ j, Y.basicOpen (r j)) = U.1 ⊓ (⨆ i, (V i).1))
    (hW : W.1 ≤ ⨆ i, (V i).1) :
    (⨆ j, Y.basicOpen (Y.presheaf.map (homOfLE hWU).op (r j))) = W.1 := by
  apply le_antisymm (iSup_le fun _ => Y.basicOpen_le _)
  intro x hx
  have hxr : x ∈ ⨆ j, Y.basicOpen (r j) := by
    rw [hr]
    exact ⟨hWU hx, hW hx⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxr
  refine Opens.mem_iSup.mpr ⟨j, ?_⟩
  rw [Scheme.basicOpen_res]
  exact ⟨hx, hj⟩

/-- A finitely generated compatible affine atlas can be extended across
one additional affine chart. The extension agrees over every affine
subchart of each overlap. -/
theorem exists_extension_to_chart [IsAffineHom f] [QuasiSeparatedSpace Y]
    {I : Type u} [Finite I] (V : I → Y.AffineZariskiSite)
    (B : ∀ i, AffineSubalgebra f (V i)) (hFG : ∀ i, (B i).IsFinitelyGenerated)
    (hB : Compatible V B) (U : Y.AffineZariskiSite) :
    ∃ D : AffineSubalgebra f U, D.IsFinitelyGenerated ∧
      ∀ (i : I) (W : Y.AffineZariskiSite) (hWU : W.1 ≤ U.1) (hWV : W.1 ≤ (V i).1),
        D.restrict (U := W) hWU = (B i).restrict (U := W) hWV := by
  obtain ⟨J, hJ, a, r, hV, hr⟩ := exists_principal_overlap_cover U V
  let T (j : J) := U.basicOpen (r j)
  let C (j : J) : AffineSubalgebra f (T j) := (B (a j)).restrict (U := T j) (hV j)
  have hC (j : J) : (C j).IsFinitelyGenerated := (B (a j)).restrict_fg (hV j) (hFG (a j))
  have hCompat : Compatible T C := by
    intro i j W hi hj
    dsimp only [C]
    rw [AffineSubalgebra.restrict_comp, AffineSubalgebra.restrict_comp]
    exact hB (a i) (a j) W (hi.trans (hV i)) (hj.trans (hV j))
  obtain ⟨D, hD, hDC⟩ :=
    PhilipponCompatibleSubalgebraCover.exists_fg_subalgebra_restrict_eq f U r C hC hCompat
  refine ⟨D, hD, fun i W hWU hWV => ?_⟩
  let s (j : J) := Y.presheaf.map (homOfLE hWU).op (r j)
  have hCov : (⨆ j, Y.basicOpen (s j)) = W.1 :=
    cover_by_restrictions hWU r hr (hWV.trans (le_iSup (fun i => (V i).1) i))
  apply AffineSubalgebra.eq_of_restrict_eq_on_principal_cover W s hCov
  intro j
  let P := W.basicOpen (s j)
  let hPW : P.1 ≤ W.1 := Y.basicOpen_le (s j)
  have hPT : P.1 ≤ (T j).1 := by
    change Y.basicOpen (Y.presheaf.map (homOfLE hWU).op (r j)) ≤ Y.basicOpen (r j)
    rw [Scheme.basicOpen_res]
    exact inf_le_right
  let hTU : (T j).1 ≤ U.1 := Y.basicOpen_le (r j)
  calc
    (D.restrict (U := W) hWU).restrict (U := P) hPW =
        (D.restrict (U := T j) hTU).restrict (U := P) hPT := by
      rw [AffineSubalgebra.restrict_comp, AffineSubalgebra.restrict_comp]
    _ = (C j).restrict (U := P) hPT := by rw [hDC j]
    _ = (B (a j)).restrict (U := P) (hPT.trans (hV j)) :=
      AffineSubalgebra.restrict_comp _ _ _
    _ = (B i).restrict (U := P) (hPW.trans hWV) :=
      hB (a j) i P _ _
    _ = ((B i).restrict (U := W) hWV).restrict (U := P) hPW :=
      (AffineSubalgebra.restrict_comp _ _ _).symm

/-- Compatible finitely generated subalgebras on a finite affine cover
give a compatible family on all affine opens. -/
theorem exists_family_of_cover [IsAffineHom f] [QuasiSeparatedSpace Y]
    {I : Type u} [Finite I] (V : I → Y.AffineZariskiSite)
    (hV : (⨆ i, (V i).1) = ⊤)
    (B : ∀ i, AffineSubalgebra f (V i)) (hFG : ∀ i, (B i).IsFinitelyGenerated)
    (hB : Compatible V B) :
    ∃ C : SubalgebraFamily f, (∀ U, (C.atOpen U).IsFinitelyGenerated) ∧
      (∀ (U W : Y.AffineZariskiSite) (h : W.1 ≤ U.1), (C.atOpen U).restrict (U := W) h = C.atOpen W) ∧
      ∀ i, C.atOpen (V i) = B i := by
  classical
  choose D hD hAgree using exists_extension_to_chart V B hFG hB
  have hRes (U W : Y.AffineZariskiSite) (hWU : W.1 ≤ U.1) :
      (D U).restrict (U := W) hWU = D W := by
    obtain ⟨J, _, a, r, hContain, hCov⟩ := exists_principal_overlap_cover W V
    rw [hV, inf_top_eq] at hCov
    apply AffineSubalgebra.eq_of_restrict_eq_on_principal_cover W r hCov
    intro j
    let P := W.basicOpen (r j)
    let hPW : P.1 ≤ W.1 := Y.basicOpen_le (r j)
    change ((D U).restrict (U := W) hWU).restrict (U := P) hPW =
      (D W).restrict (U := P) hPW
    rw [AffineSubalgebra.restrict_comp]
    exact (hAgree U (a j) P (hPW.trans hWU) (hContain j)).trans
      (hAgree W (a j) P hPW (hContain j)).symm
  refine ⟨⟨D, ?_, ?_⟩, hD, hRes, fun i => ?_⟩
  · intro U W k x hx
    have hk : U.1 ≤ W.1 := toOpens_mono k.le
    have h := AffineSubalgebra.restrict_mem (U := U) (D W) hk hx
    rwa [hRes W U hk] at h
  · intro U r
    exact hRes U (U.basicOpen r) (Y.basicOpen_le r)
  · simpa only [AffineSubalgebra.restrict_refl] using hAgree (V i) i (V i) le_rfl le_rfl

private structure FiniteAtlas (f : X ⟶ Y) where
  I : Type u
  finite : Finite I
  chart : I → Y.AffineZariskiSite
  sections : ∀ i, AffineSubalgebra f (chart i)
  fg : ∀ i, (sections i).IsFinitelyGenerated
  compatible : Compatible chart sections

private def FiniteAtlas.Extends (A B : FiniteAtlas f) : Prop :=
  ∀ i : A.I, ∃ j : B.I, ∃ h : (A.chart i).1 ≤ (B.chart j).1,
    (B.sections j).restrict (U := A.chart i) h = A.sections i

private theorem FiniteAtlas.Extends.trans {A B C : FiniteAtlas f}
    (hAB : A.Extends B) (hBC : B.Extends C) : A.Extends C := by
  intro i
  obtain ⟨j, h, hres⟩ := hAB i
  obtain ⟨k, h', hres'⟩ := hBC j
  refine ⟨k, h.trans h', ?_⟩
  rw [← AffineSubalgebra.restrict_comp (C.sections k) h h', hres', hres]

private theorem exists_add_chart [IsAffineHom f] [QuasiSeparatedSpace Y]
    (A : FiniteAtlas f) (U : Y.AffineZariskiSite) :
    ∃ B : FiniteAtlas f, A.Extends B ∧ ∃ i : B.I, U.1 ≤ (B.chart i).1 := by
  have := A.finite
  obtain ⟨D, hD, hAgree⟩ := exists_extension_to_chart A.chart A.sections A.fg A.compatible U
  let V (i : Option A.I) := i.elim U A.chart
  let C : ∀ i, AffineSubalgebra f (V i)
    | none => D
    | some i => A.sections i
  have hC (i : Option A.I) : (C i).IsFinitelyGenerated := by
    cases i with
    | none => exact hD
    | some i => exact A.fg i
  have hCompat : Compatible V C := by
    intro i j W hi hj
    cases i <;> cases j
    · rfl
    · exact hAgree _ W hi hj
    · exact (hAgree _ W hj hi).symm
    · exact A.compatible _ _ W hi hj
  let B : FiniteAtlas f := ⟨Option A.I, inferInstance, V, C, hC, hCompat⟩
  refine ⟨B, fun i => ⟨some i, le_rfl, ?_⟩, ⟨none, le_rfl⟩⟩
  exact AffineSubalgebra.restrict_refl (A.sections i)

private theorem exists_atlas_over_list [IsAffineHom f] [QuasiSeparatedSpace Y]
    (L : List Y.AffineZariskiSite) (A : FiniteAtlas f) :
    ∃ B : FiniteAtlas f, A.Extends B ∧
      ∀ U ∈ L, ∃ i : B.I, U.1 ≤ (B.chart i).1 := by
  induction L generalizing A with
  | nil =>
    exact ⟨A, fun i => ⟨i, le_rfl, AffineSubalgebra.restrict_refl _⟩, by simp⟩
  | cons U L ih =>
    obtain ⟨B, hAB, i, hi⟩ := exists_add_chart A U
    obtain ⟨C, hBC, hL⟩ := ih B
    refine ⟨C, hAB.trans hBC, fun W hW => ?_⟩
    rcases List.mem_cons.mp hW with rfl | hW
    · obtain ⟨j, hj, _⟩ := hBC i
      exact ⟨j, hi.trans hj⟩
    · exact hL W hW

/-- A finitely generated subalgebra on one affine open extends to a
compatible finitely generated family over a spectral scheme. -/
theorem exists_family_extending_chart [IsAffineHom f] [SpectralSpace Y]
    (U : Y.AffineZariskiSite) (B : AffineSubalgebra f U) (hB : B.IsFinitelyGenerated) :
    ∃ C : SubalgebraFamily f, (∀ W, (C.atOpen W).IsFinitelyGenerated) ∧ C.atOpen U = B := by
  classical
  let A : FiniteAtlas f :=
    { I := PUnit.{u + 1}
      finite := inferInstance
      chart := fun _ => U
      sections := fun _ => B
      fg := fun _ => hB
      compatible := fun _ _ _ _ _ => rfl }
  have hCov : (Set.univ : Set Y) ⊆ ⋃ W : Y.AffineZariskiSite, (W.1 : Set Y) := by
    intro y _
    have hy : y ∈ ⨆ W : Y.AffineZariskiSite, W.1 :=
      (iSup_affineOpens_eq_top Y).symm ▸ trivial
    exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp hy)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun W : Y.AffineZariskiSite => (W.1 : Set Y)) (fun W => W.1.isOpen) hCov
  obtain ⟨E, hAE, hL⟩ := exists_atlas_over_list F.toList A
  have hE : (⨆ i : E.I, (E.chart i).1) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨W, hW, hy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
    obtain ⟨i, hi⟩ := hL W (by simpa using hW)
    exact Opens.mem_iSup.mpr ⟨i, hi hy⟩
  have := E.finite
  obtain ⟨C, hFG, hRes, hValues⟩ := exists_family_of_cover E.chart hE E.sections E.fg E.compatible
  obtain ⟨i, hi, hEq⟩ := hAE PUnit.unit
  refine ⟨C, hFG, ?_⟩
  have h := hRes (E.chart i) U hi
  rw [hValues i, hEq] at h
  exact h.symm

end PhilipponCompatibleSubalgebraAtlas


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.AffineZariskiSite
open PhilipponFiniteSubalgebraSchemes
open PhilipponIntegralSubalgebraLocalization (adjoin_ringHom_image_adjoin)

noncomputable section

namespace PhilipponFiniteEtaleRefinement

universe u

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

private theorem restrict_sup {U V : Y.AffineZariskiSite} (B C : AffineSubalgebra f V)
    (h : U.1 ≤ V.1) :
    letI := (f.app V.1).hom.toAlgebra
    letI := (f.app U.1).hom.toAlgebra
    ((B ⊔ C : AffineSubalgebra f V)).restrict (U := U) h =
      B.restrict (U := U) h ⊔ C.restrict (U := U) h := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  have hSup : Algebra.adjoin Γ(Y, V.1) ((B : Set Γ(X, f ⁻¹ᵁ V.1)) ∪ C) = B ⊔ C := by
    rw [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq]
  change (B ⊔ C : AffineSubalgebra f V).restrict (U := U) h =
    B.restrict (U := U) h ⊔ C.restrict (U := U) h
  nth_rw 1 [← hSup]
  unfold AffineSubalgebra.restrict
  rw [adjoin_ringHom_image_adjoin (Y.presheaf.map (homOfLE h).op).hom
    (restrictSectionsLE f h).hom (restrictSectionsLE_algebraMap f h),
    Set.image_union, Algebra.adjoin_union]

private theorem restrict_bot {U V : Y.AffineZariskiSite} (h : U.1 ≤ V.1) :
    letI := (f.app V.1).hom.toAlgebra
    letI := (f.app U.1).hom.toAlgebra
    (⊥ : AffineSubalgebra f V).restrict (U := U) h = (⊥ : AffineSubalgebra f U) := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  change (⊥ : AffineSubalgebra f V).restrict (U := U) h = (⊥ : AffineSubalgebra f U)
  apply bot_unique
  apply Algebra.adjoin_le
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hx
  change restrictSectionsLE f h (f.app V.1 r) ∈ (⊥ : AffineSubalgebra f U)
  rw [restrictSectionsLE_algebraMap]
  exact Subalgebra.algebraMap_mem _ _

private def familyOfPrincipalRestrictions (C : ∀ U, AffineSubalgebra f U)
    (h : ∀ (U : Y.AffineZariskiSite) (r : Γ(Y, U.1)),
      (C U).restrict (U := U.basicOpen r) (Y.basicOpen_le r) = C (U.basicOpen r)) :
    SubalgebraFamily f where
  atOpen := C
  restrict_mem {U V} k x hx := by
    obtain ⟨r, hr⟩ := k.le
    obtain rfl : V.basicOpen r = U := Subtype.ext hr
    change restrictSectionsLE f (Y.basicOpen_le r) x ∈ C (V.basicOpen r)
    rw [← h]
    exact AffineSubalgebra.restrict_mem (C V) _ hx
  basicOpen := h

private def scalarFamily (f : X ⟶ Y) : SubalgebraFamily f :=
  familyOfPrincipalRestrictions (fun U =>
    letI := (f.app U.1).hom.toAlgebra
    (⊥ : AffineSubalgebra f U)) (fun U r => restrict_bot (U := U.basicOpen r) (Y.basicOpen_le r))

private def joinedFamily (B C : SubalgebraFamily f) : SubalgebraFamily f :=
  familyOfPrincipalRestrictions (fun U =>
    letI := (f.app U.1).hom.toAlgebra
    B.atOpen U ⊔ C.atOpen U) (fun U r => by
      let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
      let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
        (f.app (Y.basicOpen r)).hom.toAlgebra
      have hB : (B.atOpen U).restrict (U := U.basicOpen r) (Y.basicOpen_le r) = B.atOpen (U.basicOpen r) :=
        B.basicOpen U r
      have hC : (C.atOpen U).restrict (U := U.basicOpen r) (Y.basicOpen_le r) = C.atOpen (U.basicOpen r) :=
        C.basicOpen U r
      rw [restrict_sup, hB, hC])

/-- Finitely generated subalgebras selected on finitely many affine
charts are contained in one global finitely generated family. -/
theorem exists_family_containing [IsAffineHom f] [SpectralSpace Y]
    {I : Type u} [Finite I] (U : I → Y.AffineZariskiSite)
    (B : ∀ i, AffineSubalgebra f (U i)) (hB : ∀ i, (B i).IsFinitelyGenerated) :
    ∃ C : SubalgebraFamily f, (∀ V, (C.atOpen V).IsFinitelyGenerated) ∧
      ∀ i, B i ≤ C.atOpen (U i) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  choose C hC hEq using fun i =>
    PhilipponCompatibleSubalgebraAtlas.exists_family_extending_chart (U i) (B i) (hB i)
  have hFinite (s : Finset I) :
      ∃ D : SubalgebraFamily f, (∀ V, (D.atOpen V).IsFinitelyGenerated) ∧
        ∀ i ∈ s, B i ≤ D.atOpen (U i) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨scalarFamily f, ?_, by simp⟩
      intro V
      let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
      exact Subalgebra.fg_bot
    | @insert i s hi ih =>
      obtain ⟨D, hD, hIn⟩ := ih
      refine ⟨joinedFamily (C i) D, ?_, ?_⟩
      · intro V
        let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
        exact (hC i V).sup (hD V)
      · intro j hj
        let : Algebra Γ(Y, (U j).1) Γ(X, f ⁻¹ᵁ (U j).1) := (f.app (U j).1).hom.toAlgebra
        change B j ≤ (C i).atOpen (U j) ⊔ D.atOpen (U j)
        rcases Finset.mem_insert.mp hj with hj | hj
        · subst j
          exact (hEq i).ge.trans le_sup_left
        · exact (hIn j hj).trans le_sup_right
  obtain ⟨D, hD, hIn⟩ := hFinite Finset.univ
  exact ⟨D, hD, fun i => hIn i (Finset.mem_univ i)⟩

open PhilipponIntegralEtaleRefinement (LocallyFactorsThrough)

/-- A surjective étale morphism over a spectral scheme admits a finite
surjective cover which factors through it Zariski locally. -/
theorem exists_finite_zariski_refinement_of_surjective_etale [SpectralSpace Y]
    (f : X ⟶ Y) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Y), IsFinite p ∧ Surjective p ∧
      LocallyFactorsThrough p f := by
  classical
  obtain ⟨Q, q, hInt, hSurj, hLoc⟩ :=
    AlgebraicGeometry.Scheme.exists_integral_zariski_refinement_of_surjective_etale f
  have hCov : (Set.univ : Set Y) ⊆ ⋃ U : Y.AffineZariskiSite, (U.1 : Set Y) := by
    intro y _
    have hy : y ∈ ⨆ U : Y.AffineZariskiSite, U.1 :=
      (iSup_affineOpens_eq_top Y).symm ▸ trivial
    exact Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp hy)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun U : Y.AffineZariskiSite => (U.1 : Set Y)) (fun U => U.1.isOpen) hCov
  refine PhilipponFiniteGlobalRefinement.exists_finite_refinement_of_subalgebra_extension
    q f hLoc (fun U : ↥F => U.val) ?_ ?_
  · intro y
    obtain ⟨U, hU, hy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
    exact ⟨⟨U, hU⟩, hy⟩
  · exact exists_family_containing _

end PhilipponFiniteEtaleRefinement


universe u

theorem solution {U X : Scheme.{u}} [SpectralSpace X]
    (f : U ⟶ X) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsFinite p ∧ Surjective p ∧
      ∀ x : P, ∃ (W : Scheme.{u}) (i : W ⟶ P), IsOpenImmersion i ∧ x ∈ Set.range i ∧
        ∃ g : W ⟶ U, g ≫ f = i ≫ p := by 
  exact PhilipponFiniteEtaleRefinement.exists_finite_zariski_refinement_of_surjective_etale f