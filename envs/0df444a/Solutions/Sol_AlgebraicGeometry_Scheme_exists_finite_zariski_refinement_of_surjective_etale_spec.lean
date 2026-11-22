-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale_spec
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T06:32:33.942144+00:00
-- url     : https://prove2.me/submissions/aced8265-3f64-4306-afac-19af3f4356f5

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Ring.FilteredColimits
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

/-- Over an affine base, a surjective integral morphism with a
Zariski-local factorization descends to a surjective finite morphism
with such a factorization. -/
theorem exists_finite_refinement_of_integral_algebra
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (h : LocallyFactorsThrough (Spec.map (CommRingCat.ofHom (algebraMap R A))) f) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of R)), IsFinite p ∧ Surjective p ∧
      LocallyFactorsThrough p f := by
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
  have (i : (Finset A)ᵒᵖ) : IsFinite (t.app i) := by
    have : Module.Finite R (stage R A i.unop) :=
      Algebra.finite_adjoin_of_finite_of_isIntegral i.unop.finite_toSet
        (fun a _ => Algebra.IsIntegral.isIntegral a)
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (stage R A i.unop))))
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
    infer_instance
  have hp (i : (Finset A)ᵒᵖ) : c.π.app i ≫ t.app i =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map ((finiteSubalgebraCocone R A).ι.app i.unop) ≫
      Spec.map ((structureMaps R A).app i.unop) = _
    rw [← Spec.map_comp]
    congr 1
  have : SpectralSpace (Spec (CommRingCat.of R)) :=
    inferInstanceAs (SpectralSpace (PrimeSpectrum R))
  exact PhilipponEtaleRefinementLimit.exists_finite_refinement_of_limit D t c hc f _ hp h

/-- The finite form of the étale refinement theorem over an affine base. -/
theorem exists_finite_zariski_refinement_of_surjective_etale_spec {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec R), IsFinite p ∧ Surjective p ∧
      LocallyFactorsThrough p f := by
  have : SpectralSpace (Spec R) := inferInstanceAs (SpectralSpace (PrimeSpectrum R))
  obtain ⟨Y, p, hp, hs, hloc⟩ :=
    AlgebraicGeometry.Scheme.exists_integral_zariski_refinement_of_surjective_etale f
  have : IsAffine Y := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ p)
  have hInt : IsIntegralHom (Spec.map φ) :=
    hφ.symm ▸ inferInstanceAs (IsIntegralHom (Y.isoSpec.inv ≫ p))
  have hSurj : Surjective (Spec.map φ) :=
    hφ.symm ▸ inferInstanceAs (Surjective (Y.isoSpec.inv ≫ p))
  have hLocal : LocallyFactorsThrough (Spec.map φ) f := by
    rw [hφ]
    exact LocallyFactorsThrough.precomp hloc Y.isoSpec.inv
  have hi := (IsIntegralHom.SpecMap_iff.mp hInt)
  algebraize [φ.hom]
  exact exists_finite_refinement_of_integral_algebra f hSurj hLocal

end PhilipponEtaleRefinementAffine


universe u

theorem solution {R : CommRingCat.{u}} {U : Scheme.{u}}
    (f : U ⟶ Spec R) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec R), IsFinite p ∧ Surjective p ∧
      ∀ x : P, ∃ (W : Scheme.{u}) (i : W ⟶ P), IsOpenImmersion i ∧ x ∈ Set.range i ∧
        ∃ g : W ⟶ U, g ≫ f = i ≫ p := by 
  exact PhilipponEtaleRefinementAffine.exists_finite_zariski_refinement_of_surjective_etale_spec f