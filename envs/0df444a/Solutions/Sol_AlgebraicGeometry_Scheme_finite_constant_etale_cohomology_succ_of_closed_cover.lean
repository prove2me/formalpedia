-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_succ_of_closed_cover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T18:55:46.852965+00:00
-- url     : https://prove2.me/submissions/e37fd76d-6aa9-4706-a0fb-cd8bcd294f42

import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Topology.Homeomorph.Lemmas
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_equiv_closed_direct_image

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

open AlgebraicGeometry CategoryTheory
namespace PhilipponEtaleClosedCohomology
universe u

def cohomologyEquiv {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    F.H q ≃+ ((PhilipponEtaleClosedPushforward.pushforward i).obj F).H q :=
  Classical.choice (Scheme.nonempty_etale_cohomology_equiv_closed_direct_image i F q)

end PhilipponEtaleClosedCohomology

end

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

open Set Topology

namespace PhilipponClosedCoverContinuousMaps

variable {X Y Z A : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A]

private theorem continuousOn_range {p : Y → X} (hp : IsEmbedding p)
    {h : X → A} (f : C(Y, A)) (hres : ∀ y, h (p y) = f y) :
    ContinuousOn h (range p) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (range p).domRestrict h = f ∘ hp.toHomeomorph.symm := by
    funext x
    obtain ⟨y, rfl⟩ := hp.toHomeomorph.surjective x
    simpa only [Set.domRestrict_apply, Function.comp_apply, Homeomorph.symm_apply_apply,
      IsEmbedding.toHomeomorph_apply_coe] using hres y
  rw [he]
  exact f.continuous.comp hp.toHomeomorph.symm.continuous

/-- Compatible continuous maps on two closed subspaces glue on their union. -/
theorem exists_glue {p : Y → X} {q : Z → X}
    (hp : IsClosedEmbedding p) (hq : IsClosedEmbedding q)
    (hcover : range p ∪ range q = univ) (f : C(Y, A)) (g : C(Z, A))
    (hagree : ∀ y z, p y = q z → f y = g z) :
    ∃ h : C(X, A), (∀ y, h (p y) = f y) ∧ ∀ z, h (q z) = g z := by
  classical
  have hr (x : X) (hx : x ∉ range p) : x ∈ range q := by
    have : x ∈ range p ∪ range q := hcover.symm ▸ mem_univ x
    exact this.resolve_left hx
  let h (x : X) := if hx : x ∈ range p then f hx.choose else g (hr x hx).choose
  have hleft (y : Y) : h (p y) = f y := by
    have hy : p y ∈ range p := mem_range_self y
    simp only [h, dif_pos hy, hp.injective hy.choose_spec]
  have hright (z : Z) : h (q z) = g z := by
    by_cases hz : q z ∈ range p
    · simp only [h, dif_pos hz]
      exact hagree _ z hz.choose_spec
    · simp only [h, dif_neg hz, hq.injective (hr (q z) hz).choose_spec]
  have hc := (continuousOn_range hp.isEmbedding f hleft).union_of_isClosed
    (continuousOn_range hq.isEmbedding g hright) hp.isClosed_range hq.isClosed_range
  rw [hcover, continuousOn_univ] at hc
  exact ⟨⟨h, hc⟩, hleft, hright⟩

/-- Near any point of the ambient space, a continuous map from a closed
subspace to a discrete set takes a single value on the part of the subspace
in that neighborhood. -/
theorem exists_open_constant [DiscreteTopology A] [Nonempty A] {p : Y → X}
    (hp : IsClosedEmbedding p) (f : C(Y, A)) (x : X) :
    ∃ (U : Set X) (_ : IsOpen U) (_ : x ∈ U) (a : A), ∀ y, p y ∈ U → f y = a := by
  classical
  by_cases hx : x ∈ range p
  · obtain ⟨y, rfl⟩ := hx
    let B := (f ⁻¹' ({f y} : Set A))ᶜ
    have hB : IsClosed B := ((isOpen_discrete _).preimage f.continuous).isClosed_compl
    refine ⟨(p '' B)ᶜ, (hp.isClosedMap _ hB).isOpen_compl, ?_, f y, ?_⟩
    · rintro ⟨z, hz, he⟩
      have := hp.injective he
      subst z
      exact hz rfl
    · intro z hz
      by_contra hne
      exact hz ⟨z, hne, rfl⟩
  · exact ⟨(range p)ᶜ, hp.isClosed_range.isOpen_compl, hx, Classical.arbitrary A,
      fun y hy => (hy (mem_range_self y)).elim⟩

end PhilipponClosedCoverContinuousMaps

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

private def pullbackAlong (i : Y ⟶ X) (j : Z ⟶ X) (a : Z ⟶ Y) (ha : a ≫ i = j)
    (W : X.Etale) : pullback W.hom j ⟶ pullback W.hom i :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a)
    (by rw [Category.assoc, ha, pullback.condition])

@[reassoc (attr := simp)]
private theorem pullbackAlong_fst (i : Y ⟶ X) (j : Z ⟶ X) (a : Z ⟶ Y) (ha : a ≫ i = j)
    (W : X.Etale) : pullbackAlong i j a ha W ≫ pullback.fst W.hom i =
      pullback.fst W.hom j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem pullbackAlong_snd (i : Y ⟶ X) (j : Z ⟶ X) (a : Z ⟶ Y) (ha : a ≫ i = j)
    (W : X.Etale) : pullbackAlong i j a ha W ≫ pullback.snd W.hom i =
      pullback.snd W.hom j ≫ a :=
  pullback.lift_snd _ _ _

private theorem pullbackAlong_naturality (i : Y ⟶ X) (j : Z ⟶ X) (a : Z ⟶ Y)
    (ha : a ≫ i = j) {U V : X.Etale} (g : U ⟶ V) :
    ((baseChange j).map g).left ≫ pullbackAlong i j a ha V =
      pullbackAlong i j a ha U ≫ ((baseChange i).map g).left := by
  have hs (f : Scheme.{u}) (r : f ⟶ X) :
      ((baseChange r).map g).left ≫ pullback.snd V.hom r = pullback.snd U.hom r :=
    pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackAlong_fst, projection_naturality, pullbackAlong_fst_assoc]
  · calc
      _ = pullback.snd U.hom j ≫ a := by
        rw [Category.assoc, pullbackAlong_snd, ← Category.assoc, hs]
      _ = _ := by rw [Category.assoc, hs, pullbackAlong_snd]

/-- Restriction between two direct images of the continuous coefficient
sheaves when their defining maps to the base factor. -/
def restrictionBetween (i : Y ⟶ X) (j : Z ⟶ X) (a : Z ⟶ Y) (ha : a ≫ i = j) :
    (pushforward i).obj (continuousSheaf Y A) ⟶ (pushforward j).obj (continuousSheaf Z A) :=
  ⟨{
    app W := AddCommGrpCat.ofHom (precompose A (pullbackAlong i j a ha W.unop))
    naturality {U V} f := by
      apply ConcreteCategory.hom_ext
      intro s
      change C(↥(pullback U.unop.hom i), A) at s
      apply ContinuousMap.ext
      intro x
      change s (((baseChange i).map f.unop).left (pullbackAlong i j a ha _ x)) =
        s (pullbackAlong i j a ha _ (((baseChange j).map f.unop).left x))
      exact congrArg s (congrArg (fun k : (_ : Scheme) ⟶ (_ : Scheme) => k x)
        (pullbackAlong_naturality i j a ha f.unop).symm)
  }⟩

theorem restriction_comp (i : Y ⟶ X) (j : Z ⟶ X) (a : Z ⟶ Y) (ha : a ≫ i = j) :
    restriction A i ≫ restrictionBetween A i j a ha = restriction A j := by
  apply Sheaf.hom_ext
  ext W s
  change C(W.unop.left, A) at s
  apply ContinuousMap.ext
  intro x
  change s (pullback.fst W.unop.hom i (pullbackAlong i j a ha W.unop x)) =
    s (pullback.fst W.unop.hom j x)
  rw [← Scheme.Hom.comp_apply, pullbackAlong_fst]

section Intersection

variable (i : Y ⟶ X) (j : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]

private abbrev intersectionMap : pullback i j ⟶ X := pullback.fst i j ≫ i

private abbrev legLeft (W : X.Etale) :=
  pullbackAlong i (intersectionMap i j) (pullback.fst i j) rfl W

private abbrev legRight (W : X.Etale) :=
  pullbackAlong j (intersectionMap i j) (pullback.snd i j) pullback.condition.symm W

omit [IsClosedImmersion i] [IsClosedImmersion j] in
private theorem covers_after_baseChange (h : Set.range i ∪ Set.range j = Set.univ)
    (W : X.Etale) :
    Set.range (pullback.fst W.hom i) ∪ Set.range (pullback.fst W.hom j) = Set.univ := by
  rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, ← Set.preimage_union]
  exact (congrArg (Set.preimage W.hom) h).trans Set.preimage_univ

private theorem exists_point_in_intersection (W : X.Etale)
    (x : ↥(pullback W.hom i)) (y : ↥(pullback W.hom j))
    (h : pullback.fst W.hom i x = pullback.fst W.hom j y) :
    ∃ t : ↥(pullback W.hom (intersectionMap i j)), legLeft i j W t = x ∧ legRight i j W t = y := by
  have hx := congrArg (fun f : pullback W.hom i ⟶ X => f x)
    (pullback.condition (f := W.hom) (g := i))
  have hy := congrArg (fun f : pullback W.hom j ⟶ X => f y)
    (pullback.condition (f := W.hom) (g := j))
  change W.hom (pullback.fst W.hom i x) = i (pullback.snd W.hom i x) at hx
  change W.hom (pullback.fst W.hom j y) = j (pullback.snd W.hom j y) at hy
  obtain ⟨s, hs, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback i j)
    (pullback.snd W.hom i x) (pullback.snd W.hom j y)
    (hx.symm.trans ((congrArg W.hom h).trans hy))
  obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback W.hom (intersectionMap i j))
    (pullback.fst W.hom i x) s (hx.trans (congrArg i hs).symm)
  refine ⟨t, (pullback.fst W.hom i).isClosedEmbedding.injective ?_,
    (pullback.fst W.hom j).isClosedEmbedding.injective ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullbackAlong_fst, ht]
  · rw [← Scheme.Hom.comp_apply, pullbackAlong_fst, ht, h]

omit [AddCommGroup A] [DiscreteTopology A] in
/-- Agreement on the scheme-theoretic intersection suffices to glue two
sections of the continuous coefficient sheaf over an étale object. -/
theorem exists_glued_section (h : Set.range i ∪ Set.range j = Set.univ) (W : X.Etale)
    (s : C(↥(pullback W.hom i), A)) (t : C(↥(pullback W.hom j), A))
    (hc : ∀ z : ↥(pullback W.hom (intersectionMap i j)), s (legLeft i j W z) = t (legRight i j W z)) :
    ∃ f : C(W.left, A), (∀ x, f (pullback.fst W.hom i x) = s x) ∧
      ∀ y, f (pullback.fst W.hom j y) = t y := by
  apply PhilipponClosedCoverContinuousMaps.exists_glue
    (pullback.fst W.hom i).isClosedEmbedding (pullback.fst W.hom j).isClosedEmbedding
    (covers_after_baseChange i j h W) s t
  intro x y hxy
  obtain ⟨z, h₁, h₂⟩ := exists_point_in_intersection i j W x y hxy
  simpa only [h₁, h₂] using hc z

private abbrev coeff {U : Scheme.{u}} (f : U ⟶ X) :=
  (pushforward f).obj (continuousSheaf U A)

private abbrev restrictionLeft :=
  restrictionBetween A i (intersectionMap i j) (pullback.fst i j) rfl

private abbrev restrictionRight :=
  restrictionBetween A j (intersectionMap i j) (pullback.snd i j) pullback.condition.symm

/-- The difference sequence for a pair of closed subschemes. -/
def differenceSequence :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk (biprod.lift (restriction A i) (restriction A j))
    (biprod.fst ≫ restrictionLeft A i j - biprod.snd ≫ restrictionRight A i j) (by
      simp [Preadditive.comp_sub, restriction_comp])

private abbrev sections (W : X.Etaleᵒᵖ) :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj W

private instance (W : X.Etaleᵒᵖ) : (sections W).Additive where
  map_add := rfl

private instance (W : X.Etaleᵒᵖ) : PreservesBinaryBiproducts (sections W) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

private abbrev sectionsPair (W : X.Etaleᵒᵖ) :
    (sections W).obj (coeff A i ⊞ coeff A j) ≅
      AddCommGrpCat.of (C(↥(pullback W.unop.hom i), A) × C(↥(pullback W.unop.hom j), A)) :=
  ((sections W).mapBiprod (coeff A i) (coeff A j)) ≪≫
    AddCommGrpCat.biprodIsoProd ((sections W).obj (coeff A i)) ((sections W).obj (coeff A j))

private theorem sectionsPair_fst (W : X.Etaleᵒᵖ) :
    (sectionsPair A i j W).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (sections W).map (biprod.fst : coeff A i ⊞ coeff A j ⟶ _) := by
  change (sectionsPair A i j W).hom ≫ AddCommGrpCat.ofHom
    (AddMonoidHom.fst ((sections W).obj (coeff A i)) ((sections W).obj (coeff A j))) = _
  rw [sectionsPair, Iso.trans_hom, Category.assoc, ← AddCommGrpCat.biprodIsoProd_inv_comp_fst,
    Iso.hom_inv_id_assoc, Functor.mapBiprod_hom, biprod.lift_fst]

private theorem sectionsPair_snd (W : X.Etaleᵒᵖ) :
    (sectionsPair A i j W).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (sections W).map (biprod.snd : coeff A i ⊞ coeff A j ⟶ _) := by
  change (sectionsPair A i j W).hom ≫ AddCommGrpCat.ofHom
    (AddMonoidHom.snd ((sections W).obj (coeff A i)) ((sections W).obj (coeff A j))) = _
  rw [sectionsPair, Iso.trans_hom, Category.assoc, ← AddCommGrpCat.biprodIsoProd_inv_comp_snd,
    Iso.hom_inv_id_assoc, Functor.mapBiprod_hom, biprod.lift_snd]

private theorem restrictions_apply (W : X.Etaleᵒᵖ) (s : C(W.unop.left, A)) :
    (sectionsPair A i j W).hom ((sections W).map (differenceSequence A i j).f s) =
      (precompose A (pullback.fst W.unop.hom i) s, precompose A (pullback.fst W.unop.hom j) s) := by
  apply Prod.ext
  · have e : (sections W).map (differenceSequence A i j).f ≫
        ((sectionsPair A i j W).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) =
        (sections W).map (restriction A i) := by
      rw [sectionsPair_fst, ← Functor.map_comp]
      simp [differenceSequence]
    exact ConcreteCategory.congr_hom e s
  · have e : (sections W).map (differenceSequence A i j).f ≫
        ((sectionsPair A i j W).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) =
        (sections W).map (restriction A j) := by
      rw [sectionsPair_snd, ← Functor.map_comp]
      simp [differenceSequence]
    exact ConcreteCategory.congr_hom e s

private theorem difference_apply (W : X.Etaleᵒᵖ)
    (s : (sections W).obj (coeff A i ⊞ coeff A j)) :
    (sections W).map (differenceSequence A i j).g s =
      precompose A (legLeft i j W.unop) ((sectionsPair A i j W).hom s).1 -
        precompose A (legRight i j W.unop) ((sectionsPair A i j W).hom s).2 := by
  change (sections W).map
      (biprod.fst ≫ restrictionLeft A i j - biprod.snd ≫ restrictionRight A i j) s = _
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, ← sectionsPair_fst, ← sectionsPair_snd]
  rfl

private theorem mappedF_injective (h : Set.range i ∪ Set.range j = Set.univ) (W : X.Etaleᵒᵖ) :
    Function.Injective ((sections W).map (differenceSequence A i j).f) := by
  intro a b hab
  have he := congrArg ((sectionsPair A i j W).hom) hab
  change C(W.unop.left, A) at a b
  rw [restrictions_apply, restrictions_apply] at he
  apply ContinuousMap.ext
  intro x
  have hx : x ∈ Set.range (pullback.fst W.unop.hom i) ∪ Set.range (pullback.fst W.unop.hom j) :=
    (covers_after_baseChange i j h W.unop).symm ▸ Set.mem_univ x
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hx
  · exact congrArg (fun k => k.1 y) he
  · exact congrArg (fun k => k.2 y) he

private def sectionsKernel (h : Set.range i ∪ Set.range j = Set.univ) (W : X.Etaleᵒᵖ) :
    IsLimit ((KernelFork.ofι _ (differenceSequence A i j).zero).map (sections W)) := by
  let S := (differenceSequence A i j).map (sections W)
  have : Mono S.f := (AddCommGrpCat.mono_iff_injective S.f).mpr (mappedF_injective A i j h W)
  have hS : S.Exact := (ShortComplex.ab_exact_iff_function_exact S).mpr (by
    intro s
    constructor
    · intro hs
      have hd := difference_apply A i j W s
      change S.g s = 0 at hs
      change S.g s = _ at hd
      rw [hs, eq_comm, sub_eq_zero] at hd
      obtain ⟨a, px, py⟩ := exists_glued_section A i j h W.unop
        ((sectionsPair A i j W).hom s).1 ((sectionsPair A i j W).hom s).2
        (fun z => congrArg (fun f : C(↥(pullback W.unop.hom (intersectionMap i j)), A) => f z) hd)
      refine ⟨a, (AddCommGrpCat.mono_iff_injective (sectionsPair A i j W).hom).mp
        inferInstance ?_⟩
      change (sectionsPair A i j W).hom ((sections W).map (differenceSequence A i j).f a) = _
      rw [restrictions_apply]
      exact Prod.ext (ContinuousMap.ext px) (ContinuousMap.ext py)
    · rintro ⟨a, rfl⟩
      exact ConcreteCategory.congr_hom S.zero a)
  exact hS.fIsKernel

private theorem epi_difference : Epi (differenceSequence A i j).g := by
  let S := differenceSequence A i j
  apply (Sheaf.isLocallySurjective_iff_epi' (J := X.smallEtaleTopology)
    AddCommGrpCat.{u} S.g).mp
  constructor
  intro W s
  let p := pullback.fst W.hom (intersectionMap i j)
  have hclosed : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion
    (pullback.fst W.hom (pullback.fst i j ≫ i)))
  change C(↥(pullback W.hom (intersectionMap i j)), A) at s
  choose U hU hx a ha using fun x : W.left =>
    PhilipponClosedCoverContinuousMaps.exists_open_constant p.isClosedEmbedding s x
  let D (x : W.left) : W.left.Opens := ⟨U x, hU x⟩
  let V (x : W.left) := Scheme.Etale.mk ((D x).ι ≫ W.hom)
  let f (x : W.left) : V x ⟶ W := MorphismProperty.Over.homMk (D x).ι rfl trivial
  have hc : Sieve.ofArrows V f ∈ X.smallEtaleTopology W :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
      (Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨x, ⟨⟨x, hx x⟩, rfl⟩⟩)
  apply X.smallEtaleTopology.superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨x⟩
  let b := (sectionsPair A i j (op W)).inv (ContinuousMap.const _ (a x), 0)
  have hb : (sectionsPair A i j (op W)).hom b = (ContinuousMap.const _ (a x), 0) := by
    exact ConcreteCategory.congr_hom (sectionsPair A i j (op W)).inv_hom_id _
  refine ⟨S.X₂.obj.map (f x).op b, ?_⟩
  rw [NatTrans.naturality_apply]
  change S.X₃.obj.map (f x).op ((sections (op W)).map (differenceSequence A i j).g b) = _
  rw [difference_apply, hb]
  apply ContinuousMap.ext
  intro y
  let z := ((baseChange (intersectionMap i j)).map (f x)).left y
  have hz : p z ∈ U x := by
    have e := congrArg (fun k : (_ : Scheme) ⟶ (_ : Scheme) => k y)
      (projection_naturality (intersectionMap i j) (f x))
    change p z = ((D x).ι) (pullback.fst (V x).hom (intersectionMap i j) y) at e
    rw [e]
    exact (pullback.fst (V x).hom (intersectionMap i j) y).property
  change a x - (0 : A) = s z
  rw [sub_zero, ha x _ hz]

/-- The restriction and difference maps give a short exact sequence for a
cover by closed subschemes on the small étale site. -/
theorem differenceSequence_shortExact (h : Set.range i ∪ Set.range j = Set.univ) :
    (differenceSequence A i j).ShortExact := by
  let S := differenceSequence A i j
  let F := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let c := KernelFork.ofι S.f S.zero
  have hc : IsLimit c := by
    apply isLimitOfReflects F
    apply evaluationJointlyReflectsLimits
    intro W
    change IsLimit ((sections W).mapCone c)
    exact (c.isLimitMapConeEquiv (sections W)).symm (sectionsKernel A i j h W)
  exact ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel hc)
    (mono_of_isLimit_fork hc) (epi_difference A i j)

end Intersection

end PhilipponEtaleClosedCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PhilipponEtaleClosedCover
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleClosedCohomology (cohomologyEquiv)
open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso)


namespace PhilipponEtaleClosedCoverFiniteness

universe u
private abbrev AbelianSheaves (W : Scheme.{u}) := Sheaf W.smallEtaleTopology AddCommGrpCat.{u}

private abbrev H {W : Scheme.{u}} (F : AbelianSheaves W) (q : ℕ) : Type u := F.H q

private theorem finite_of_shortExact_succ {W : Scheme.{u}} {S : ShortComplex (AbelianSheaves W)}
    (hS : S.ShortExact) (q : ℕ) (h₂ : Finite (H S.X₂ (q + 1))) (h₃ : Finite (H S.X₃ q)) :
    Finite (H S.X₁ (q + 1)) := by
  let Q := (constantSheaf W.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let δ : H S.X₃ q →+ H S.X₁ (q + 1) := hS.extClass.postcomp Q rfl
  let f : H S.X₁ (q + 1) →+ H S.X₂ (q + 1) := Sheaf.H.map S.f (q + 1)
  have hex : f.ker ≤ δ.range := by
    intro x hx
    exact Ext.covariant_sequence_exact₁ Q hS x hx rfl
  letI : Fintype (H S.X₃ q) := @Fintype.ofFinite _ h₃
  letI : Fintype (H S.X₂ (q + 1)) := @Fintype.ofFinite _ h₂
  exact @Finite.of_fintype _ (AddGroup.fintypeOfKerLeRange δ f hex)

variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private theorem finite_biprod_cohomology {W : Scheme.{u}} (F G : AbelianSheaves W) (q : ℕ)
    (hF : Finite (H F q)) (hG : Finite (H G q)) :
    Finite (H (F ⊞ G) q) := by
  let Hq : AbelianSheaves W ⥤ AddCommGrpCat.{u} := Sheaf.functorH W.smallEtaleTopology q
  have : PreservesBinaryBiproducts Hq := preservesBinaryBiproducts_of_preservesBinaryProducts _
  let e := (Hq.mapBiprod F G ≪≫ AddCommGrpCat.biprodIsoProd (Hq.obj F) (Hq.obj G))
  exact e.addCommGroupIsoToAddEquiv.toEquiv.finite_iff.mpr (inferInstance : Finite (H F q × H G q))

/-- Finiteness in degree `q+1` on two closed pieces and in degree `q` on
their scheme-theoretic intersection implies finiteness in degree `q+1`
on the scheme they cover. -/
theorem finite_succ_of_closed_cover {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i ∪ Set.range j = Set.univ)
    (q : ℕ)
    (hy : Finite (H (continuousSheaf Y A) (q + 1)))
    (hz : Finite (H (continuousSheaf Z A) (q + 1)))
    (ht : Finite (H (continuousSheaf (pullback i j) A) q)) :
    Finite (H (continuousSheaf X A) (q + 1)) := by
  let S := differenceSequence A i j
  have hS : S.ShortExact := differenceSequence_shortExact A i j h
  have h₂ : Finite (H S.X₂ (q + 1)) :=
    finite_biprod_cohomology _ _ (q + 1)
      ((cohomologyEquiv i (continuousSheaf Y A) (q + 1)).toEquiv.finite_iff.mp hy)
      ((cohomologyEquiv j (continuousSheaf Z A) (q + 1)).toEquiv.finite_iff.mp hz)
  have h₃ : Finite (H S.X₃ q) :=
    (cohomologyEquiv (pullback.fst i j ≫ i) (continuousSheaf (pullback i j) A) q).toEquiv.finite_iff.mp ht
  exact finite_of_shortExact_succ hS q h₂ h₃

end PhilipponEtaleClosedCoverFiniteness

end

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso)

theorem solution
    {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i ∪ Set.range j = Set.univ)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (hy : Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H (q + 1)))
    (hz : Finite (((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H (q + 1)))
    (ht : Finite (((constantSheaf (pullback i j).smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H (q + 1)) := by 
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have compare (W : Scheme.{u}) (n : ℕ) :
      Finite (((constantSheaf W.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of A)).H n) ↔ Finite ((continuousSheaf W A).H n) :=
    ((Sheaf.functorH W.smallEtaleTopology n).mapIso
      (constantSheafIso W A)).addCommGroupIsoToAddEquiv.toEquiv.finite_iff
  exact (compare X _).mpr
    (PhilipponEtaleClosedCoverFiniteness.finite_succ_of_closed_cover A i j h q
      ((compare Y _).mp hy) ((compare Z _).mp hz) ((compare _ _).mp ht))

end
