-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_etale_representation_constant_torsor_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T08:04:36.779089+00:00
-- url     : https://prove2.me/submissions/334ca4ff-c64e-40da-8b56-3c445f7bf6ea

import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.Topology.ContinuousMap.Basic

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleConstantDegreeZero

universe u
variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

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
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponSchemeConstantSection

universe u

variable (I : Type u) [TopologicalSpace I] [DiscreteTopology I]

private abbrev copies (X : Scheme.{u}) : I → Scheme.{u} := fun _ => X

/-- The structure map from the disjoint union of copies of a scheme. -/
def projection (X : Scheme.{u}) : (∐ copies I X) ⟶ X := Sigma.desc (fun _ => 𝟙 X)

/-- The component index is a continuous map to the discrete index set. -/
def component (X : Scheme.{u}) : C(↥(∐ copies I X : Scheme.{u}), I) :=
  ⟨fun x => ((sigmaMk (copies I X)).symm x).1,
    (continuous_sigma_iff.mpr (fun _ => continuous_const)).comp
      (sigmaMk (copies I X)).symm.continuous⟩

omit [DiscreteTopology I] in
@[simp]
theorem component_ι (X : Scheme.{u}) (i : I) (x : X) :
    component I X (Sigma.ι (copies I X) i x) = i := by
  change ((sigmaMk (copies I X)).symm (Sigma.ι (copies I X) i x)).1 = i
  rw [← sigmaMk_mk, Homeomorph.symm_apply_apply]

/-- The map of constant schemes over a map of bases. -/
def mapCopies {X Y : Scheme.{u}} (p : Y ⟶ X) : (∐ copies I Y) ⟶ (∐ copies I X) :=
  CategoryTheory.Limits.Sigma.map (fun _ => p)

omit [TopologicalSpace I] [DiscreteTopology I] in
theorem mapCopies_projection {X Y : Scheme.{u}} (p : Y ⟶ X) :
    mapCopies I p ≫ projection I X = projection I Y ≫ p := by
  apply Sigma.hom_ext
  intro i
  simp [mapCopies, projection]

omit [DiscreteTopology I] in
@[simp] theorem component_mapCopies {X Y : Scheme.{u}} (p : Y ⟶ X) (z : (∐ copies I Y : Scheme.{u})) :
    component I X (mapCopies I p z) = component I Y z := by
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk (copies I Y)).surjective z
  rw [sigmaMk_mk] at hy
  rw [← hy, component_ι, ← Scheme.Hom.comp_apply, mapCopies, Sigma.ι_map, Scheme.Hom.comp_apply, component_ι]

private def fiberOpen {Y : Scheme.{u}} (k : C(Y, I)) (i : I) : Y.Opens :=
  ⟨k ⁻¹' {i}, (isOpen_discrete {i}).preimage k.continuous⟩

private def fiberCover {Y : Scheme.{u}} (k : C(Y, I)) : Y.OpenCover where
  I₀ := I
  X i := (fiberOpen I k i).toScheme
  f i := (fiberOpen I k i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x => ⟨k x, ⟨⟨x, rfl⟩, rfl⟩⟩, fun _ => inferInstance⟩

private theorem fiberCover_apply {Y : Scheme.{u}} (k : C(Y, I)) (i : I)
    (z : (fiberCover I k).X i) : k ((fiberCover I k).f i z) = i := z.property

omit [DiscreteTopology I] in
private theorem eq_ι_of_component_const {Y X T : Scheme.{u}} {p : Y ⟶ X}
    {f : Y ⟶ (∐ copies I X)} (hf : f ≫ projection I X = p) (g : T ⟶ Y) (i : I)
    (h : ∀ x : T, component I X (f (g x)) = i) :
    g ≫ f = g ≫ p ≫ Sigma.ι (copies I X) i := by
  let j := Sigma.ι (copies I X) i
  have hi : Set.range (g ≫ f) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    let t := (sigmaMk (copies I X)).symm (f (g x))
    have ht : t.1 = i := h x
    have hz : sigmaMk (copies I X) t = f (g x) :=
      (sigmaMk (copies I X)).apply_symm_apply _
    obtain ⟨a, y⟩ := t
    change a = i at ht
    subst a
    exact ⟨y, (sigmaMk_mk (copies I X) i y).symm.trans hz⟩
  let l := IsOpenImmersion.lift j (g ≫ f) hi
  have hl : l ≫ j = g ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hl' : l = g ≫ p := by
    calc
      l = (l ≫ j) ≫ projection I X := by
        rw [Category.assoc, show j ≫ projection I X = 𝟙 X from Sigma.ι_desc _ _, Category.comp_id]
      _ = g ≫ p := by rw [hl, Category.assoc, hf]
  exact hl.symm.trans (congrArg (· ≫ j) hl')

/-- Maps over `X` to the constant scheme with index set `I` are precisely
continuous index functions on the source. -/
def homEquivContinuous {X Y : Scheme.{u}} (p : Y ⟶ X) :
    {f : Y ⟶ (∐ copies I X) // f ≫ projection I X = p} ≃ C(Y, I) := by
  classical
  let indexMap (f : {f : Y ⟶ (∐ copies I X) // f ≫ projection I X = p}) : C(Y, I) :=
    (component I X).comp ⟨f.val, f.val.continuous⟩
  apply Equiv.ofBijective indexMap
  constructor
  · intro f g h
    apply Subtype.ext
    let V := fiberCover I (indexMap f)
    apply V.hom_ext
    intro i
    have hf (z : V.X i) : component I X (f.val (V.f i z)) = i := by
      exact fiberCover_apply I (indexMap f) i z
    have hg (z : V.X i) : component I X (g.val (V.f i z)) = i :=
      (congrArg (fun k : C(Y, I) => k (V.f i z)) h).symm.trans (hf z)
    exact (eq_ι_of_component_const I f.property (V.f i) i hf).trans
      (eq_ι_of_component_const I g.property (V.f i) i hg).symm
  · intro k
    let V := fiberCover I k
    let b (i : I) := V.f i ≫ p ≫ Sigma.ι (copies I X) i
    have hGlue (i j : I) : pullback.fst (V.f i) (V.f j) ≫ b i = pullback.snd (V.f i) (V.f j) ≫ b j := by
      by_cases h : i = j
      · subst j
        simpa only [b, ← Category.assoc] using
          congrArg (· ≫ p ≫ Sigma.ι (copies I X) i) (pullback.condition (f := V.f i) (g := V.f i))
      · let D := pullback (V.f i) (V.f j)
        let l : D ⟶ V.X i := pullback.fst _ _
        let r : D ⟶ V.X j := pullback.snd _ _
        let : IsEmpty ↥D := ⟨fun z =>
          h ((fiberCover_apply I k i (l z)).symm.trans
            ((congrArg (fun d : D ⟶ Y => k (d z)) (pullback.condition (f := V.f i) (g := V.f j))).trans
              (fiberCover_apply I k j (r z))))⟩
        exact (isInitialOfIsEmpty (X := D)).hom_ext _ _
    let f := V.glueMorphisms b hGlue
    have hf (i : I) : V.f i ≫ f = b i := V.ι_glueMorphisms b hGlue i
    have hp : f ≫ projection I X = p := by
      apply V.hom_ext
      intro i
      rw [← Category.assoc, hf]
      simp only [b, projection, Category.assoc, Sigma.ι_desc, Category.comp_id]
    refine ⟨⟨f, hp⟩, ?_⟩
    ext x
    obtain ⟨i, y, rfl⟩ := V.exists_eq x
    change I at i
    change component I X ((V.f i ≫ f) y) = k (V.f i y)
    rw [hf i]
    exact (component_ι I X i (p (V.f i y))).trans (fiberCover_apply I k i y).symm

@[simp]
theorem homEquivContinuous_apply {X Y : Scheme.{u}} (p : Y ⟶ X)
    (f : {f : Y ⟶ (∐ copies I X) // f ≫ projection I X = p}) (y : Y) :
    homEquivContinuous I p f y = component I X (f.val y) := rfl

/-- The constant scheme on a fixed set commutes with change of base. -/
theorem isPullback_mapCopies_projection {X Y : Scheme.{u}} (p : Y ⟶ X) :
    IsPullback (projection I Y) (mapCopies I p) p (projection I X) := by
  let cone := PullbackCone.mk (projection I Y) (mapCopies I p) (mapCopies_projection I p).symm
  apply (IsPullback.of_isLimit (c := cone))
  refine PullbackCone.isLimitAux' cone (fun s => ?_)
  let a : C(s.pt, I) := (component I X).comp ⟨s.snd, s.snd.continuous⟩
  let t := (homEquivContinuous I s.fst).symm a
  have hIndex (x : s.pt) : component I Y (t.val x) = a x := by
    simpa only [homEquivContinuous_apply] using
      congrArg (fun k : C(s.pt, I) => k x) ((homEquivContinuous I s.fst).apply_symm_apply a)
  have hRight : t.val ≫ mapCopies I p = s.snd := by
    have hOver : (t.val ≫ mapCopies I p) ≫ projection I X = s.fst ≫ p := by
      rw [Category.assoc, mapCopies_projection, ← Category.assoc, t.property]
    let m : {f : s.pt ⟶ (∐ copies I X) // f ≫ projection I X = s.fst ≫ p} := ⟨_, hOver⟩
    let n : {f : s.pt ⟶ (∐ copies I X) // f ≫ projection I X = s.fst ≫ p} := ⟨s.snd, s.condition.symm⟩
    apply congrArg Subtype.val ((homEquivContinuous I (s.fst ≫ p)).injective (show
        homEquivContinuous I (s.fst ≫ p) m = homEquivContinuous I (s.fst ≫ p) n from ?_))
    ext x
    simp only [homEquivContinuous_apply, m, n, Scheme.Hom.comp_apply, component_mapCopies, hIndex]
    rfl
  refine ⟨t.val, t.property, hRight, fun {m} hm₁ hm₂ => ?_⟩
  let m' : {f : s.pt ⟶ (∐ copies I Y) // f ≫ projection I Y = s.fst} := ⟨m, hm₁⟩
  apply congrArg Subtype.val ((homEquivContinuous I s.fst).injective (show
      homEquivContinuous I s.fst m' = homEquivContinuous I s.fst t from ?_))
  ext x
  simp only [homEquivContinuous_apply, m', hIndex]
  change component I Y (m x) = component I X (s.snd x)
  rw [← hm₂]
  exact (component_mapCopies I p (m x)).symm

/-- A finite constant scheme is finite étale over its base. -/
theorem finite_etale_projection [Finite I] (X : Scheme.{u}) :
    IsFinite (projection I X) ∧ Etale (projection I X) := by
  let R := ULift.{u} ℤ
  let B : CommRingCat.{u} := .of R
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (I → R)))
  let : Fintype I := Fintype.ofFinite I
  let : IsFinite f := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have he : sigmaSpec (fun _ : I => B) ≫ f = projection I (Spec B) := by
    apply Sigma.hom_ext
    intro i
    rw [ι_sigmaSpec_assoc, projection, Sigma.ι_desc, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  have hFinite : IsFinite (projection I (Spec B)) := he ▸ inferInstanceAs (IsFinite (sigmaSpec (fun _ : I => B) ≫ f))
  refine ⟨MorphismProperty.of_isPullback (isPullback_mapCopies_projection I
    (specULiftZIsTerminal.from X)).flip hFinite, ?_⟩
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)

end PhilipponSchemeConstantSection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso)
open PhilipponSchemeConstantSection (component projection finite_etale_projection homEquivContinuous)


namespace PhilipponEtaleConstantFiniteRepresentability

universe u

variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]

/-- The finite étale chart consisting of one copy of the base per coefficient. -/
def constantChart : X.Etale := by
  let : Etale (projection A X) := (finite_etale_projection A X).2
  exact Scheme.Etale.mk (projection A X)

omit [AddCommGroup A] in
theorem isFinite_constantChart : IsFinite (constantChart X A).hom :=
  (finite_etale_projection A X).1

private def overCoproductEquiv (U : X.Etale) :
    (U ⟶ constantChart X A) ≃ {r : U.left ⟶ (∐ fun _ : A => X) // r ≫ projection A X = U.hom} where
  toFun a := ⟨a.left, MorphismProperty.Over.w a⟩
  invFun r := MorphismProperty.Over.homMk r.val r.property trivial
  left_inv _ := MorphismProperty.Over.Hom.ext rfl
  right_inv _ := Subtype.ext rfl

private def representedContinuousSections :
    yoneda.obj (constantChart X A) ≅ (continuousSheaf X A).obj ⋙ forget AddCommGrpCat.{u} := by
  let e (U : X.Etaleᵒᵖ) : (yoneda.obj (constantChart X A)).obj U ≃
      ((continuousSheaf X A).obj ⋙ forget AddCommGrpCat.{u}).obj U :=
    (overCoproductEquiv X A U.unop).trans (homEquivContinuous A U.unop.hom)
  refine NatIso.ofComponents (fun U => Equiv.toIso (e U)) ?_
  intro U V f
  apply ConcreteCategory.hom_ext
  intro a
  change e V (f.unop ≫ a) = ((continuousSheaf X A).obj ⋙ forget AddCommGrpCat.{u}).map f (e U a)
  apply ContinuousMap.ext
  intro x
  rfl

/-- The underlying sheaf of sets of a finite constant abelian sheaf is
represented on the small étale site by the finite constant scheme. -/
def representsConstant : yoneda.obj (constantChart X A) ≅
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).obj ⋙
      forget AddCommGrpCat.{u} :=
  representedContinuousSections X A ≪≫
    Functor.isoWhiskerRight ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      (constantSheafIso X A).symm) (forget AddCommGrpCat.{u})

end PhilipponEtaleConstantFiniteRepresentability

end

section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers PhilipponTorsorInvariantDescent

namespace PhilipponAffineEtaleTorsorCover
universe u

/-- Over an affine scheme, a torsor has sections on a finite
jointly surjective family of affine étale objects. -/
theorem exists_affine_family (X : Scheme.{u}) [IsAffine X]
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (A : Torsor G) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Etale),
      (∀ i, IsAffine (V i).left) ∧ (∀ i, Nonempty (A.D.P.obj (op (V i)))) ∧
      ∀ x : X, ∃ (i : ι) (y : (V i).left), (V i).hom y = x := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let R := presence A.D.P T
  have hR : R ∈ X.smallEtaleTopology T := A.locally_nonempty T
  obtain ⟨U, hOver, hU, h⟩ := (Scheme.mem_smallGrothendieckTopology T R).mp hR
  let : U.Over X := hOver
  let : QuasiCompactCover U.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i => (U.f i).isOpenMap)
  let : CompactSpace T.left := inferInstanceAs (CompactSpace X)
  obtain ⟨W, r, hfin, _⟩ := QuasiCompactCover.exists_hom.{u} U
  let : ∀ i, Etale (W.f i) := fun i => W.cover.map_prop i
  let V (i : W.I₀) : X.Etale := Scheme.Etale.mk (W.f i)
  refine ⟨W.I₀, hfin, V, fun i => inferInstanceAs (IsAffine (Spec (W.X i))), ?_, ?_⟩
  · intro i
    let j := r.s₀ i
    let Uj := (U.X j).asOverProp X (hU j)
    let u : Uj ⟶ T := (U.f j).asOverProp X
    have hu : U.toPresieveOverProp hU u := ⟨j⟩
    obtain ⟨s⟩ : Nonempty (A.D.P.obj (op Uj)) := h _ _ hu
    have huj : (U.f j) = Uj.hom := by
      change U.f j = U.X j ↘ X
      exact (Category.comp_id (U.f j)).symm.trans (comp_over (U.f j) X)
    let v : V i ⟶ Uj := MorphismProperty.Over.homMk (r.h₀ i)
      ((congrArg (r.h₀ i ≫ ·) huj.symm).trans (r.w₀ i)) trivial
    exact ⟨A.D.P.map v.op s⟩
  · intro x
    obtain ⟨y, hy⟩ := W.covers x
    exact ⟨W.idx x, y, hy⟩

private theorem sections_subsingleton_of_empty {X : Scheme.{u}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (A : Torsor G) {W : X.Etale}
    (hW : IsEmpty W.left) : Subsingleton (A.D.P.obj (op W)) := by
  let V : Empty → X.Etale := Empty.elim
  let p (i : Empty) : V i ⟶ W := Empty.elim i
  have hCover : Sieve.ofArrows V p ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr
    exact Set.ext fun x => (hW.false x).elim
  have hBot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Empty.elim i
  refine ⟨fun x y => ?_⟩
  apply (A.isSheaf.isSheafFor _ hBot).isSeparatedFor.ext
  intro _ _ h
  exact h.elim

/-- A torsor over an affine scheme has a section on one affine
surjective étale scheme. -/
theorem exists_affine_object (X : Scheme.{u}) [IsAffine X]
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (A : Torsor G) :
    ∃ E : X.Etale, IsAffine E.left ∧ Function.Surjective E.hom ∧
      Nonempty (A.D.P.obj (op E)) := by
  obtain ⟨ι, hfin, V, ha, hs, hsur⟩ := exists_affine_family X A
  let : Finite ι := hfin
  let Y := fun i : ι => (V i).left
  let : ∀ i, IsAffine (Y i) := ha
  let q : (∐ Y) ⟶ X := Sigma.desc (fun i => (V i).hom)
  let : Etale q := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover Y)).mpr
    intro i
    change Etale (Sigma.ι Y i ≫ q)
    rw [Sigma.ι_desc]
    exact (V i).prop
  let E : X.Etale := Scheme.Etale.mk q
  let j (i : ι) : V i ⟶ E :=
    MorphismProperty.Over.homMk (Sigma.ι Y i) (Sigma.ι_desc _ _) trivial
  refine ⟨E, inferInstanceAs (IsAffine (∐ Y)), ?_, ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := hsur x
    refine ⟨Sigma.ι Y i y, ?_⟩
    change (Sigma.ι Y i ≫ q) y = x
    rw [Sigma.ι_desc]
    exact hy
  · have hCover : Sieve.ofArrows V j ∈ X.smallEtaleTopology E := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      let oc := sigmaOpenCover Y
      obtain ⟨y, hy⟩ := oc.covers x
      exact ⟨oc.idx x, y, hy⟩
    have hSheaf : Presieve.IsSheafFor A.D.P (.ofArrows V j) :=
      (Presieve.isSheafFor_iff_generate (.ofArrows V j)).mpr (A.isSheaf.isSheafFor _ hCover)
    let s (i : ι) : A.D.P.obj (op (V i)) := (hs i).some
    have hCompat : Presieve.Arrows.Compatible A.D.P j s := by
      intro i k W a b h
      have hh : a.left ≫ Sigma.ι Y i = b.left ≫ Sigma.ι Y k :=
        congrArg (fun t : W ⟶ E => t.left) h
      by_cases hEq : i = k
      · subst k
        have hSame : a = b := MorphismProperty.Over.Hom.ext ((cancel_mono (Sigma.ι Y i)).mp hh)
        rw [hSame]
      · exact (sections_subsingleton_of_empty A (isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ hEq)).elim _ _
    obtain ⟨s', _, _⟩ := (Presieve.isSheafFor_arrows_iff (π := j) (P := A.D.P)).mp hSheaf s hCompat
    exact ⟨s'⟩

/-- The affine covering object can be presented as the spectrum of
a faithfully flat étale ring extension. -/
theorem exists_spec_cover (R : CommRingCat.{u})
    {G : Sheaf (Spec R).smallEtaleTopology AddCommGrpCat.{u}} (A : Torsor G) :
    ∃ (S : CommRingCat.{u}) (f : R ⟶ S) (_ : Etale (Spec.map f)),
      f.hom.FaithfullyFlat ∧ Nonempty (A.D.P.obj (op (Scheme.Etale.mk (Spec.map f)))) := by
  obtain ⟨E, ha, hsur, ⟨s⟩⟩ := exists_affine_object (Spec R) A
  let : IsAffine E.left := ha
  let : Etale E.hom := E.prop
  let : Surjective E.hom := ⟨hsur⟩
  let g := E.left.isoSpec.inv ≫ E.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective g
  let : Etale (Spec.map f) := by
    rw [hf]
    exact inferInstanceAs (Etale (E.left.isoSpec.inv ≫ E.hom))
  have hs : Surjective (Spec.map f) := by
    rw [hf]
    exact inferInstanceAs (Surjective (E.left.isoSpec.inv ≫ E.hom))
  have hff := (flat_and_surjective_SpecMap_iff f).mp ⟨inferInstance, hs⟩
  let e : Scheme.Etale.mk (Spec.map f) ⟶ E :=
    MorphismProperty.Over.homMk E.left.isoSpec.inv hf.symm trivial
  exact ⟨_, f, inferInstance, hff, ⟨A.D.P.map e.op s⟩⟩

end PhilipponAffineEtaleTorsorCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open PhilipponTorsorSectionFibers (Torsor)


namespace PhilipponTorsorTrivialization

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J AddCommGrpCat.{w}} (B : Torsor G)

/-- An isomorphism of coefficient sheaves transports the difference map
on a torsor's presheaf of sections. -/
def changeCoefficients {H : Sheaf J AddCommGrpCat.{w}} (e : G ≅ H) : Torsor H where
  D := {
    P := B.D.P
    diff := fun U x y => e.hom.hom.app U (B.D.diff U x y)
    diff_add_diff := fun U x y z => by rw [← map_add, B.D.diff_add_diff]
    map_diff := fun f x y => by
      rw [← NatTrans.naturality_apply e.hom.hom f, B.D.map_diff] }
  isSheaf := B.isSheaf
  locally_nonempty := B.locally_nonempty
  diff_bijective := fun U y =>
    (ConcreteCategory.bijective_of_isIso ((sheafSections J AddCommGrpCat.{w}).obj U |>.mapIso e).hom).comp
      (B.diff_bijective U y)

/-- A section of a torsor on a chart trivializes its restriction to the slice
site over that chart. The trivialization takes differences from the section. -/
def trivializationAt {V : C} (b : B.D.P.obj (op V)) :
    (Over.forget V).op ⋙ B.D.P ≅ ((Over.forget V).op ⋙ G.obj) ⋙ forget AddCommGrpCat.{w} := by
  let e (U : (Over V)ᵒᵖ) := Equiv.ofBijective
    (fun x => B.D.diff (op U.unop.left) x (B.D.P.map U.unop.hom.op b))
    (B.diff_bijective (op U.unop.left) (B.D.P.map U.unop.hom.op b))
  refine NatIso.ofComponents (fun U => Equiv.toIso (e U)) ?_
  intro U W f
  apply ConcreteCategory.hom_ext
  intro x
  let k := f.unop.left.op
  change B.D.diff (op W.unop.left) (B.D.P.map k x) (B.D.P.map W.unop.hom.op b) =
    G.obj.map k (B.D.diff (op U.unop.left) x (B.D.P.map U.unop.hom.op b))
  rw [B.D.map_diff]
  have h : U.unop.hom.op ≫ k = W.unop.hom.op :=
    Quiver.Hom.unop_inj (Over.w f.unop)
  rw [← Functor.map_comp_apply, h]

end PhilipponTorsorTrivialization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleConstantFiniteRepresentability (constantChart representsConstant)
open PhilipponEtaleNeighborhoodRestriction (along restrict restrictionIso)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponTorsorSectionFibers (Torsor)
open PhilipponTorsorInvariantDescent (presence)
open PhilipponTorsorTrivialization (trivializationAt changeCoefficients)


namespace PhilipponEtaleConstantTorsorLocalModel

universe u

variable {X : Scheme.{u}}

private def alongSlice (V : X.Etale) : V.left.Etale ⥤ Over V :=
  (along V.hom).toOver V (fun U => MorphismProperty.Over.homMk U.hom rfl trivial)
    (fun f => MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f))

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]

private abbrev K (Y : Scheme.{u}) :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)

/-- A section of a finite constant torsor identifies it over the given étale
chart with the representable presheaf of the finite constant scheme. -/
def localRepresentation (B : Torsor (K M X)) (V : X.Etale) (b : B.D.P.obj (op V)) :
    (along V.hom).op ⋙ B.D.P ≅ yoneda.obj (constantChart V.left M) := by
  let a := Functor.isoWhiskerLeft (alongSlice V).op (trivializationAt B b)
  let e := (restrictionIso V.hom).app (K M X) ≪≫
    (pullbackConstantIso V.hom).app (AddCommGrpCat.of M)
  let f := Functor.isoWhiskerRight
    ((sheafToPresheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).mapIso e) (forget AddCommGrpCat.{u})
  exact a ≪≫ f ≪≫ (representsConstant V.left M).symm

/-- Every finite constant torsor is represented by finite étale schemes on
an étale cover of the base. -/
theorem exists_etale_cover_with_local_representations (B : Torsor (K M X)) :
    ∃ (I : Type u) (V : I → X.Etale), (⋃ i, Set.range (fun x : (V i).left => ((V i).hom x : X))) = (Set.univ : Set X) ∧
      ∀ i, Nonempty ((along (V i).hom).op ⋙ B.D.P ≅ yoneda.obj (constantChart (V i).left M)) := by
  let T := Scheme.Etale.mk (𝟙 X)
  obtain ⟨𝒰, hOver, hEt, hLift⟩ :=
    (Scheme.mem_smallGrothendieckTopology T (presence B.D.P T)).mp (B.locally_nonempty T)
  let : 𝒰.Over X := hOver
  let V (i : 𝒰.I₀) := (𝒰.X i).asOverProp X (hEt i)
  let r (i : 𝒰.I₀) : V i ⟶ T := (𝒰.f i).asOverProp X
  have hr (i : 𝒰.I₀) : (r i).left = (V i).hom := by
    have h := MorphismProperty.Over.w (r i)
    change (r i).left ≫ 𝟙 X = (V i).hom at h
    exact (Category.comp_id ((r i).left)).symm.trans h
  refine ⟨𝒰.I₀, V, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    exact Set.mem_iUnion.mpr ⟨𝒰.idx x, ⟨y, (congrArg (fun k : (𝒰.X (𝒰.idx x)) ⟶ X => k y)
      (hr (𝒰.idx x)).symm).trans hy⟩⟩
  · intro i
    have h : (presence B.D.P T) (r i) := hLift _ _ ⟨i⟩
    obtain ⟨b⟩ := h
    exact ⟨localRepresentation M B (V i) b⟩

/-- Over an affine base a torsor under a pulled-back finite constant
coefficient sheaf has a finite étale model after one faithfully flat
affine étale base change. -/
theorem exists_model_on_spec_cover {Y : Scheme.{u}} (R : CommRingCat.{u}) (j : Spec R ⟶ Y)
    (B : Torsor ((pullbackSheaves j).obj (K M Y))) :
    ∃ (S : CommRingCat.{u}) (f : R ⟶ S) (_ : Etale (Spec.map f)), f.hom.FaithfullyFlat ∧
      ∃ V : (Spec S).Etale, IsFinite V.hom ∧ IsAffine V.left ∧
        Nonempty ((along (Spec.map f)).op ⋙ B.D.P ≅ yoneda.obj V) := by
  let e := (pullbackConstantIso j).app (AddCommGrpCat.of M)
  let D := changeCoefficients B e
  obtain ⟨S, f, hEt, hFlat, ⟨b⟩⟩ := PhilipponAffineEtaleTorsorCover.exists_spec_cover R D
  let U := Scheme.Etale.mk (Spec.map f)
  let V := constantChart (Spec S) M
  let : IsFinite V.hom := PhilipponEtaleConstantFiniteRepresentability.isFinite_constantChart (Spec S) M
  exact ⟨S, f, hEt, hFlat, V, inferInstance, isAffine_of_isAffineHom (Y := Spec S) V.hom,
    ⟨localRepresentation M D U b⟩⟩

end PhilipponEtaleConstantTorsorLocalModel

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory


namespace PhilipponMonadAlgebraTransport

universe u v w t

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{t} D]
variable {M : Monad C} {N : Monad D} {F : C ⥤ D}

variable (e : (M : C ⥤ C) ⋙ F ≅ F ⋙ (N : D ⥤ D))
variable (hη : ∀ X, F.map (M.η.app X) ≫ e.hom.app X = N.η.app (F.obj X))
variable (hμ : ∀ X, F.map (M.μ.app X) ≫ e.hom.app X =
  e.hom.app (M.obj X) ≫ N.map (e.hom.app X) ≫ N.μ.app (F.obj X))

include hμ in
private theorem inv_μ (X : C) : N.μ.app (F.obj X) ≫ e.inv.app X =
    N.map (e.inv.app X) ≫ e.inv.app (M.obj X) ≫ F.map (M.μ.app X) := by
  calc
    _ = N.map (e.inv.app X) ≫ e.inv.app (M.obj X) ≫
        (e.hom.app (M.obj X) ≫ N.map (e.hom.app X) ≫ N.μ.app (F.obj X)) ≫ e.inv.app X := by
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← N.map_comp_assoc,
        Iso.inv_hom_id_app]
      rw [N.toFunctor.map_id, Category.id_comp]
    _ = _ := by
      rw [← hμ X]
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact congrArg (fun p => N.map (e.inv.app X) ≫ e.inv.app (M.obj X) ≫ p)
        (Category.comp_id (F.map (M.μ.app X)))

/-- A functor commuting with the units and multiplications sends monad
algebras to monad algebras. -/
def mapAlgebras : M.Algebra ⥤ N.Algebra where
  obj A := {
    A := F.obj A.A
    a := e.inv.app A.A ≫ F.map A.a
    unit := by
      rw [← hη A.A, Category.assoc, Iso.hom_inv_id_app_assoc, ← F.map_comp,
        A.unit]
      exact F.map_id _
    assoc := by
      have hn : e.inv.app (M.obj A.A) ≫ F.map (M.map A.a) = N.map (F.map A.a) ≫ e.inv.app A.A :=
        (e.inv.naturality A.a).symm
      rw [← Category.assoc, inv_μ e hμ, Category.assoc, Category.assoc, ← F.map_comp,
        A.assoc, F.map_comp, N.map_comp]
      simp only [Category.assoc, reassoc_of% hn] }
  map {A B} f := {
    f := F.map f.f
    h := by
      change N.map (F.map f.f) ≫ (e.inv.app B.A ≫ F.map B.a) =
        (e.inv.app A.A ≫ F.map A.a) ≫ F.map f.f
      have hn : N.map (F.map f.f) ≫ e.inv.app B.A = e.inv.app A.A ≫ F.map (M.map f.f) :=
        e.inv.naturality f.f
      rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, f.h, F.map_comp, Category.assoc] }
  map_id A := Monad.Algebra.Hom.ext (F.map_id _)
  map_comp f g := Monad.Algebra.Hom.ext (F.map_comp _ _)

/-- The induced functor on algebras is fully faithful whenever the
underlying functor is fully faithful. -/
def mapAlgebrasFullyFaithful (hF : F.FullyFaithful) : (mapAlgebras e hη hμ).FullyFaithful where
  preimage {A B} t := {
    f := hF.preimage t.f
    h := by
      let g := hF.preimage t.f
      have hg : F.map g = t.f := hF.map_preimage t.f
      apply hF.map_injective
      simp only [Functor.map_comp]
      apply (cancel_epi (e.inv.app A.A)).mp
      have ht := t.h
      change N.map t.f ≫ (e.inv.app B.A ≫ F.map B.a) =
        (e.inv.app A.A ≫ F.map A.a) ≫ t.f at ht
      have hn : N.map (F.map g) ≫ e.inv.app B.A = e.inv.app A.A ≫ F.map (M.map g) :=
        e.inv.naturality g
      rw [← hg, reassoc_of% hn, Category.assoc] at ht
      exact ht }
  map_preimage t := Monad.Algebra.Hom.ext (hF.map_preimage t.f)
  preimage_map t := Monad.Algebra.Hom.ext (hF.preimage_map t.f)

/-- An algebra on an object in the image of a fully faithful functor
lifts along the compatible monad comparison. -/
theorem exists_algebra_lift [F.Full] [F.Faithful] (B : N.Algebra) (X : C) (i : F.obj X ≅ B.A) :
    ∃ A : M.Algebra, A.A = X ∧ Nonempty ((mapAlgebras e hη hμ).obj A ≅ B) := by
  let k := N.map i.hom ≫ B.a ≫ i.inv
  have kη : N.η.app (F.obj X) ≫ k = 𝟙 _ := by
    have h : N.η.app (F.obj X) ≫ N.map i.hom = i.hom ≫ N.η.app B.A := (N.η.naturality i.hom).symm
    dsimp only [k]
    rw [reassoc_of% h, B.unit_assoc, i.hom_inv_id]
    rfl
  have kμ : N.μ.app (F.obj X) ≫ k = N.map k ≫ k := by
    have h : N.μ.app (F.obj X) ≫ N.map i.hom = N.map (N.map i.hom) ≫ N.μ.app B.A :=
      (N.μ.naturality i.hom).symm
    have hi : N.map i.inv ≫ N.map i.hom = 𝟙 _ := by rw [← N.map_comp, i.inv_hom_id, N.map_id]
    dsimp only [k]
    simp only [N.map_comp, Category.assoc, reassoc_of% h, B.assoc_assoc, reassoc_of% hi]
  let p := F.preimage (e.hom.app X ≫ k)
  have hp : F.map p = e.hom.app X ≫ k := F.map_preimage _
  let A : M.Algebra := {
    A := X
    a := p
    unit := F.map_injective (by
      rw [F.map_comp, hp, ← Category.assoc, hη, kη]
      exact (F.map_id _).symm)
    assoc := F.map_injective (by
      have hn : F.map (M.map p) ≫ e.hom.app X = e.hom.app (M.obj X) ≫ N.map (F.map p) :=
        e.hom.naturality p
      simp only [F.map_comp, hp, Category.assoc, reassoc_of% (hμ X), reassoc_of% hn, N.map_comp, kμ]) }
  have hA : ((mapAlgebras e hη hμ).obj A).a = k := by
    change e.inv.app X ≫ F.map p = k
    rw [hp, Iso.inv_hom_id_app_assoc]
  refine ⟨A, rfl, ⟨Monad.Algebra.isoMk i ?_⟩⟩
  change N.map i.hom ≫ B.a = ((mapAlgebras e hη hμ).obj A).a ≫ i.hom
  rw [hA]
  simp [k]

end PhilipponMonadAlgebraTransport

end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponAffineDescentSpec

universe u

/-- The affine scheme of an algebra, viewed over the spectrum of its base. -/
abbrev overSpec (R : CommRingCat.{u}) : (Under R)ᵒᵖ ⥤ Over (Spec R) :=
  (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

def overSpecFullyFaithful (R : CommRingCat.{u}) : (overSpec R).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful (Over.opEquivOpUnder R).inverse).comp
    ((Functor.FullyFaithful.ofFullyFaithful Scheme.Spec).over (op R))

theorem exists_under_of_affine {R : CommRingCat.{u}} (V : Over (Spec R)) [IsAffine V.left] :
    ∃ B : Under R, Nonempty ((overSpec R).obj (op B) ≅ V) := by
  let g := V.left.isoSpec.inv ≫ V.hom
  let b := Spec.preimage g
  exact ⟨Under.mk b, ⟨Over.isoMk V.left.isoSpec.symm (Spec.map_preimage g).symm⟩⟩

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

abbrev ringAdj := (Under.mapPushoutAdj f).op
abbrev schemeAdj := Over.mapPullbackAdj (Spec.map f)
abbrev ringMonad := (ringAdj f).toMonad
abbrev schemeMonad := (schemeAdj f).toMonad

private def pullbackApp (A : (Under R)ᵒᵖ) :
    (overSpec S).obj ((Under.pushout f).op.obj A) ≅
      (Over.pullback (Spec.map f)).obj ((overSpec R).obj A) := by
  let h := isPullback_SpecMap_pushout A.unop.hom f
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

private theorem pullbackApp_fst (A : (Under R)ᵒᵖ) :
    (pullbackApp f A).hom.left ≫ pullback.fst (Spec.map A.unop.hom) (Spec.map f) =
      Spec.map (pushout.inl A.unop.hom f) :=
  (isPullback_SpecMap_pushout A.unop.hom f).isoPullback_hom_fst

private theorem pullback_map_fst {A B : Over (Spec R)} (g : A ⟶ B) :
    ((Over.pullback (Spec.map f)).map g).left ≫ pullback.fst B.hom (Spec.map f) =
      pullback.fst A.hom (Spec.map f) ≫ g.left := pullback.lift_fst ..

/-- The spectrum of a pushout algebra is the base-changed affine scheme. -/
def baseChangeIso : (Under.pushout f).op ⋙ overSpec S ≅ overSpec R ⋙ Over.pullback (Spec.map f) := by
  refine NatIso.ofComponents (pullbackApp f) ?_
  intro A B g
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hg := pullback_map_fst f ((overSpec R).map g)
    change ((Over.pullback (Spec.map f)).map ((overSpec R).map g)).left ≫
      pullback.fst (Spec.map B.unop.hom) (Spec.map f) =
      pullback.fst (Spec.map A.unop.hom) (Spec.map f) ≫ Spec.map g.unop.right at hg
    change Spec.map ((Under.pushout f).map g.unop).right ≫ (pullbackApp f B).hom.left ≫
        pullback.fst (Spec.map B.unop.hom) (Spec.map f) =
      (pullbackApp f A).hom.left ≫ ((Over.pullback (Spec.map f)).map ((overSpec R).map g)).left ≫
        pullback.fst (Spec.map B.unop.hom) (Spec.map f)
    rw [pullbackApp_fst, hg, ← Category.assoc, pullbackApp_fst]
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map (pushout.inl_desc ..)).trans (Spec.map_comp _ _))
  · exact (Over.w (((Under.pushout f).op ⋙ overSpec S).map g ≫ (pullbackApp f B).hom)).trans
      (Over.w ((pullbackApp f A).hom ≫ (overSpec R ⋙ Over.pullback (Spec.map f)).map g)).symm

private def compositionApp (B : (Under S)ᵒᵖ) :
    (overSpec R).obj ((Under.map f).op.obj B) ≅
      (Over.map (Spec.map f)).obj ((overSpec S).obj B) := by
  refine Over.isoMk (Iso.refl (Spec B.unop.right)) ?_
  change 𝟙 (Spec B.unop.right) ≫ (Spec.map B.unop.hom ≫ Spec.map f) = Spec.map (f ≫ B.unop.hom)
  exact (Category.id_comp _).trans (Spec.map_comp f B.unop.hom).symm

private theorem monadSquare (B : (Under S)ᵒᵖ) :
    IsPullback (Spec.map (pushout.inl (f ≫ B.unop.hom) f))
      (Spec.map (pushout.inr (f ≫ B.unop.hom) f))
      (Spec.map B.unop.hom ≫ Spec.map f) (Spec.map f) := by
  simpa only [Spec.map_comp] using isPullback_SpecMap_pushout (f ≫ B.unop.hom) f

private def monadApp (B : (Under S)ᵒᵖ) :
    (overSpec S).obj ((ringMonad f).obj B) ≅ (schemeMonad f).obj ((overSpec S).obj B) :=
  Over.isoMk (monadSquare f B).isoPullback (monadSquare f B).isoPullback_hom_snd

private abbrev forgetPullbackFst (V : Over (Spec S)) :=
  pullback.fst (V.hom ≫ Spec.map f) (Spec.map f)

private theorem monadApp_fst (B : (Under S)ᵒᵖ) :
    (monadApp f B).hom.left ≫ forgetPullbackFst f ((overSpec S).obj B) =
      Spec.map (pushout.inl (f ≫ B.unop.hom) f) := (monadSquare f B).isoPullback_hom_fst

private theorem monadApp_hom_eq (B : (Under S)ᵒᵖ) : (monadApp f B).hom =
    (pullbackApp f ((Under.map f).op.obj B)).hom ≫
      (Over.pullback (Spec.map f)).map (compositionApp f B).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h := pullback_map_fst f (compositionApp f B).hom
    change ((Over.pullback (Spec.map f)).map (compositionApp f B).hom).left ≫
      forgetPullbackFst f ((overSpec S).obj B) =
      pullback.fst (Spec.map (f ≫ B.unop.hom)) (Spec.map f) ≫ 𝟙 _ at h
    change (monadApp f B).hom.left ≫ forgetPullbackFst f ((overSpec S).obj B) =
      ((pullbackApp f ((Under.map f).op.obj B)).hom.left ≫
        ((Over.pullback (Spec.map f)).map (compositionApp f B).hom).left) ≫
        forgetPullbackFst f ((overSpec S).obj B)
    rw [monadApp_fst, Category.assoc, h, Category.comp_id]
    exact (pullbackApp_fst f ((Under.map f).op.obj B)).symm
  · exact (Over.w (monadApp f B).hom).trans (Over.w
      ((pullbackApp f ((Under.map f).op.obj B)).hom ≫
        (Over.pullback (Spec.map f)).map (compositionApp f B).hom)).symm

private theorem schemeMonad_map_fst {U V : Over (Spec S)} (g : U ⟶ V) :
    ((schemeMonad f).map g).left ≫ forgetPullbackFst f V = forgetPullbackFst f U ≫ g.left :=
  pullback_map_fst f ((Over.map (Spec.map f)).map g)

private def compositionIso : (Under.map f).op ⋙ overSpec R ≅ overSpec S ⋙ Over.map (Spec.map f) := by
  refine NatIso.ofComponents (compositionApp f) ?_
  intro A B g
  apply Over.OverMorphism.ext
  change Spec.map g.unop.right ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map g.unop.right
  rw [Category.comp_id, Category.id_comp]

private def compositeMonadIso : (ringMonad f).toFunctor ⋙ overSpec S ≅
    overSpec S ⋙ (schemeMonad f).toFunctor :=
  let L := (Under.map f).op
  let R' := (Under.pushout f).op
  let l := Over.map (Spec.map f)
  let r := Over.pullback (Spec.map f)
  Functor.associator L R' (overSpec S) ≪≫
    Functor.isoWhiskerLeft L (baseChangeIso f) ≪≫
    (Functor.associator L (overSpec R) r).symm ≪≫
    Functor.isoWhiskerRight (compositionIso f) r ≪≫
    Functor.associator (overSpec S) l r

private theorem compositeMonadIso_hom_app (B : (Under S)ᵒᵖ) :
    (compositeMonadIso f).hom.app B = (monadApp f B).hom := by
  rw [monadApp_hom_eq]
  simp only [compositeMonadIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  rfl

/-- The spectrum comparison between the pullback monad and its affine
algebra model. -/
def monadIso : (ringMonad f).toFunctor ⋙ overSpec S ≅ overSpec S ⋙ (schemeMonad f).toFunctor := by
  refine NatIso.ofComponents (monadApp f) ?_
  intro A B g
  rw [← compositeMonadIso_hom_app, ← compositeMonadIso_hom_app]
  exact (compositeMonadIso f).hom.naturality g

private theorem schemeMonad_η_fst (V : Over (Spec S)) :
    ((schemeMonad f).η.app V).left ≫ forgetPullbackFst f V = 𝟙 _ := by
  change ((schemeAdj f).unit.app V).left ≫ forgetPullbackFst f V = _
  simp [Over.mapPullbackAdj_unit_app, forgetPullbackFst]

private theorem schemeMonad_μ_fst (V : Over (Spec S)) :
    ((schemeMonad f).μ.app V).left ≫ forgetPullbackFst f V =
      forgetPullbackFst f ((schemeMonad f).obj V) ≫ forgetPullbackFst f V := by
  exact pullback_map_fst f ((schemeAdj f).counit.app ((Over.map (Spec.map f)).obj V))

private theorem ringMonad_η_inl (B : (Under S)ᵒᵖ) :
    pushout.inl (f ≫ B.unop.hom) f ≫ ((ringMonad f).η.app B).unop.right = 𝟙 _ := by
  change pushout.inl (f ≫ B.unop.hom) f ≫ ((Under.mapPushoutAdj f).counit.app B.unop).right = _
  simp [Under.mapPushoutAdj_counit_app]

private theorem ringMonad_μ_inl (B : (Under S)ᵒᵖ) :
    pushout.inl (f ≫ B.unop.hom) f ≫ ((ringMonad f).μ.app B).unop.right =
      pushout.inl (f ≫ B.unop.hom) f ≫ pushout.inl (f ≫ ((ringMonad f).obj B).unop.hom) f := by
  let A := (Under.map f).obj B.unop
  let A' := (Under.map f).obj ((Under.pushout f).obj A)
  change pushout.inl A.hom f ≫
    pushout.desc (pushout.inl A.hom f ≫ pushout.inl A'.hom f) (pushout.inr A'.hom f) _ = _
  exact pushout.inl_desc ..

theorem monadIso_unit (B : (Under S)ᵒᵖ) :
    (overSpec S).map ((ringMonad f).η.app B) ≫ (monadIso f).hom.app B =
      (schemeMonad f).η.app ((overSpec S).obj B) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change Spec.map ((ringMonad f).η.app B).unop.right ≫ (monadApp f B).hom.left ≫
      forgetPullbackFst f ((overSpec S).obj B) =
        ((schemeMonad f).η.app ((overSpec S).obj B)).left ≫ forgetPullbackFst f ((overSpec S).obj B)
    rw [monadApp_fst, schemeMonad_η_fst]
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map (ringMonad_η_inl f B)).trans (Spec.map_id _))
  · exact (Over.w ((overSpec S).map ((ringMonad f).η.app B) ≫ (monadIso f).hom.app B)).trans
      (Over.w ((schemeMonad f).η.app ((overSpec S).obj B))).symm

theorem monadIso_mul (B : (Under S)ᵒᵖ) :
    (overSpec S).map ((ringMonad f).μ.app B) ≫ (monadIso f).hom.app B =
      (monadIso f).hom.app ((ringMonad f).obj B) ≫
        (schemeMonad f).map ((monadIso f).hom.app B) ≫ (schemeMonad f).μ.app ((overSpec S).obj B) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hμ := schemeMonad_μ_fst f ((overSpec S).obj B)
    have hmap := schemeMonad_map_fst f (monadApp f B).hom
    have hfst := monadApp_fst f ((ringMonad f).obj B)
    change Spec.map ((ringMonad f).μ.app B).unop.right ≫ (monadApp f B).hom.left ≫
      forgetPullbackFst f ((overSpec S).obj B) =
      (monadApp f ((ringMonad f).obj B)).hom.left ≫ ((schemeMonad f).map (monadApp f B).hom).left ≫
        ((schemeMonad f).μ.app ((overSpec S).obj B)).left ≫ forgetPullbackFst f ((overSpec S).obj B)
    rw [monadApp_fst, hμ]
    let a := (monadApp f ((ringMonad f).obj B)).hom.left
    let b := (monadApp f B).hom.left
    let p := forgetPullbackFst f ((overSpec S).obj B)
    let q := forgetPullbackFst f ((overSpec S).obj ((ringMonad f).obj B))
    have hright : a ≫ ((schemeMonad f).map (monadApp f B).hom).left ≫
        forgetPullbackFst f ((schemeMonad f).obj ((overSpec S).obj B)) ≫ p =
      Spec.map (pushout.inl (f ≫ ((ringMonad f).obj B).unop.hom) f) ≫
        Spec.map (pushout.inl (f ≫ B.unop.hom) f) := by
      calc
        _ = a ≫ (q ≫ b) ≫ p :=
          (congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
            (congrArg (fun k => a ≫ k ≫ p) hmap)
        _ = (a ≫ q) ≫ (b ≫ p) := by simp only [Category.assoc]
        _ = _ := congrArg₂ (· ≫ ·) hfst (monadApp_fst f B)
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map (ringMonad_μ_inl f B)).trans
      ((Spec.map_comp _ _).trans hright.symm))
  · exact (Over.w ((overSpec S).map ((ringMonad f).μ.app B) ≫ (monadIso f).hom.app B)).trans
      (Over.w ((monadIso f).hom.app ((ringMonad f).obj B) ≫
        (schemeMonad f).map ((monadIso f).hom.app B) ≫ (schemeMonad f).μ.app ((overSpec S).obj B))).symm

abbrev mapAlgebras :=
  PhilipponMonadAlgebraTransport.mapAlgebras (monadIso f) (monadIso_unit f) (monadIso_mul f)

private theorem counit_match (A : (Under R)ᵒᵖ) :
    (overSpec R).map ((ringAdj f).counit.app A) =
      (compositionApp f ((Under.pushout f).op.obj A)).hom ≫
        (Over.map (Spec.map f)).map ((baseChangeIso f).hom.app A) ≫
          (schemeAdj f).counit.app ((overSpec R).obj A) := by
  apply Over.OverMorphism.ext
  change Spec.map ((Under.mapPushoutAdj f).unit.app A.unop).right =
    𝟙 _ ≫ (pullbackApp f A).hom.left ≫ pullback.fst (Spec.map A.unop.hom) (Spec.map f)
  rw [Category.id_comp, pullbackApp_fst]
  rfl

/-- The ring and scheme comparison functors induce the same descent data
on a base-changed affine scheme. -/
def comparisonIso (A : (Under R)ᵒᵖ) :
    (mapAlgebras f).obj ((Monad.comparison (ringAdj f)).obj A) ≅
      (Monad.comparison (schemeAdj f)).obj ((overSpec R).obj A) := by
  let B := (Under.pushout f).op.obj A
  let b := (baseChangeIso f).app A
  let θ := (monadIso f).app B
  let t := (ringAdj f).counit.app A
  let u := (schemeAdj f).counit.app ((overSpec R).obj A)
  refine Monad.Algebra.isoMk b ?_
  change (schemeMonad f).map b.hom ≫ (Over.pullback (Spec.map f)).map u =
    (θ.inv ≫ (overSpec S).map ((Under.pushout f).op.map t)) ≫ b.hom
  have h : (overSpec S).map ((Under.pushout f).op.map t) ≫ b.hom =
      θ.hom ≫ (schemeMonad f).map b.hom ≫ (Over.pullback (Spec.map f)).map u := by
    have hnat := (baseChangeIso f).hom.naturality t
    change (overSpec S).map ((Under.pushout f).op.map t) ≫ b.hom =
      (baseChangeIso f).hom.app ((Under.map f).op.obj B) ≫
        (Over.pullback (Spec.map f)).map ((overSpec R).map t) at hnat
    have hθ : θ.hom = (baseChangeIso f).hom.app ((Under.map f).op.obj B) ≫
      (Over.pullback (Spec.map f)).map (compositionApp f B).hom := monadApp_hom_eq f B
    rw [hnat, counit_match f A, hθ]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

end PhilipponAffineDescentSpec

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct


namespace PhilipponFaithfullyFlatAlgebraDescent

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Base change of commutative algebras along a faithfully flat map
reflects isomorphisms. -/
theorem reflectsIsomorphisms (hf : f.hom.FaithfullyFlat) :
    (Under.pushout f).ReflectsIsomorphisms := by
  refine ⟨fun {A B} g hg => ?_⟩
  let : Algebra R S := f.hom.toAlgebra
  let : Module.FaithfullyFlat R S := (RingHom.faithfullyFlat_algebraMap_iff).mp hf
  let e := CommRingCat.tensorProdIsoPushout R S
  have hIso : IsIso ((CommRingCat.tensorProd R S).map g) :=
    (NatIso.isIso_map_iff e g).mpr hg
  have hg' : IsIso (((CategoryTheory.Under.forget S).map ((CommRingCat.tensorProd R S).map g))) :=
    Functor.map_isIso _ _
  have hb := (ConcreteCategory.isIso_iff_bijective _).mp hg'
  rw [← isIso_iff_of_reflects_iso g (CategoryTheory.Under.forget R), ConcreteCategory.isIso_iff_bijective]
  let l := (CommRingCat.toAlgHom g).toLinearMap
  have hmap : LinearMap.lTensor S l = (Algebra.TensorProduct.map (AlgHom.id S S) (CommRingCat.toAlgHom g)).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S l).mp
  rw [hmap]
  exact hb

/-- Faithfully flat base change of commutative algebras is comonadic. -/
@[instance_reducible]
def comonadicPushout (hf : f.hom.FaithfullyFlat) : ComonadicLeftAdjoint (Under.pushout f) := by
  let : (Under.pushout f).ReflectsIsomorphisms := reflectsIsomorphisms f hf
  let : PreservesFiniteLimits (Under.pushout f) := CommRingCat.Under.preservesFiniteLimits_of_flat f hf.flat
  convert Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (Under.mapPushoutAdj f)
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩

abbrev comparison := Comonad.comparison (Under.mapPushoutAdj f)

/-- A finite étale algebra with faithfully flat descent data descends to
a finite étale algebra, preserving the full descent data. -/
theorem exists_finiteEtale_model (hf : f.hom.FaithfullyFlat)
    (B : (Under.mapPushoutAdj f).toComonad.Coalgebra)
    (hFin : B.A.hom.hom.Finite) (hEt : B.A.hom.hom.Etale) :
    ∃ A : Under R, A.hom.hom.Finite ∧ A.hom.hom.Etale ∧
      Nonempty ((comparison f).obj A ≅ B) := by
  let hC := comonadicPushout f hf
  let : (comparison f).IsEquivalence := hC.eqv
  let A := (comparison f).objPreimage B
  let d := (comparison f).objObjPreimageIso B
  let : Algebra R S := f.hom.toAlgebra
  let k : ((CommRingCat.tensorProd R S).obj A) ≅ B.A :=
    (CommRingCat.tensorProdIsoPushout R S).app A ≪≫
      ((Under.mapPushoutAdj f).toComonad.forget).mapIso d
  let p : S ⟶ CommRingCat.of (S ⊗[R] A) := CommRingCat.ofHom (algebraMap S (S ⊗[R] A))
  let r := ((Under.forget S).mapIso k).hom
  have hk : p ≫ r = B.A.hom := Under.w k.hom
  have h₁ : (algebraMap S (S ⊗[R] A)).Finite := by
    apply (RingHom.finite_respectsIso.cancel_right_isIso p r).mp
    rw [← CommRingCat.hom_comp, hk]
    exact hFin
  have h₂ : (algebraMap S (S ⊗[R] A)).Etale := by
    apply (RingHom.Etale.respectsIso.cancel_right_isIso p r).mp
    rw [← CommRingCat.hom_comp, hk]
    exact hEt
  exact ⟨A, RingHom.Finite.codescendsAlong_faithfullyFlat.algebraMap_tensorProduct
      (R := R) (S := S) (T := A) _ hf h₁,
    RingHom.Etale.codescendsAlong_faithfullyFlat.algebraMap_tensorProduct
      (R := R) (S := S) (T := A) _ hf h₂, ⟨d⟩⟩

/-- The finite étale descent result in the opposite category, in the
orientation used by the affine scheme pullback adjunction. -/
theorem exists_opposite_finiteEtale_model (hf : f.hom.FaithfullyFlat)
    (B : (Under.mapPushoutAdj f).op.toMonad.Algebra)
    (hFin : B.A.unop.hom.hom.Finite) (hEt : B.A.unop.hom.hom.Etale) :
    ∃ A : Under R, A.hom.hom.Finite ∧ A.hom.hom.Etale ∧
      Nonempty ((Monad.comparison (Under.mapPushoutAdj f).op).obj (op A) ≅ B) := by
  let adj := Under.mapPushoutAdj f
  let C : adj.toComonad.Coalgebra := {
    A := B.A.unop
    a := B.a.unop
    counit := congrArg Quiver.Hom.unop B.unit
    coassoc := congrArg Quiver.Hom.unop B.assoc }
  obtain ⟨A, hA, hE, ⟨d⟩⟩ := exists_finiteEtale_model f hf C hFin hEt
  let e := (adj.toComonad.forget.mapIso d).symm.op
  refine ⟨A, hA, hE, ⟨Monad.Algebra.isoMk e ?_⟩⟩
  exact congrArg Quiver.Hom.op d.inv.h

end PhilipponFaithfullyFlatAlgebraDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme (etaleTopology etaleTopology_le_proetaleTopology)
open PhilipponTorsorInvariantDescent (presence)


namespace PhilipponEtaleRepresentablePresence

universe u

private theorem subcanonical (X : Scheme.{u}) : X.smallEtaleTopology.Subcanonical := by
  let : etaleTopology.Subcanonical := .of_le etaleTopology_le_proetaleTopology
  let : RepresentablyFlat (Scheme.Etale.forget X) := flat_of_preservesFiniteLimits _
  let : (Scheme.Etale.forget X).LocallyCoverDense (etaleTopology.over X) :=
    inferInstanceAs ((MorphismProperty.Over.forget @Etale ⊤ X).LocallyCoverDense
      (X.overGrothendieckTopology @Etale))
  let : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) := by
    rw [Functor.isContinuous_iff_coverPreserving]
    exact (Scheme.Etale.forget X).coverPreserving_restrictedTopology (etaleTopology.over X)
  exact GrothendieckTopology.subcanonical_of_full_of_faithful (Scheme.Etale.forget X)
    X.smallEtaleTopology (etaleTopology.over X)

/-- A representable presheaf on the small étale site is a sheaf. -/
theorem isSheaf_yoneda {X : Scheme.{u}} (W : X.Etale) :
    Presheaf.IsSheaf X.smallEtaleTopology (yoneda.obj W) := by
  let := subcanonical X
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- A surjective étale chart has sections locally over each chart. -/
theorem presence_mem_of_surjective {X : Scheme.{u}} (W U : X.Etale) [Surjective W.hom] :
    presence (yoneda.obj W) U ∈ X.smallEtaleTopology U := by
  let P := Scheme.Etale.mk (pullback.fst U.hom W.hom ≫ U.hom)
  let p : P ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom W.hom) rfl trivial
  let q : P ⟶ W := MorphismProperty.Over.homMk (pullback.snd U.hom W.hom) pullback.condition.symm trivial
  let f (_ : Unit) : P ⟶ U := p
  have hCover : Sieve.ofArrows (fun _ : Unit => P) f ∈ X.smallEtaleTopology U := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    apply Set.eq_univ_of_forall
    intro x
    have hSurj : Surjective (pullback.fst U.hom W.hom) := inferInstance
    have hx : x ∈ Set.range (p.left) := hSurj.surj x
    exact Set.mem_iUnion.mpr ⟨(), hx⟩
  apply X.smallEtaleTopology.superset_covering _ hCover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  exact ⟨q⟩

/-- If a presheaf represented by an étale chart has sections locally on
the terminal chart, the representing étale morphism is surjective. -/
theorem surjective_of_presence {X : Scheme.{u}} {B : X.Etaleᵒᵖ ⥤ Type u} {W : X.Etale}
    (e : B ≅ yoneda.obj W)
    (h : presence B (Scheme.Etale.mk (𝟙 X)) ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X))) :
    Surjective W.hom := by
  let T := Scheme.Etale.mk (𝟙 X)
  obtain ⟨𝒰, hOver, hEt, hLift⟩ := (Scheme.mem_smallGrothendieckTopology T (presence B T)).mp h
  let : 𝒰.Over X := hOver
  refine ⟨fun x => ?_⟩
  let i := 𝒰.idx x
  let U := (𝒰.X i).asOverProp X (hEt i)
  let a : U ⟶ T := (𝒰.f i).asOverProp X
  obtain ⟨b⟩ : (presence B T) a := hLift _ _ ⟨i⟩
  let m : U ⟶ W := e.hom.app (op U) b
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have ha := MorphismProperty.Over.w a
  change (𝒰.f i) ≫ 𝟙 X = U.hom at ha
  have hm : m.left ≫ W.hom = 𝒰.f i :=
    (MorphismProperty.Over.w m).trans (ha.symm.trans (Category.comp_id _))
  refine ⟨m.left y, ?_⟩
  exact (congrArg (fun k : (𝒰.X i) ⟶ X => k y) hm).trans hy

end PhilipponEtaleRepresentablePresence

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponRepresentableDescentDatum

universe u v w

variable {D : Type u} {C : Type v} [Category.{w} D] [Category.{w} C]
variable {L : D ⥤ C} {R : C ⥤ D} (a : L ⊣ R)
variable {P : Cᵒᵖ ⥤ Type w} {V : D} (e : yoneda.obj V ≅ L.op ⋙ P)

/-- Sections of the restricted presheaf are coordinates for maps to its
representing object. -/
abbrev evaluate {W : D} (p : W ⟶ V) : P.obj (op (L.obj W)) := e.hom.app (op W) p

private theorem evaluate_comp {W Z : D} (f : W ⟶ Z) (g : Z ⟶ V) :
    evaluate e (f ≫ g) = P.map (L.map f).op (evaluate e g) :=
  NatTrans.naturality_apply e.hom f.op g

private theorem evaluate_from_identity {W : D} (f : W ⟶ V) :
    P.map (L.map f).op (evaluate e (𝟙 V)) = evaluate e f := by
  simpa only [Category.comp_id] using (evaluate_comp e f (𝟙 V)).symm

private theorem restrict_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (p : P.obj (op Z)) :
    P.map f.op (P.map g.op p) = P.map (f ≫ g).op p := by
  rw [op_comp, Functor.map_comp_apply]

private def action : R.obj (L.obj V) ⟶ V :=
  e.inv.app (op (R.obj (L.obj V))) (P.map (a.counit.app (L.obj V)).op (evaluate e (𝟙 V)))

private theorem evaluate_action :
    evaluate e (action a e) = P.map (a.counit.app (L.obj V)).op (evaluate e (𝟙 V)) :=
  ConcreteCategory.congr_hom (e.inv_hom_id_app (op (R.obj (L.obj V)))) _

private theorem evaluate_action_comp {W : D} (f : W ⟶ R.obj (L.obj V)) :
    evaluate e (f ≫ action a e) =
      P.map (L.map f ≫ a.counit.app (L.obj V)).op (evaluate e (𝟙 V)) := by
  rw [evaluate_comp, evaluate_action, op_comp, Functor.map_comp_apply]
  rfl

/-- A representing object for the restriction of a presheaf carries a
canonical descent datum for the adjunction monad. -/
def descentAlgebra : a.toMonad.Algebra where
  A := V
  a := action a e
  unit := by
    change a.unit.app V ≫ action a e = 𝟙 V
    apply (e.app (op V)).toEquiv.injective
    change evaluate e (a.unit.app V ≫ action a e) = evaluate e (𝟙 V)
    have h : L.map (a.unit.app V) ≫ a.counit.app (L.obj V) = 𝟙 _ := a.left_triangle_components V
    rw [evaluate_action_comp, h, op_id]
    exact ConcreteCategory.congr_hom (P.map_id (op (L.obj V))) _
  assoc := by
    change R.map (a.counit.app (L.obj V)) ≫ action a e = R.map (L.map (action a e)) ≫ action a e
    apply (e.app (op (R.obj (L.obj (R.obj (L.obj V)))))).toEquiv.injective
    change evaluate e (R.map (a.counit.app (L.obj V)) ≫ action a e) =
      evaluate e (R.map (L.map (action a e)) ≫ action a e)
    have h₁ := a.counit.naturality (a.counit.app (L.obj V))
    have h₂ := a.counit.naturality (L.map (action a e))
    change L.map (R.map (a.counit.app (L.obj V))) ≫ a.counit.app (L.obj V) =
      a.counit.app (L.obj (R.obj (L.obj V))) ≫ a.counit.app (L.obj V) at h₁
    change L.map (R.map (L.map (action a e))) ≫ a.counit.app (L.obj V) =
      a.counit.app (L.obj (R.obj (L.obj V))) ≫ L.map (action a e) at h₂
    rw [evaluate_action_comp, evaluate_action_comp, h₁, h₂, op_comp, op_comp,
      Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (P.map (a.counit.app (L.obj (R.obj (L.obj V)))).op)
      ((evaluate_action a e).symm.trans (evaluate_from_identity e (action a e)).symm)

/-- A map to the representing object respects descent data exactly when its
section agrees under the two pullbacks along the covering counit. -/
theorem compatible_iff {X : C} (p : R.obj X ⟶ V) :
    (a.toMonad.toFunctor.map p ≫ (descentAlgebra a e).a = ((Monad.comparison a).obj X).a ≫ p) ↔
      P.map (a.counit.app (L.obj (R.obj X))).op (evaluate e p) =
        P.map (L.map (R.map (a.counit.app X))).op (evaluate e p) := by
  change (R.map (L.map p) ≫ action a e = R.map (a.counit.app X) ≫ p) ↔ _
  have h₁ : evaluate e (R.map (L.map p) ≫ action a e) =
      P.map (a.counit.app (L.obj (R.obj X))).op (evaluate e p) := by
    have h := a.counit.naturality (L.map p)
    change L.map (R.map (L.map p)) ≫ a.counit.app (L.obj V) =
      a.counit.app (L.obj (R.obj X)) ≫ L.map p at h
    rw [evaluate_action_comp, h, op_comp, Functor.map_comp_apply]
    exact congrArg (P.map (a.counit.app (L.obj (R.obj X))).op) (evaluate_from_identity e p)
  have h₂ := evaluate_comp e (R.map (a.counit.app X)) p
  rw [← h₁, ← h₂]
  exact ((e.app (op (R.obj (L.obj (R.obj X))))).toEquiv.injective.eq_iff).symm

private theorem comparisonMapBijective
    (hSheaf : ∀ (X Y : C), Presieve.IsSheafFor (yoneda.obj Y) (.singleton (a.counit.app X)))
    (hPull : ∀ X, IsPullback (a.counit.app (L.obj (R.obj X)))
      (L.map (R.map (a.counit.app X))) (a.counit.app X) (a.counit.app X)) (X Y : C) :
    Function.Bijective ((Monad.comparison a).map : (X ⟶ Y) → _) := by
  constructor
  · intro f g h
    have hr : R.map f = R.map g := congrArg (fun z => z.f) h
    have hSep : Function.Injective (fun q : X ⟶ Y => a.counit.app X ≫ q) :=
      Presieve.isSeparatedFor_singleton.mp (hSheaf X Y).isSeparatedFor
    apply hSep
    calc
      _ = L.map (R.map f) ≫ a.counit.app Y := (a.counit.naturality f).symm
      _ = L.map (R.map g) ≫ a.counit.app Y := congrArg (fun q => L.map q ≫ a.counit.app Y) hr
      _ = _ := a.counit.naturality g
  · intro z
    let k := L.map z.f ≫ a.counit.app Y
    have hz : R.map k = R.map (a.counit.app X) ≫ z.f := (R.map_comp _ _).trans z.h
    have hk : a.counit.app (L.obj (R.obj X)) ≫ k = L.map (R.map (a.counit.app X)) ≫ k := by
      calc
        _ = L.map (R.map k) ≫ a.counit.app Y := (a.counit.naturality k).symm
        _ = _ := by rw [hz, L.map_comp, Category.assoc]
    obtain ⟨f, hf, _⟩ := Presieve.isSheafFor_singleton.mp (hSheaf X Y) k (by
      intro Z l r eq
      let s := (hPull X).lift l r eq
      have hl : s ≫ a.counit.app (L.obj (R.obj X)) = l := IsPullback.lift_fst ..
      have hr : s ≫ L.map (R.map (a.counit.app X)) = r := IsPullback.lift_snd ..
      change l ≫ k = r ≫ k
      rw [← hl, ← hr, Category.assoc, Category.assoc, hk])
    refine ⟨f, Monad.Algebra.Hom.ext ?_⟩
    change R.map f = z.f
    apply (a.homEquiv (R.obj X) Y).symm.injective
    exact (a.counit.naturality f).trans hf

/-- Morphisms descend whenever representable presheaves are sheaves for
the counit covers with the indicated pullback overlaps. -/
def comparisonFullyFaithful
    (hSheaf : ∀ (X Y : C), Presieve.IsSheafFor (yoneda.obj Y) (.singleton (a.counit.app X)))
    (hPull : ∀ X, IsPullback (a.counit.app (L.obj (R.obj X)))
      (L.map (R.map (a.counit.app X))) (a.counit.app X) (a.counit.app X)) :
    (Monad.comparison a).FullyFaithful := by
  let h := comparisonMapBijective a hSheaf hPull
  let : (Monad.comparison a).Full := ⟨fun {X Y} => (h X Y).2⟩
  let : (Monad.comparison a).Faithful := ⟨fun {X Y} => (h X Y).1⟩
  exact .ofFullyFaithful _

/-- A model for the representing object's descent datum represents the
original presheaf when the comparison is fully faithful and the counit is
a sheaf cover with the stated double overlap. -/
theorem represents_of_comparison_iso [(Monad.comparison a).Full] [(Monad.comparison a).Faithful]
    (hSheaf : ∀ X, Presieve.IsSheafFor P (.singleton (a.counit.app X)))
    (hPull : ∀ X, IsPullback (a.counit.app (L.obj (R.obj X)))
      (L.map (R.map (a.counit.app X))) (a.counit.app X) (a.counit.app X))
    (A : C) (j : (Monad.comparison a).obj A ≅ descentAlgebra a e) :
    Nonempty (yoneda.obj A ≅ P) := by
  let F := Monad.comparison a
  let Q := descentAlgebra a e
  have hInject (X : C) : Function.Injective (P.map (a.counit.app X).op) :=
    Presieve.isSeparatedFor_singleton.mp (hSheaf X).isSeparatedFor
  have hJ := (compatible_iff a e j.hom.f).mp j.hom.h
  obtain ⟨x, hx, _⟩ := Presieve.isSheafFor_singleton.mp (hSheaf A) (evaluate e j.hom.f) (by
    intro Z g h eq
    let k := (hPull A).lift g h eq
    have hg : k ≫ a.counit.app (L.obj (R.obj A)) = g := IsPullback.lift_fst ..
    have hh : k ≫ L.map (R.map (a.counit.app A)) = h := IsPullback.lift_snd ..
    rw [← hg, ← hh, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (P.map k.op) hJ)
  let η : yoneda.obj A ⟶ P := yonedaEquiv.symm x
  have hEval {X : C} (f : X ⟶ A) :
      P.map (a.counit.app X).op (η.app (op X) f) = evaluate e (F.map f ≫ j.hom).f := by
    have hf : L.map (R.map f) ≫ a.counit.app A = a.counit.app X ≫ f := a.counit.naturality f
    change P.map (a.counit.app X).op (P.map f.op x) = evaluate e (R.map f ≫ j.hom.f)
    calc
      _ = P.map (a.counit.app X ≫ f).op x := restrict_comp (a.counit.app X) f x
      _ = P.map (L.map (R.map f) ≫ a.counit.app A).op x := congrArg (fun k => P.map k.op x) hf.symm
      _ = P.map (L.map (R.map f)).op (P.map (a.counit.app A).op x) :=
        (restrict_comp (L.map (R.map f)) (a.counit.app A) x).symm
      _ = _ := (congrArg (P.map (L.map (R.map f)).op) hx).trans (evaluate_comp e (R.map f) j.hom.f).symm
  have hBij (X : C) : Function.Bijective (η.app (op X)) := by
    constructor
    · intro f g h
      have h' := congrArg (P.map (a.counit.app X).op) h
      rw [hEval f, hEval g] at h'
      apply F.map_injective
      apply (cancel_mono j.hom).mp
      apply Monad.Algebra.Hom.ext
      exact (e.app _).toEquiv.injective h'
    · intro y
      let t := P.map (a.counit.app X).op y
      let u : R.obj X ⟶ V := e.inv.app (op (R.obj X)) t
      have hu : evaluate e u = t := ConcreteCategory.congr_hom (e.inv_hom_id_app (op (R.obj X))) t
      let l := a.counit.app (L.obj (R.obj X))
      let r := L.map (R.map (a.counit.app X))
      have hm : P.map l.op t = P.map r.op t :=
        (restrict_comp l (a.counit.app X) y).trans
          ((congrArg (fun k => P.map k.op y) (hPull X).w).trans (restrict_comp r (a.counit.app X) y).symm)
      let m : F.obj X ⟶ Q := ⟨u, (compatible_iff a e u).mpr
        ((congrArg (P.map l.op) hu).trans (hm.trans (congrArg (P.map r.op) hu.symm)))⟩
      obtain ⟨f, hf⟩ := F.map_surjective (m ≫ j.inv)
      have hk : F.map f ≫ j.hom = m := by rw [hf, Category.assoc, j.inv_hom_id, Category.comp_id]
      refine ⟨f, hInject X ?_⟩
      rw [hEval f, hk]
      exact hu
  let : IsIso η := (NatTrans.isIso_iff_isIso_app η).mpr
    (fun X => (CategoryTheory.isIso_iff_bijective _).mpr (hBij X.unop))
  exact ⟨asIso η⟩

end PhilipponRepresentableDescentDatum

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleNeighborhoodRestriction (along)
open PhilipponEtaleRepresentablePresence (isSheaf_yoneda)


namespace PhilipponEtaleDescentCounit

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

abbrev adjunction : along f ⊣ baseChange f :=
  MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ f inferInstance trivial

private abbrev overAdjunction := Over.mapPullbackAdj f

private def forgetMonadIso : (adjunction f).toMonad.toFunctor ⋙ Scheme.Etale.forget Y ≅
    Scheme.Etale.forget Y ⋙ (overAdjunction f).toMonad.toFunctor := Iso.refl _

private theorem forgetMonadIso_unit (V : Y.Etale) :
    (Scheme.Etale.forget Y).map ((adjunction f).toMonad.η.app V) ≫ (forgetMonadIso f).hom.app V =
      (overAdjunction f).toMonad.η.app ((Scheme.Etale.forget Y).obj V) := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply Over.OverMorphism.ext
  rfl

private theorem forgetMonadIso_mul (V : Y.Etale) :
    (Scheme.Etale.forget Y).map ((adjunction f).toMonad.μ.app V) ≫ (forgetMonadIso f).hom.app V =
      (forgetMonadIso f).hom.app ((adjunction f).toMonad.obj V) ≫
        (overAdjunction f).toMonad.map ((forgetMonadIso f).hom.app V) ≫
          (overAdjunction f).toMonad.μ.app ((Scheme.Etale.forget Y).obj V) := by
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ (overAdjunction f).toMonad.map (𝟙 _) ≫ _
  rw [Category.comp_id, Category.id_comp, (overAdjunction f).toMonad.toFunctor.map_id, Category.id_comp]
  apply Over.OverMorphism.ext
  rfl

/-- Forgetting the étale condition embeds the étale descent data into
the descent data for schemes over the covering scheme. -/
def forgetAlgebras : (adjunction f).toMonad.Algebra ⥤ (overAdjunction f).toMonad.Algebra :=
  PhilipponMonadAlgebraTransport.mapAlgebras (forgetMonadIso f) (forgetMonadIso_unit f) (forgetMonadIso_mul f)

def forgetAlgebrasFullyFaithful : (forgetAlgebras f).FullyFaithful :=
  PhilipponMonadAlgebraTransport.mapAlgebrasFullyFaithful (forgetMonadIso f) (forgetMonadIso_unit f)
    (forgetMonadIso_mul f) (Scheme.Etale.forgetFullyFaithful Y)

/-- The étale and scheme comparisons agree after forgetting. -/
def forgetComparisonIso (W : X.Etale) :
    (forgetAlgebras f).obj ((Monad.comparison (adjunction f)).obj W) ≅
      (Monad.comparison (overAdjunction f)).obj ((Scheme.Etale.forget X).obj W) :=
  Monad.Algebra.isoMk (Iso.refl _) (by
    change (overAdjunction f).toMonad.map (𝟙 _) ≫ _ = (𝟙 _ ≫ _) ≫ 𝟙 _
    rw [(overAdjunction f).toMonad.toFunctor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
    apply Over.OverMorphism.ext
    rfl)

/-- The two counit-derived maps are the projections of the double
overlap of a base-changed étale chart. -/
theorem isPullback_counit (U : X.Etale) :
    let a := adjunction f
    let π := a.counit.app U
    IsPullback (a.counit.app ((along f).obj ((baseChange f).obj U)))
      ((along f).map ((baseChange f).map π)) π π := by
  let a := adjunction f
  let π := a.counit.app U
  let F := Scheme.Etale.forget X ⋙ Over.forget X
  apply IsPullback.of_map_of_faithful F
  exact map_isPullback f π

/-- Étale sheaves satisfy the singleton sheaf condition on each
base-changed chart of a surjective étale map. -/
theorem isSheafFor_counit (P : X.Etaleᵒᵖ ⥤ Type u)
    (h : Presheaf.IsSheaf X.smallEtaleTopology P) [Surjective f] (U : X.Etale) :
    Presieve.IsSheafFor P (.singleton ((adjunction f).counit.app U)) := by
  let π := (adjunction f).counit.app U
  let V (_ : Unit) := (along f).obj ((baseChange f).obj U)
  let p (i : Unit) : V i ⟶ U := π
  have he : Presieve.ofArrows V p = Presieve.singleton π := Presieve.ofArrows_of_unique p
  rw [← he, Presieve.isSheafFor_iff_generate]
  apply h.isSheafFor
  exact (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr (Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.mpr ⟨(), (inferInstance : Surjective (pullback.fst U.hom f)).surj x⟩)

/-- Maps between étale charts descend along a surjective étale map. -/
def comparisonFullyFaithful [Surjective f] : (Monad.comparison (adjunction f)).FullyFaithful :=
  PhilipponRepresentableDescentDatum.comparisonFullyFaithful (adjunction f)
    (fun U V => isSheafFor_counit f (yoneda.obj V) (isSheaf_yoneda V) U)
    (isPullback_counit f)

/-- A model of the descent datum of a locally represented étale sheaf
represents the sheaf on the base. -/
theorem represents_of_descent_model [Surjective f]
    {P : X.Etaleᵒᵖ ⥤ Type u} (hP : Presheaf.IsSheaf X.smallEtaleTopology P) {V : Y.Etale}
    (e : yoneda.obj V ≅ (along f).op ⋙ P) (W : X.Etale)
    (d : (Monad.comparison (adjunction f)).obj W ≅
      PhilipponRepresentableDescentDatum.descentAlgebra (adjunction f) e) :
    Nonempty (yoneda.obj W ≅ P) := by
  let h := comparisonFullyFaithful f
  let := h.full
  let := h.faithful
  exact PhilipponRepresentableDescentDatum.represents_of_comparison_iso (adjunction f) e
    (isSheafFor_counit f P hP) (isPullback_counit f) W d

end PhilipponEtaleDescentCounit

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponEtaleBaseChangeComparison (baseChange coverPreserving)
open PhilipponEtaleDescentCounit (adjunction)
open PhilipponEtaleNeighborhoodRestriction (along restrict restrictionIso)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponTorsorSectionFibers (Torsor)
open PhilipponTorsorTrivialization (changeCoefficients)


namespace PhilipponEtaleTorsorRestriction

universe u

/-- Composing two restrictions is compatible with composition of the chart maps. -/
def alongCompIso {X Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}
    [Etale f] [Etale g] [Etale h] (e : g ≫ f = h) : along g ⋙ along f ≅ along h := by
  refine NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_
  · change 𝟙 _ ≫ U.hom ≫ h = (U.hom ≫ g) ≫ f
    rw [Category.id_comp, Category.assoc, e]
  · intro U V a
    apply MorphismProperty.Over.Hom.ext
    change a.left ≫ 𝟙 _ = 𝟙 _ ≫ a.left
    rw [Category.comp_id, Category.id_comp]

/-- Restricting along the identity preserves the chart. -/
def alongIdIso (X : Scheme.{u}) : along (𝟙 X) ≅ 𝟭 X.Etale := by
  refine NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_
  · change 𝟙 _ ≫ U.hom = U.hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  · intro U V a
    apply MorphismProperty.Over.Hom.ext
    change a.left ≫ 𝟙 _ = 𝟙 _ ≫ a.left
    rw [Category.comp_id, Category.id_comp]

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Restriction of a representable presheaf to an étale neighborhood is
represented by the base change of its representing scheme. -/
def restrictYonedaIso (W : X.Etale) :
    yoneda.obj ((baseChange f).obj W) ≅ (along f).op ⋙ yoneda.obj W := by
  refine NatIso.ofComponents (fun U => Equiv.toIso ((adjunction f).homEquiv U.unop W).symm) ?_
  intro U V g
  apply ConcreteCategory.hom_ext
  intro p
  exact (adjunction f).homEquiv_naturality_left_symm g.unop p

private def restrictTorsor {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (B : Torsor G) :
    Torsor ((restrict f).obj G) where
  D := {
    P := (along f).op ⋙ B.D.P
    diff U := B.D.diff ((along f).op.obj U)
    diff_add_diff U := B.D.diff_add_diff ((along f).op.obj U)
    map_diff g := B.D.map_diff ((along f).op.map g) }
  isSheaf := (along f).op_comp_isSheaf_of_isSheaf _ _ _ B.isSheaf
  locally_nonempty U := by
    let : (along f).IsCocontinuous Y.smallEtaleTopology X.smallEtaleTopology :=
      ((adjunction f).isCocontinuous_iff_coverPreserving _ _).mpr (coverPreserving f)
    exact (along f).cover_lift _ _ (B.locally_nonempty ((along f).obj U))
  diff_bijective U := B.diff_bijective ((along f).op.obj U)

/-- Restriction of torsor sections along an étale neighborhood gives a
torsor under the pullback coefficient sheaf. -/
def pullbackTorsor {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (B : Torsor G) :
    Torsor ((pullbackSheaves f).obj G) :=
  changeCoefficients (restrictTorsor f B) ((restrictionIso f).app G)

end PhilipponEtaleTorsorRestriction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponAffineDescentSpec (overSpec ringAdj schemeAdj monadIso monadIso_unit monadIso_mul)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleDescentCounit (adjunction forgetAlgebras forgetAlgebrasFullyFaithful forgetComparisonIso)
open PhilipponEtaleNeighborhoodRestriction (along)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleTorsorRestriction (alongCompIso alongIdIso pullbackTorsor restrictYonedaIso)
open PhilipponTorsorSectionFibers (Torsor)
open PhilipponTorsorTrivialization (changeCoefficients)


namespace PhilipponEtaleAffineRepresentability

universe u

/-- An affine finite étale chart equipped with descent data over a
faithfully flat étale affine cover descends to a finite étale chart. -/
theorem exists_model_of_finiteEtale_descent {R S : CommRingCat.{u}} (f : R ⟶ S)
    [Etale (Spec.map f)] (hf : f.hom.FaithfullyFlat)
    (D : (adjunction (Spec.map f)).toMonad.Algebra) [IsFinite D.A.hom] [IsAffine D.A.left] :
    ∃ W : (Spec R).Etale, IsFinite W.hom ∧
      Nonempty ((Monad.comparison (adjunction (Spec.map f))).obj W ≅ D) := by
  let σ := Spec.map f
  let E := (forgetAlgebras σ).obj D
  let : IsAffine E.A.left := (inferInstance : IsAffine D.A.left)
  obtain ⟨B, ⟨e⟩⟩ := PhilipponAffineDescentSpec.exists_under_of_affine E.A
  let e' := (Over.forget (Spec S)).mapIso e
  have he : e'.hom ≫ D.A.hom = Spec.map B.hom := Over.w e.hom
  have hF : B.hom.hom.Finite := (IsFinite.SpecMap_iff B.hom).mp
    (he ▸ inferInstanceAs (IsFinite (e'.hom ≫ D.A.hom)))
  have hE : B.hom.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (he ▸ inferInstanceAs (Etale (e'.hom ≫ D.A.hom)))
  let hff := PhilipponAffineDescentSpec.overSpecFullyFaithful S
  let := hff.full
  let := hff.faithful
  obtain ⟨Q, hQ, ⟨q⟩⟩ := PhilipponMonadAlgebraTransport.exists_algebra_lift
    (monadIso f) (monadIso_unit f) (monadIso_mul f) E (op B) e
  have hQF : Q.A.unop.hom.hom.Finite := by rw [hQ]; exact hF
  have hQE : Q.A.unop.hom.hom.Etale := by rw [hQ]; exact hE
  obtain ⟨A, hAF, hAE, ⟨d⟩⟩ :=
    PhilipponFaithfullyFlatAlgebraDescent.exists_opposite_finiteEtale_model f hf Q hQF hQE
  let g := Spec.map A.hom
  let : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hAE
  let W := Scheme.Etale.mk g
  have hFin : IsFinite W.hom := (IsFinite.SpecMap_iff A.hom).mpr hAF
  let K := PhilipponAffineDescentSpec.mapAlgebras f
  let c := PhilipponAffineDescentSpec.comparisonIso f (op A)
  let a := forgetComparisonIso σ W
  have hIso : (forgetAlgebras σ).obj ((Monad.comparison (adjunction σ)).obj W) ≅ (forgetAlgebras σ).obj D :=
    a ≪≫ c.symm ≪≫ K.mapIso d ≪≫ q
  exact ⟨W, hFin, ⟨(forgetAlgebrasFullyFaithful σ).preimageIso hIso⟩⟩

/-- Over the spectrum of a ring, a torsor under a pulled-back finite
constant coefficient sheaf is represented by a finite étale chart. -/
theorem exists_finiteEtale_representation {Y : Scheme.{u}} (R : CommRingCat.{u}) (j : Spec R ⟶ Y)
    (M : Type u) [AddCommGroup M] [Finite M]
    (B : Torsor ((pullbackSheaves j).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)))) :
    ∃ W : (Spec R).Etale, IsFinite W.hom ∧ Nonempty (yoneda.obj W ≅ B.D.P) := by
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨S, f, hEt, hFlat, V, hV, hAff, ⟨e⟩⟩ :=
    PhilipponEtaleConstantTorsorLocalModel.exists_model_on_spec_cover M R j B
  let σ := Spec.map f
  let : Surjective σ := ((flat_and_surjective_SpecMap_iff f).mpr hFlat).2
  let Q := PhilipponRepresentableDescentDatum.descentAlgebra (adjunction σ) e.symm
  let : IsFinite Q.A.hom := hV
  let : IsAffine Q.A.left := hAff
  obtain ⟨W, hW, ⟨d⟩⟩ := exists_model_of_finiteEtale_descent f hFlat Q
  exact ⟨W, hW, PhilipponEtaleDescentCounit.represents_of_descent_model σ B.isSheaf e.symm W d⟩

/-- The finite étale model over an affine base is independent of the choice
of a presentation of that base as a spectrum. -/
theorem exists_finiteEtale_representation_of_isAffine {A Y : Scheme.{u}} [IsAffine A] (j : A ⟶ Y)
    (M : Type u) [AddCommGroup M] [Finite M]
    (B : Torsor ((pullbackSheaves j).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)))) :
    ∃ W : A.Etale, IsFinite W.hom ∧ Nonempty (yoneda.obj W ≅ B.D.P) := by
  let R := Γ(A, ⊤)
  let e : A ≅ Spec R := A.isoSpec
  let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)
  let D := changeCoefficients (pullbackTorsor e.inv B) ((pullbackCompIso j e.inv).app G)
  obtain ⟨V, hV, ⟨m⟩⟩ := exists_finiteEtale_representation R (e.inv ≫ j) M D
  let : IsFinite V.hom := hV
  let W := (baseChange e.hom).obj V
  have hW : IsFinite W.hom := inferInstanceAs (IsFinite (pullback.snd V.hom e.hom))
  let F := (along e.hom).op
  let K := (along e.inv).op
  let c := alongCompIso e.hom_inv_id ≪≫ alongIdIso A
  let E := (Functor.opComp (along e.hom) (along e.inv)).symm ≪≫ NatIso.op c.symm
  exact ⟨W, hW, ⟨restrictYonedaIso e.hom V ≪≫ Functor.isoWhiskerLeft F m ≪≫
    (Functor.associator F K B.D.P).symm ≪≫ Functor.isoWhiskerRight E B.D.P ≪≫
    Functor.leftUnitor B.D.P⟩⟩

end PhilipponEtaleAffineRepresentability

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleDescentCounit (adjunction)
open PhilipponEtaleNeighborhoodRestriction (along)


namespace PhilipponEtaleRepresentabilityLocal

universe u

/-- The section over the representing chart that corresponds to its
identity after restriction to an étale neighborhood. -/
abbrev localSection {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {P : X.Etaleᵒᵖ ⥤ Type u} {W : Y.Etale}
    (e : yoneda.obj W ≅ (along f).op ⋙ P) : P.obj (op ((along f).obj W)) :=
  e.hom.app (op W) (𝟙 W)

theorem map_localSection {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {P : X.Etaleᵒᵖ ⥤ Type u} {W : Y.Etale} (e : yoneda.obj W ≅ (along f).op ⋙ P)
    {U : Y.Etale} (g : U ⟶ W) :
    P.map ((along f).map g).op (localSection f e) = e.hom.app (op U) g := by
  have h := NatTrans.naturality_apply e.hom g.op (𝟙 W)
  change e.hom.app (op U) (g ≫ 𝟙 W) = P.map ((along f).map g).op (localSection f e) at h
  rw [Category.comp_id] at h
  exact h.symm

section Cover

variable {X : Scheme.{u}} {I : Type u} {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i)]

private theorem counit_covers (hCover : ∀ x : X, ∃ (i : I) (y : Y i), f i y = x) (U : X.Etale) :
    Sieve.ofArrows (fun i => (along (f i)).obj ((baseChange (f i)).obj U))
      (fun i => (adjunction (f i)).counit.app U) ∈ X.smallEtaleTopology U := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := hCover (U.hom x)
  obtain ⟨p, hp, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback U.hom (f i)) x y hy.symm
  exact Set.mem_iUnion.mpr ⟨i, ⟨p, hp⟩⟩

/-- A map of étale sheaves is an isomorphism if its restrictions are
isomorphisms on a jointly surjective family of étale neighborhoods. -/
theorem isIso_of_etale_cover_restrictions
    (F G : Sheaf X.smallEtaleTopology (Type u)) (m : F ⟶ G)
    (hCover : ∀ x : X, ∃ (i : I) (y : Y i), f i y = x)
    (hIso : ∀ i, IsIso (Functor.whiskerLeft (along (f i)).op m.hom)) : IsIso m := by
  have hB (i : I) (U : (Y i).Etale) : Function.Bijective (m.hom.app (op ((along (f i)).obj U))) := by
    let := hIso i
    exact CategoryTheory.isIso_iff_bijective _ |>.mp
      (inferInstance : IsIso ((Functor.whiskerLeft (along (f i)).op m.hom).app (op U)))
  apply (Sheaf.isLocallyBijective_iff_isIso m).mp
  constructor
  · constructor
    intro U a b hab
    apply X.smallEtaleTopology.superset_covering _ (counit_covers f hCover U.unop)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    let p := (adjunction (f i)).counit.app U.unop
    apply (hB i ((baseChange (f i)).obj U.unop)).1
    exact (NatTrans.naturality_apply m.hom p.op a).trans
      ((congrArg (G.obj.map p.op) hab).trans (NatTrans.naturality_apply m.hom p.op b).symm)
  · constructor
    intro U a
    apply X.smallEtaleTopology.superset_covering _ (counit_covers f hCover U)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact (hB i ((baseChange (f i)).obj U)).2 (G.obj.map ((adjunction (f i)).counit.app U).op a)

end Cover

end PhilipponEtaleRepresentabilityLocal

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleDescentCounit (adjunction)
open PhilipponEtaleNeighborhoodRestriction (along)
open PhilipponEtaleRepresentabilityLocal (localSection map_localSection)
open PhilipponEtaleTorsorRestriction (alongCompIso restrictYonedaIso)


namespace PhilipponEtaleAffineModels

universe u v

variable {X : Scheme.{u}} (P : X.Etaleᵒᵖ ⥤ Type u)

/-- Finite étale scheme models for the restriction of a presheaf to each
affine open of its base. -/
structure Models where
  chart (U : X.AffineZariskiSite) : U.toOpens.toScheme.Etale
  finite (U : X.AffineZariskiSite) : IsFinite (chart U).hom
  represents (U : X.AffineZariskiSite) : yoneda.obj (chart U) ≅ (along U.toOpens.ι).op ⋙ P

namespace Models

variable {P} (M : Models P)

private abbrev 𝒰 := Scheme.AffineZariskiSite.directedCover X

abbrev overBase (U : X.AffineZariskiSite) : X.Etale :=
  (along U.toOpens.ι).obj (M.chart U)

abbrev sectionAt (U : X.AffineZariskiSite) : P.obj (op (M.overBase U)) :=
  localSection U.toOpens.ι (M.represents U)

private def chartOver {U V : X.AffineZariskiSite} (g : U ⟶ V) : V.toOpens.toScheme.Etale :=
  Scheme.Etale.mk ((M.chart U).hom ≫ (𝒰 (X := X)).trans g)

private def chartOverIso {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    (along V.toOpens.ι).obj (M.chartOver g) ≅ M.overBase U :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (M.chart U).hom ≫ U.toOpens.ι =
      ((M.chart U).hom ≫ (𝒰 (X := X)).trans g) ≫ V.toOpens.ι
    rw [Category.id_comp, Category.assoc, Scheme.Cover.trans_map (𝒰 (X := X)) g])

private def chartMap {U V : X.AffineZariskiSite} (g : U ⟶ V) : M.chartOver g ⟶ M.chart V :=
  (M.represents V).inv.app (op (M.chartOver g))
    (P.map (M.chartOverIso g).hom.op (M.sectionAt U))

/-- The map between models over nested affine opens obtained by restricting
their universal sections. -/
def transition {U V : X.AffineZariskiSite} (g : U ⟶ V) : M.overBase U ⟶ M.overBase V :=
  (M.chartOverIso g).inv ≫ (along V.toOpens.ι).map (M.chartMap g)

theorem transition_projection {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    (M.transition g).left ≫ (M.chart V).hom = (M.chart U).hom ≫ (𝒰 (X := X)).trans g := by
  change (𝟙 _ ≫ (M.chartMap g).left) ≫ (M.chart V).hom = _
  rw [Category.id_comp]
  exact MorphismProperty.Over.w (M.chartMap g)

theorem transition_section {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    P.map (M.transition g).op (M.sectionAt V) = M.sectionAt U := by
  let e := M.chartOverIso g
  let a := M.represents V
  have h : a.hom.app (op (M.chartOver g)) (M.chartMap g) = P.map e.hom.op (M.sectionAt U) :=
    ConcreteCategory.congr_hom (a.inv_hom_id_app (op (M.chartOver g))) _
  change P.map (e.inv ≫ (along V.toOpens.ι).map (M.chartMap g)).op (M.sectionAt V) = _
  rw [op_comp, Functor.map_comp_apply, map_localSection, h, ← Functor.map_comp_apply, ← op_comp,
    e.inv_hom_id, op_id, P.map_id]
  rfl

theorem transition_unique {U V : X.AffineZariskiSite} (g : U ⟶ V) (a : M.overBase U ⟶ M.overBase V)
    (h : P.map a.op (M.sectionAt V) = M.sectionAt U) : a = M.transition g := by
  have hp : a.left ≫ (M.chart V).hom = (M.chart U).hom ≫ (𝒰 (X := X)).trans g := by
    apply (cancel_mono V.toOpens.ι).mp
    have ha := MorphismProperty.Over.w a
    change a.left ≫ ((M.chart V).hom ≫ V.toOpens.ι) = (M.chart U).hom ≫ U.toOpens.ι at ha
    rw [Category.assoc, Category.assoc, Scheme.Cover.trans_map (𝒰 (X := X)) g]
    exact ha
  let b : M.chartOver g ⟶ M.chart V := MorphismProperty.Over.homMk a.left hp trivial
  let e := M.chartOverIso g
  have hb : (along V.toOpens.ι).map b = e.hom ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.id_comp a.left).symm
  have hsec : (M.represents V).hom.app (op (M.chartOver g)) b = P.map e.hom.op (M.sectionAt U) := by
    calc
      _ = P.map ((along V.toOpens.ι).map b).op (M.sectionAt V) := (map_localSection _ (M.represents V) b).symm
      _ = _ := by rw [hb, op_comp, Functor.map_comp_apply, h]
  have hc : b = M.chartMap g := ((M.represents V).app (op (M.chartOver g))).toEquiv.injective
    (hsec.trans (ConcreteCategory.congr_hom ((M.represents V).inv_hom_id_app (op (M.chartOver g))) _).symm)
  apply MorphismProperty.Over.Hom.ext
  have hd := congrArg (fun c => c.left) hc
  change a.left = 𝟙 _ ≫ (M.chartMap g).left
  exact hd.trans (Category.id_comp _).symm

private theorem transition_id (U : X.AffineZariskiSite) : M.transition (𝟙 U) = 𝟙 (M.overBase U) := by
  symm
  apply M.transition_unique
  rw [op_id, P.map_id]
  rfl

private theorem transition_comp {U V Z : X.AffineZariskiSite} (g : U ⟶ V) (h : V ⟶ Z) :
    M.transition (g ≫ h) = M.transition g ≫ M.transition h := by
  symm
  apply M.transition_unique
  rw [op_comp, Functor.map_comp_apply, M.transition_section, M.transition_section]

private def restrictedModelIso {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    yoneda.obj ((baseChange ((𝒰 (X := X)).trans g)).obj (M.chart V)) ≅ (along U.toOpens.ι).op ⋙ P :=
  let F := (along ((𝒰 (X := X)).trans g)).op
  let G := (along V.toOpens.ι).op
  restrictYonedaIso ((𝒰 (X := X)).trans g) (M.chart V) ≪≫
    Functor.isoWhiskerLeft F (M.represents V) ≪≫ (Functor.associator F G P).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (alongCompIso ((𝒰 (X := X)).trans_map g)).symm) P

private theorem restrictedModelIso_apply {U V : X.AffineZariskiSite} (g : U ⟶ V)
    (z : M.chart U ⟶ (baseChange ((𝒰 (X := X)).trans g)).obj (M.chart V)) :
    (M.restrictedModelIso g).hom.app (op (M.chart U)) z =
      P.map (M.chartOverIso g).inv.op ((M.represents V).hom.app (op (M.chartOver g))
        (((adjunction ((𝒰 (X := X)).trans g)).homEquiv (M.chart U) (M.chart V)).symm z)) := by
  rfl

private theorem model_section_preimage {C : Type v} [Category.{u} C]
    {U V : C} {Q : Cᵒᵖ ⥤ Type u} (e : yoneda.obj U ≅ Q) (d : yoneda.obj V ≅ Q) :
    d.hom.app (op U) (yoneda.preimageIso (e ≪≫ d.symm)).hom = e.hom.app (op U) (𝟙 U) := by
  let w := yoneda.preimageIso (e ≪≫ d.symm)
  have hw : yoneda.map w.hom = (e ≪≫ d.symm).hom := yoneda.map_preimage _
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hw (op U)) (𝟙 U)
  change 𝟙 U ≫ w.hom = d.inv.app (op U) (e.hom.app (op U) (𝟙 U)) at h
  rw [Category.id_comp] at h
  exact (congrArg (fun z => d.hom.app (op U) z) h).trans
    (((d.app (op U)).toEquiv).apply_symm_apply _)

/-- The map between models over nested affine opens is a pullback. -/
theorem transition_isPullback {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    IsPullback (M.transition g).left (M.chart U).hom (M.chart V).hom ((𝒰 (X := X)).trans g) := by
  let k := (𝒰 (X := X)).trans g
  let d := M.restrictedModelIso g
  let e := M.represents U ≪≫ d.symm
  let w := yoneda.preimageIso e
  let b := ((adjunction k).homEquiv (M.chart U) (M.chart V)).symm w.hom
  have hb : b.left = w.hom.left ≫ pullback.fst (M.chart V).hom k := rfl
  let a := (M.chartOverIso g).inv ≫ (along V.toOpens.ι).map b
  have he : d.hom.app (op (M.chart U)) w.hom = M.sectionAt U := model_section_preimage (M.represents U) d
  have hsec : P.map a.op (M.sectionAt V) = M.sectionAt U := by
    change P.map ((M.chartOverIso g).inv ≫ (along V.toOpens.ι).map b).op (M.sectionAt V) = _
    rw [op_comp, Functor.map_comp_apply, map_localSection]
    exact (M.restrictedModelIso_apply g w.hom).symm.trans he
  have ha := M.transition_unique g a hsec
  have ht : w.hom.left ≫ pullback.fst (M.chart V).hom k = (M.transition g).left := by
    rw [← hb, ← ha]
    exact (Category.id_comp b.left).symm
  let w' := (Scheme.Etale.forget U.toOpens.toScheme ⋙ Over.forget _).mapIso w
  have hs : w'.hom ≫ pullback.snd (M.chart V).hom k = (M.chart U).hom := MorphismProperty.Over.w w.hom
  exact (IsPullback.of_hasPullback (M.chart V).hom k).of_iso' w' (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (ht.trans (Category.comp_id _).symm) (hs.trans (Category.comp_id _).symm)
    (by simp) (by change 𝟙 _ ≫ k = k ≫ 𝟙 _; rw [Category.id_comp, Category.comp_id])

def diagram : X.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := (M.chart U).left
  map g := (M.transition g).left
  map_id U := congrArg (fun t => t.left) (M.transition_id U)
  map_comp g h := congrArg (fun t => t.left) (M.transition_comp g h)

/-- The affine models give a relative scheme gluing datum. -/
def gluing : (𝒰 (X := X)).RelativeGluingData where
  functor := M.diagram
  natTrans := { app U := (M.chart U).hom, naturality _ _ g := M.transition_projection g }
  equifibered {_U _V} g := M.transition_isPullback g

end Models

end PhilipponEtaleAffineModels

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 450000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAffineModels (Models)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleDescentCounit (adjunction)
open PhilipponEtaleNeighborhoodRestriction (along)
open PhilipponEtaleRepresentabilityLocal (isIso_of_etale_cover_restrictions)
open PhilipponEtaleRepresentablePresence (isSheaf_yoneda)
open PhilipponEtaleTorsorRestriction (restrictYonedaIso)


namespace PhilipponEtaleRepresentabilityGluing

universe u

variable {X : Scheme.{u}} {P : X.Etaleᵒᵖ ⥤ Type u} (M : Models P)

private abbrev 𝒰 := Scheme.AffineZariskiSite.directedCover X

private instance {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    IsOpenImmersion (M.gluing.functor.map g) := by
  apply MorphismProperty.of_isPullback (M.gluing.equifibered g).flip
  infer_instance

private instance : (M.gluing.functor ⋙ Scheme.forget).IsLocallyDirected :=
  M.gluing.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

private theorem localProperty (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ U, Q (M.chart U).hom) : Q M.gluing.toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := Q) (𝒰 (X := X))]
  intro U
  rw [Scheme.Cover.pullbackHom, ← (M.gluing.isPullback_natTrans_ι_toBase U).flip.isoPullback_inv_snd,
    Q.cancel_left_of_respectsIso]
  exact hQ U

private instance : Etale M.gluing.toBase :=
  localProperty M @Etale fun U => inferInstanceAs (Etale (M.chart U).hom)

private abbrev W : X.Etale := Scheme.Etale.mk M.gluing.toBase

private def ι (U : X.AffineZariskiSite) : M.overBase U ⟶ W M :=
  MorphismProperty.Over.homMk (colimit.ι M.gluing.functor U) (M.gluing.ι_toBase U)

private theorem ι_covers : Sieve.ofArrows M.overBase (ι M) ∈ X.smallEtaleTopology (W M) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨U, y, h⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective M.gluing.functor x
  exact Set.mem_iUnion.mpr ⟨U, ⟨y, h⟩⟩

private theorem transition_ι {U V : X.AffineZariskiSite} (g : U ⟶ V) :
    M.transition g ≫ ι M V = ι M U :=
  MorphismProperty.Over.Hom.ext (colimit.w M.gluing.functor g)

private instance mono_ι (U : X.AffineZariskiSite) : Mono (ι M U) := by
  let : Mono (ι M U).left := inferInstanceAs (Mono (M.gluing.cover.f U))
  constructor
  intro Z a b h
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (ι M U).left).mp
  exact congrArg (fun p => p.left) h

private abbrev OverlapIndex (U V : X.AffineZariskiSite) := Σ Q, (Q ⟶ U) × (Q ⟶ V)

private theorem compatible (hP : Presheaf.IsSheaf X.smallEtaleTopology P) :
    Presieve.Arrows.Compatible P (ι M) M.sectionAt := by
  intro U V T a b h
  let f := a ≫ ι M U
  let T' (i : OverlapIndex U V) := pullback f (ι M i.1)
  let p (i : OverlapIndex U V) : T' i ⟶ T := pullback.fst f (ι M i.1)
  let q (i : OverlapIndex U V) : T' i ⟶ M.overBase i.1 := pullback.snd f (ι M i.1)
  have hp : Sieve.ofArrows T' p ∈ X.smallEtaleTopology T := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    have hx : (ι M U).left (a.left x) = (ι M V).left (b.left x) :=
      congrArg (fun k => k.left x) h
    obtain ⟨Q, g₁, g₂, y, hy, _⟩ := M.gluing.cover.exists_of_f_eq_f (a.left x) (b.left x) hx
    let i : OverlapIndex U V := ⟨Q, g₁, g₂⟩
    have he : f.left x = (ι M Q).left y := by
      change (ι M U).left (a.left x) = _
      rw [← hy]
      exact congrArg (fun k => k.left y) (transition_ι M g₁)
    let K := Scheme.Etale.forget X ⋙ Over.forget X
    let : PreservesLimitsOfShape WalkingCospan K := by dsimp [K]; infer_instance
    have hb : IsPullback (p i).left (q i).left f.left (ι M Q).left :=
      (IsPullback.of_hasPullback f (ι M Q)).map K
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback hb x y he
    exact Set.mem_iUnion.mpr ⟨i, ⟨z, hz⟩⟩
  apply (Presieve.isSeparatedFor_iff_generate.mpr (hP.isSheafFor _ hp).isSeparatedFor).ext
  rintro _ _ ⟨i⟩
  have ha : p i ≫ a = q i ≫ M.transition i.2.1 := by
    apply (cancel_mono (ι M U)).mp
    rw [Category.assoc, Category.assoc, transition_ι]
    exact pullback.condition
  have hb : p i ≫ b = q i ≫ M.transition i.2.2 := by
    apply (cancel_mono (ι M V)).mp
    rw [Category.assoc, Category.assoc, transition_ι, ← h]
    exact pullback.condition
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ha, hb,
    op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, M.transition_section, M.transition_section]

private def chartIso (U : X.AffineZariskiSite) :
    M.chart U ≅ (baseChange U.toOpens.ι).obj (W M) :=
  MorphismProperty.Over.isoMk (M.gluing.isPullback_natTrans_ι_toBase U).flip.isoPullback
    (M.gluing.isPullback_natTrans_ι_toBase U).flip.isoPullback_hom_snd

private theorem chartIso_adjoint (U : X.AffineZariskiSite) :
    ((adjunction U.toOpens.ι).homEquiv (M.chart U) (W M)).symm (chartIso M U).hom = ι M U :=
  MorphismProperty.Over.Hom.ext (M.gluing.isPullback_natTrans_ι_toBase U).flip.isoPullback_hom_fst

private theorem restriction_isIso (s : P.obj (op (W M)))
    (hs : ∀ U, P.map (ι M U).op s = M.sectionAt U) (U : X.AffineZariskiSite) :
    IsIso (Functor.whiskerLeft (along U.toOpens.ι).op (yonedaEquiv.symm s)) := by
  let r := yoneda.mapIso (chartIso M U) ≪≫ restrictYonedaIso U.toOpens.ι (W M)
  let a := Functor.whiskerLeft (along U.toOpens.ι).op (yonedaEquiv.symm s)
  have he : r.hom ≫ a = (M.represents U).hom := by
    apply yonedaEquiv.injective
    change a.app (op (M.chart U)) (r.hom.app (op (M.chart U)) (𝟙 (M.chart U))) = M.sectionAt U
    have hr : r.hom.app (op (M.chart U)) (𝟙 (M.chart U)) = ι M U := by
      change ((adjunction U.toOpens.ι).homEquiv (M.chart U) (W M)).symm (𝟙 _ ≫ (chartIso M U).hom) = _
      rw [Category.id_comp, chartIso_adjoint]
    rw [hr]
    exact hs U
  change IsIso a
  rw [show a = r.inv ≫ (M.represents U).hom from (Iso.eq_inv_comp r).mpr he]
  infer_instance

/-- Finite étale models of the restrictions of a sheaf to the affine opens
of its base glue to a finite étale model of the original sheaf. -/
theorem exists_finiteEtale_representation (M : Models P) (hP : Presheaf.IsSheaf X.smallEtaleTopology P) :
    ∃ V : X.Etale, IsFinite V.hom ∧ Nonempty (yoneda.obj V ≅ P) := by
  have hSheaf := (Presieve.isSheafFor_iff_generate _).mpr (hP.isSheafFor _ (ι_covers M))
  obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hSheaf M.sectionAt (compatible M hP)
  let F : Sheaf X.smallEtaleTopology (Type u) := ⟨yoneda.obj (W M), isSheaf_yoneda (W M)⟩
  let G : Sheaf X.smallEtaleTopology (Type u) := ⟨P, hP⟩
  let m : F ⟶ G := ⟨yonedaEquiv.symm s⟩
  have hc : ∀ x : X, ∃ (U : X.AffineZariskiSite) (y : U.toOpens.toScheme), U.toOpens.ι y = x := by
    intro x
    obtain ⟨y, hy⟩ := (𝒰 (X := X)).covers x
    exact ⟨(𝒰 (X := X)).idx x, y, hy⟩
  let : IsIso m := isIso_of_etale_cover_restrictions (fun U : X.AffineZariskiSite => U.toOpens.ι)
    F G m hc (restriction_isIso M s hs)
  exact ⟨W M, localProperty M @IsFinite M.finite,
    ⟨(sheafToPresheaf X.smallEtaleTopology (Type u)).mapIso (asIso m)⟩⟩

end PhilipponEtaleRepresentabilityGluing

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponEtaleAffineModels (Models)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleTorsorRestriction (pullbackTorsor)
open PhilipponTorsorSectionFibers (Torsor)
open PhilipponTorsorTrivialization (changeCoefficients)

namespace PhilipponEtaleTorsorRepresentability

universe u

/-- A torsor under a pulled-back finite constant étale sheaf is represented
by a finite étale scheme over the base of the torsor. -/
theorem exists_finiteEtale_representation {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : Type u) [AddCommGroup M] [Finite M]
    (B : Torsor ((pullbackSheaves j).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)))) :
    ∃ W : X.Etale, IsFinite W.hom ∧ Nonempty (yoneda.obj W ≅ B.D.P) := by
  let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)
  have h (U : X.AffineZariskiSite) :=
    PhilipponEtaleAffineRepresentability.exists_finiteEtale_representation_of_isAffine (U.toOpens.ι ≫ j) M
      (changeCoefficients (pullbackTorsor U.toOpens.ι B) ((pullbackCompIso j U.toOpens.ι).app G))
  choose W hF hR using h
  let D : Models B.D.P := ⟨W, hF, fun U => (hR U).some⟩
  exact PhilipponEtaleRepresentabilityGluing.exists_finiteEtale_representation D B.isSheaf

end PhilipponEtaleTorsorRepresentability

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem solution
    {Y T : Scheme.{u}} (j : T ⟶ Y) (N : ℕ) (hN : N ≠ 0)
    (B : PhilipponTorsorSectionFibers.Torsor ((PhilipponEtaleSmallSite.pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))) :
    ∃ V : T.Etale, IsFinite V.hom ∧ Nonempty (yoneda.obj V ≅ B.D.P) := by
  let : NeZero N := ⟨hN⟩
  exact PhilipponEtaleTorsorRepresentability.exists_finiteEtale_representation j (ULift.{u} (ZMod N)) B

end

end
