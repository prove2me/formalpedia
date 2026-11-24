-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_equivariant_lift_constant_etale_torsor_closed_fiber_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T07:10:36.123805+00:00
-- url     : https://prove2.me/submissions/cbf5223a-ae58-4ba7-9d17-19c5c45d7da2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Spectral.ConstructibleTopology
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_appTop_eq_idempotent_closed_fiber_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_etale_cover_lift_of_proper_closed_fiber
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_etale_representation_constant_torsor_of_ne_zero
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

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

/-- Under the continuous-function model, the adjunction unit sends a
coefficient to the function with that constant value. -/
theorem homEquiv_constantSheafIso {T : X.Etale} (hT : IsTerminal T) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv
      (AddCommGrpCat.of A) (continuousSheaf X A) (constantSheafIso X A).hom =
      (constantMap X A).app (op T) := by
  let J := X.smallEtaleTopology
  let P := (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A)
  have h : toSheafify J P ≫ (constantSheafIso X A).hom.hom = constantMap X A := by
    change toSheafify J P ≫ sheafifyMap J (constantMap X A) ≫
      (isoSheafify J (continuousSheaf X A).property).inv = _
    rw [← toSheafify_naturality_assoc, isoSheafify_inv, toSheafify_sheafifyLift, Category.comp_id]
  rw [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app]
  change (𝟙 _ ≫ (toSheafify J P).app (op T)) ≫ (constantSheafIso X A).hom.hom.app (op T) = _
  rw [Category.id_comp]
  exact NatTrans.congr_app h (op T)

theorem homEquiv_constantSheafIso_apply {T : X.Etale} (hT : IsTerminal T) (a : A) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv
      (AddCommGrpCat.of A) (continuousSheaf X A) (constantSheafIso X A).hom a =
      ContinuousMap.const T.left a := by
  rw [homEquiv_constantSheafIso X A hT]
  rfl

end PhilipponEtaleConstantDegreeZero

end

section

set_option autoImplicit false

open CategoryTheory Filter Opposite TopologicalSpace
open scoped Topology


namespace PhilipponSpectralClosedSections

universe u

section Topology

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

private abbrev inPatch (V : Set X) : Set (WithConstructibleTopology X) :=
  WithTopology.ofTopology ⁻¹' V

omit [SpectralSpace X] in
private theorem isClopen_inPatch {V : Set X} (hV : IsOpen V) (hVc : IsCompact V) :
    IsClopen (inPatch V) := by
  have hOpen : IsOpen[constructibleTopology X] V :=
    hVc.isOpen_constructibleTopology_of_isOpen hV
  have hCompl : IsOpen[constructibleTopology X] Vᶜ :=
    IsCompact.isOpen_constructibleTopology_of_isClosed (by simpa using hVc) hV.isClosed_compl
  exact ⟨isOpen_compl_iff.mp (WithConstructibleTopology.isOpen_iff.mpr hCompl),
    WithConstructibleTopology.isOpen_iff.mpr hOpen⟩

/-- An open set in a spectral space is open in its constructible topology. -/
theorem isOpen_inPatch {V : Set X} (hV : IsOpen V) : IsOpen (inPatch V) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨U, ⟨hU, hUc⟩, hxU, hUV⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
      (show x.ofTopology ∈ V from hx) hV
  exact ⟨inPatch U, Set.preimage_mono hUV, (isClopen_inPatch hU hUc).2, hxU⟩

end Topology
end PhilipponSpectralClosedSections

end

section

set_option autoImplicit false

open TopologicalSpace Topology
open PhilipponSpectralClosedSections

namespace PhilipponSpectralClosedClopens

universe u

/-- A clopen subset of a closed subspace extends when the subspace meets
every point closure in a nonempty connected set. -/
theorem exists_clopen_of_closedEmbedding {X Z : Type u} [TopologicalSpace X]
    [SpectralSpace X] [TopologicalSpace Z] {i : Z → X} (hi : IsClosedEmbedding i)
    (hConn : ∀ x : X, IsConnected (Set.range i ∩ closure ({x} : Set X)))
    {U : Set Z} (hU : IsClopen U) : ∃ V : Set X, IsClopen V ∧ i ⁻¹' V = U := by
  let C := i '' U
  let D := i '' Uᶜ
  have hC : IsClosed C := hi.isClosedMap U hU.1
  have hD : IsClosed D := hi.isClosedMap Uᶜ hU.2.isClosed_compl
  have hDisjoint : Disjoint C D := Set.disjoint_left.mpr (by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact hw (hi.injective hwz ▸ hz))
  have hUnion : C ∪ D = Set.range i := by
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ]
  let V : Set X := {x | ∃ z ∈ C, x ⤳ z}
  let W : Set X := {x | ∃ z ∈ D, x ⤳ z}
  have hV (x : X) : x ∈ V ↔ x ∉ W := by
    let E := Set.range i ∩ closure ({x} : Set X)
    have hCover : E ⊆ C ∪ D := by rw [hUnion]; exact Set.inter_subset_left
    constructor
    · rintro ⟨z, hz, hxz⟩ ⟨w, hw, hxw⟩
      have hOpenCover : E ⊆ Dᶜ ∪ Cᶜ := fun y _ => by
        by_cases hy : y ∈ D
        · exact Or.inr (fun hyC => Set.disjoint_left.mp hDisjoint hyC hy)
        · exact Or.inl hy
      obtain ⟨y, hy, hyD, hyC⟩ := (hConn x).2 Dᶜ Cᶜ hD.isOpen_compl hC.isOpen_compl
        hOpenCover
        ⟨z, ⟨hUnion ▸ Or.inl hz, specializes_iff_mem_closure.mp hxz⟩,
          fun h => Set.disjoint_left.mp hDisjoint hz h⟩
        ⟨w, ⟨hUnion ▸ Or.inr (a := w ∈ C) hw, specializes_iff_mem_closure.mp hxw⟩,
          fun h => Set.disjoint_left.mp hDisjoint h hw⟩
      exact (hCover hy).elim hyC hyD
    · intro hn
      obtain ⟨z, hz⟩ := (hConn x).1
      have hxz := specializes_iff_mem_closure.mpr hz.2
      exact ⟨z, (hCover hz).resolve_right (fun hzD => hn ⟨z, hzD, hxz⟩), hxz⟩
  have hc : V = Wᶜ := Set.ext hV
  have hd : W = Vᶜ := by rw [hc, compl_compl]
  have hopen (B E : Set X) (hE : IsClosed E) (hB : B = {x | ∃ z ∈ E, x ⤳ z}ᶜ)
      (hGen : ∀ {x y : X}, x ⤳ y → y ∈ B → x ∈ B) : IsOpen B := by
    apply isOpen_of_isOpen_constructible _ hGen
    rw [hB]
    change IsOpen (WithTopology.ofTopology ⁻¹' {x : X | ∃ z ∈ E, x ⤳ z}ᶜ :
      Set (WithConstructibleTopology X))
    rw [Set.preimage_compl]
    apply (isClosed_constructible_of_specializes_to (C := E) _).isOpen_compl
    simpa only [Set.preimage_compl, compl_compl] using
      (isOpen_inPatch hE.isOpen_compl).isClosed_compl
  have Vopen : IsOpen V := hopen V D hD hc (fun h ⟨z, hz, hyz⟩ => ⟨z, hz, h.trans hyz⟩)
  have Wopen : IsOpen W := hopen W C hC hd (fun h ⟨z, hz, hyz⟩ => ⟨z, hz, h.trans hyz⟩)
  refine ⟨V, ⟨isOpen_compl_iff.mp (hd ▸ Wopen), Vopen⟩, Set.ext fun z => ?_⟩
  refine ⟨fun hz => ?_, fun hz => ⟨i z, ⟨z, hz, rfl⟩, specializes_rfl⟩⟩
  by_contra hn
  exact (hV (i z)).mp hz ⟨i z, ⟨z, hn, rfl⟩, specializes_rfl⟩

/-- Restriction of continuous functions with discrete values is bijective
under the same connectedness condition on point closures. -/
theorem bijective_restrictContinuous {X Z M : Type u} [TopologicalSpace X]
    [SpectralSpace X] [TopologicalSpace Z] [TopologicalSpace M] [DiscreteTopology M]
    {i : Z → X} (hi : IsClosedEmbedding i)
    (hConn : ∀ x : X, IsConnected (Set.range i ∩ closure ({x} : Set X))) :
    Function.Bijective (fun s : C(X, M) => s.comp ⟨i, hi.continuous⟩) := by
  classical
  have hCenter (x : X) : ∃ z : Z, x ⤳ i z := by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := (hConn x).1
    exact ⟨z, specializes_iff_mem_closure.mpr hz⟩
  choose z hz using hCenter
  have hValue (s : C(X, M)) (x : X) : s x = s (i (z x)) :=
    (hz x).mem_open ((isOpen_discrete {s (i (z x))}).preimage s.continuous) rfl
  constructor
  · intro s t h
    apply ContinuousMap.ext
    intro x
    exact (hValue s x).trans ((congrArg (fun f : C(Z, M) => f (z x)) h).trans (hValue t x).symm)
  · intro s
    have hf (m : M) : IsClopen (s ⁻¹' {m}) :=
      ⟨(isClosed_discrete {m}).preimage s.continuous, (isOpen_discrete {m}).preimage s.continuous⟩
    choose V hV hVbase using fun m => exists_clopen_of_closedEmbedding hi hConn (hf m)
    let t (x : X) := s (z x)
    have ht (m : M) : t ⁻¹' {m} = V m := by
      ext x
      have hFiber : i (z x) ∈ V m ↔ t x = m := by
        change z x ∈ i ⁻¹' V m ↔ _
        rw [hVbase]
        rfl
      exact ⟨fun h => (hz x).mem_open (hV m).2 (hFiber.mpr h),
        fun h => hFiber.mp (by
          by_contra hn
          exact ((hz x).mem_open (hV m).1.isOpen_compl hn) h)⟩
    have hCont : Continuous t := by
      rw [continuous_def]
      intro U _
      have hU : t ⁻¹' U = ⋃ m : U, V m.val := by
        ext x
        simp only [Set.mem_preimage, Set.mem_iUnion]
        refine ⟨fun hx => ⟨⟨t x, hx⟩, ht (t x) ▸ rfl⟩, ?_⟩
        rintro ⟨m, hm⟩
        have hm' : x ∈ t ⁻¹' {m.val} := by rw [ht]; exact hm
        exact (show t x = m.val from hm').symm ▸ m.property
      rw [hU]
      exact isOpen_iUnion fun m => (hV m.val).2
    refine ⟨⟨t, hCont⟩, ContinuousMap.ext fun x => ?_⟩
    have hx : i x ∈ V (s x) := by
      change x ∈ i ⁻¹' V (s x)
      rw [hVbase]
      rfl
    change i x ∈ t ⁻¹' {s x}
    rw [ht]
    exact hx

end PhilipponSpectralClosedClopens

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso globalSectionsIso_hom_app_eq_map pullbackConstantIso)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedFiberCovers (closedFiber_inter_closure_nonempty)
open PhilipponEtaleClosedFiberSections (closedFiberι range_closedFiberι closedFiber_inter_closure_preconnected)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso homEquiv_constantSheafIso_apply)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponSpectralClosedClopens (bijective_restrictContinuous)


namespace PhilipponEtaleConstantRestriction

universe u

private abbrev terminal (X : Scheme.{u}) := Scheme.Etale.mk (𝟙 X)

private def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

variable {X Y : Scheme.{u}} (j : Y ⟶ X)
variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

private abbrev constant (V : Scheme.{u}) :=
  (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)

/-- The pullback unit on the constant sheaf is restriction of continuous
coefficient functions along the projection of each base-changed chart. -/
theorem unit_comp_comparison :
    (pullbackAdjunction j).unit.app (constant M X) ≫
      (pushforward j).map (((pullbackConstantIso j).app (AddCommGrpCat.of M)).hom ≫
        (constantSheafIso Y M).hom) = (constantSheafIso X M).hom ≫ restriction M j := by
  let K := AddCommGrpCat.of M
  let e := (pullbackConstantIso j).app K
  let a := pullbackAdjunction j
  let cX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} (isTerminal X)
  let cY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} (isTerminal Y)
  let c := Adjunction.ofNatIsoRight (cX.comp a) (globalSectionsIso j)
  let q := e.hom ≫ (constantSheafIso Y M).hom
  let r := (constantSheafIso X M).hom ≫ restriction M j
  let G := continuousSheaf Y M
  let s := (globalSectionsIso j).hom.app G
  have he : c.homEquiv K (constant M Y) e.hom = cY.unit.app K :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app c cY K
  have hq : cX.homEquiv K ((pushforward j).obj G) (a.homEquiv _ _ q) ≫ s =
      cY.homEquiv K G (constantSheafIso Y M).hom := by
    calc
      _ = c.homEquiv K G q := by
        dsimp only [c, s]
        rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
        rfl
      _ = _ := by
        dsimp only [q]
        rw [Adjunction.homEquiv_naturality_right, he, Adjunction.homEquiv_unit]
  have hr : cX.homEquiv K ((pushforward j).obj G) r ≫ s =
      cY.homEquiv K G (constantSheafIso Y M).hom := by
    let l : terminal Y ⟶ (baseChange j).obj (terminal X) :=
      MorphismProperty.Over.homMk (pullback.lift j (𝟙 Y) ((Category.comp_id j).trans (Category.id_comp j).symm))
        (pullback.lift_snd ..) trivial
    have hs : s = G.obj.map l.op := globalSectionsIso_hom_app_eq_map j G l
    dsimp only [r]
    rw [Adjunction.homEquiv_naturality_right, hs]
    apply ConcreteCategory.hom_ext
    intro m
    change G.obj.map l.op (((restriction M j).hom.app (op (terminal X)))
      (cX.homEquiv K (continuousSheaf X M) (constantSheafIso X M).hom m)) =
        cY.homEquiv K G (constantSheafIso Y M).hom m
    rw [homEquiv_constantSheafIso_apply X M (isTerminal X),
      homEquiv_constantSheafIso_apply Y M (isTerminal Y)]
    apply ContinuousMap.ext
    intro y
    rfl
  calc
    _ = a.homEquiv (constant M X) G q := rfl
    _ = r := (cX.homEquiv K ((pushforward j).obj G)).injective ((cancel_mono s).mp (hq.trans hr.symm))

/-- On a finite étale chart of a proper scheme, constant coefficient
sections are determined by their values on the closed fiber and all such
values extend, provided the proper closed-fiber connectedness criterion. -/
theorem unit_app_bijective {A : Type u} [CommRing A] [IsLocalRing A]
    (g : X ⟶ Spec (.of A)) [IsProper g]
    (s : Y ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (hConn : ∀ {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
      [IsProper f] [PreconnectedSpace V], _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint A}))
    (U : X.Etale) [IsFinite U.hom] :
    Function.Bijective (((pullbackAdjunction j).unit.app (constant M X)).hom.app (op U)) := by
  let f := U.hom ≫ g
  let p := pullback.fst U.hom j
  let : IsProper f := inferInstanceAs (IsProper (U.hom ≫ g))
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let : IsClosedImmersion j := MorphismProperty.of_isPullback h inferInstance
  let : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst U.hom j))
  let : SpectralSpace ↥((𝟭 Scheme).obj U.left) := {
    toCompactSpace := (quasiCompact_iff_compactSpace f).mp inferInstance
    toQuasiSeparatedSpace := quasiSeparatedSpace_of_quasiSeparated f }
  have hU := ((IsPullback.of_hasPullback U.hom j).paste_vert h.flip).flip
  have hp : hU.isoPullback.hom ≫ closedFiberι f = p := hU.isoPullback_hom_snd
  have hrange : Set.range p = f ⁻¹' {IsLocalRing.closedPoint A} := by
    rw [← hp, ← range_closedFiberι f]
    change Set.range (closedFiberι f ∘ hU.isoPullback.hom) = _
    rw [Set.range_comp, hU.isoPullback.hom.surjective.range_eq, Set.image_univ]
  have hr : Function.Bijective ((restriction M j).hom.app (op U)) := by
    change Function.Bijective (fun t : C(U.left, M) => t.comp ⟨p, p.continuous⟩)
    exact bijective_restrictContinuous p.isClosedEmbedding (fun x => by
      rw [hrange]
      exact ⟨closedFiber_inter_closure_nonempty f x, closedFiber_inter_closure_preconnected f hConn x⟩)
  let ev := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op U)
  let q := (pullbackConstantIso j).app (AddCommGrpCat.of M) ≪≫ constantSheafIso Y M
  let e₁ := ev.mapIso (constantSheafIso X M)
  let e₂ := ev.mapIso ((pushforward j).mapIso q)
  let a := ((pullbackAdjunction j).unit.app (constant M X)).hom.app (op U)
  have he : a ≫ e₂.hom = e₁.hom ≫ (restriction M j).hom.app (op U) :=
    congrArg (fun k => k.hom.app (op U)) (unit_comp_comparison j M)
  apply ((ConcreteCategory.bijective_of_isIso e₂.hom).of_comp_iff' a).mp
  change Function.Bijective (a ≫ e₂.hom)
  rw [he]
  exact hr.comp (ConcreteCategory.bijective_of_isIso e₁.hom)

end PhilipponEtaleConstantRestriction

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
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedFiberCovers (eq_univ_of_contains_closedFiber)
open PhilipponEtaleClosedFiberSections (closedFiberι range_closedFiberι)


namespace PhilipponFiniteEtaleClosedFiberConservative

universe u

/-- A surjective restriction to the closed fiber forces an étale map over
a proper scheme over a local ring to be surjective. -/
theorem surjective_of_closedFiber {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]
    (f : Y ⟶ X) [Etale f] [Surjective (pullback.snd f (closedFiberι g))] :
    Surjective f := by
  have hClosed : g ⁻¹' {IsLocalRing.closedPoint A} ⊆ Set.range f := by
    rw [← range_closedFiberι g]
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Set.range (pullback.snd f (closedFiberι g)) :=
      (inferInstance : Surjective (pullback.snd f (closedFiberι g))).surj y
    rwa [Scheme.Pullback.range_snd] at hy
  exact ⟨Set.range_eq_univ.mp (eq_univ_of_contains_closedFiber g f.isOpenMap.isOpen_range hClosed)⟩

/-- A finite étale morphism over a proper scheme over a local base is an
isomorphism if its restriction to the closed fiber is an isomorphism. -/
theorem isIso_of_closedFiber {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]
    (f : Y ⟶ X) [IsFinite f] [Etale f] [IsIso (pullback.snd f (closedFiberι g))] :
    IsIso f := by
  let V : Set X := {x | f.finrank x = 1}
  have hV : IsOpen V := f.isLocallyConstant_finrank.isOpen_fiber 1
  have hFiber : g ⁻¹' {IsLocalRing.closedPoint A} ⊆ V := by
    rw [← range_closedFiberι g]
    rintro _ ⟨y, rfl⟩
    change f.finrank (closedFiberι g y) = 1
    rw [← f.finrank_pullback_snd (closedFiberι g), Scheme.Hom.finrank_eq_one_of_isIso]
    rfl
  apply (f.isIso_iff_finrank_eq).mpr
  funext x
  exact Set.eq_univ_iff_forall.mp (eq_univ_of_contains_closedFiber g hV hFiber) x

/-- Two maps to an étale scheme over a common base agree if they agree over
the closed fiber of their proper source. -/
theorem eq_of_comp_closedFiber {A : Type u} [CommRing A] [IsLocalRing A]
    {U V X : Scheme.{u}} (g : U ⟶ Spec (.of A)) [IsProper g]
    (q : V ⟶ X) [Etale q] {a b : U ⟶ V} (h : a ≫ q = b ≫ q)
    (hFiber : closedFiberι g ≫ a = closedFiberι g ≫ b) : a = b := by
  let d := pullback.diagonal q
  let k : U ⟶ pullback q q := pullback.lift a b h
  let V₀ := k ⁻¹' Set.range d
  have hV : IsOpen V₀ := d.isOpenMap.isOpen_range.preimage k.continuous
  have hk : closedFiberι g ≫ k = (closedFiberι g ≫ a) ≫ d := by
    have ha' : k ≫ pullback.fst q q = a := pullback.lift_fst ..
    have hb' : k ≫ pullback.snd q q = b := pullback.lift_snd ..
    apply pullback.hom_ext
    · rw [Category.assoc, ha']
      simp [d, Category.assoc]
    · rw [Category.assoc, hb']
      simpa [d, Category.assoc] using hFiber.symm
  have hClosed : g ⁻¹' {IsLocalRing.closedPoint A} ⊆ V₀ := by
    rw [← range_closedFiberι g]
    rintro _ ⟨x, rfl⟩
    exact ⟨(closedFiberι g ≫ a) x,
      (congrArg (fun m : _ ⟶ pullback q q => m x) hk).symm⟩
  have hCover := eq_univ_of_contains_closedFiber g hV hClosed
  have hRange : Set.range k ⊆ Set.range d := by
    rintro _ ⟨x, rfl⟩
    exact Set.eq_univ_iff_forall.mp hCover x
  let l := IsOpenImmersion.lift d k hRange
  have hl : l ≫ d = k := IsOpenImmersion.lift_fac _ _ _
  calc
    a = k ≫ pullback.fst q q := (pullback.lift_fst ..).symm
    _ = l := by rw [← hl, Category.assoc]; simp [d]
    _ = k ≫ pullback.snd q q := by rw [← hl, Category.assoc]; simp [d]
    _ = b := pullback.lift_snd ..

end PhilipponFiniteEtaleClosedFiberConservative

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedFiberCovers (closedFiber_inter_closure_nonempty)
open PhilipponEtaleClosedFiberSections (closedFiberι range_closedFiberι closedFiber_inter_closure_preconnected)
open PhilipponFiniteEtaleClosedFiberConservative (isIso_of_closedFiber)
open PhilipponSpectralClosedClopens (exists_clopen_of_closedEmbedding)


namespace PhilipponFiniteEtaleClosedFiberSections

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- If proper preconnected schemes have preconnected closed fibers, a
section of a finite étale map over the closed fiber extends to the base. -/
theorem exists_section_of_closedFiber {X V : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]
    (p : V ⟶ X) [IsFinite p] [Etale p]
    (hConn : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
      [IsProper f] [PreconnectedSpace Y], _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint A}))
    (s : pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g ⟶
      pullback p (closedFiberι g)) (hs : s ≫ pullback.snd p (closedFiberι g) = 𝟙 _) :
    ∃ a : X ⟶ V, a ≫ p = 𝟙 X ∧ closedFiberι g ≫ a = s ≫ pullback.fst p (closedFiberι g) := by
  let i := closedFiberι g
  let j := pullback.fst p i
  let r := pullback.snd p i
  have hs' : s ≫ r = 𝟙 _ := hs
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.snd _ g))
  let : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (pullback.fst p i))
  let : IsFinite r := inferInstanceAs (IsFinite (pullback.snd p i))
  let : Etale r := inferInstanceAs (Etale (pullback.snd p i))
  let : IsIso (s ≫ r) := by rw [hs']; infer_instance
  let : Mono s := mono_of_mono_fac hs'
  let : Etale s := Etale.of_comp s r
  let : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
  let : IsFinite s := IsFinite.of_comp s r
  let f := p ≫ g
  let : IsProper f := inferInstanceAs (IsProper (p ≫ g))
  let : SpectralSpace V := {
    toCompactSpace := (quasiCompact_iff_compactSpace f).mp inferInstance
    toQuasiSeparatedSpace := quasiSeparatedSpace_of_quasiSeparated f }
  have hj : Set.range j = f ⁻¹' {IsLocalRing.closedPoint A} := by
    change Set.range (pullback.fst p i) = f ⁻¹' _
    rw [Scheme.Pullback.range_fst, range_closedFiberι g]
    rfl
  obtain ⟨W, hW, hWbase⟩ := exists_clopen_of_closedEmbedding j.isClosedEmbedding
    (fun v => by
      rw [hj]
      exact ⟨closedFiber_inter_closure_nonempty f v, closedFiber_inter_closure_preconnected f hConn v⟩)
    (U := Set.range s) ⟨s.isClosedMap.isClosed_range, s.isOpenMap.isOpen_range⟩
  let U : V.Opens := ⟨W, hW.2⟩
  let q := U.ι ≫ p
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by simpa [U] using hW.1)
  let : Etale q := inferInstanceAs (Etale (U.ι ≫ p))
  let : IsFinite q := inferInstanceAs (IsFinite (U.ι ≫ p))
  let k := pullback.fst U.ι j
  let l := pullback.snd U.ι j
  let : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (pullback.snd U.ι j))
  have hl : Set.range l = Set.range s := by
    change Set.range (pullback.snd U.ι j) = _
    rw [Scheme.Pullback.range_snd]
    simpa [U] using hWbase
  let t := IsOpenImmersion.lift s l hl.le
  let u := IsOpenImmersion.lift l s hl.ge
  have ht : t ≫ s = l := IsOpenImmersion.lift_fac ..
  have hu : u ≫ l = s := IsOpenImmersion.lift_fac ..
  have htr : l ≫ r = t := by rw [← ht, Category.assoc, hs', Category.comp_id]
  let : IsIso (l ≫ r) := by
    rw [htr]
    refine ⟨⟨u, ?_, ?_⟩⟩
    · apply (cancel_mono l).1
      rw [Category.assoc, hu, ht, Category.id_comp]
    · apply (cancel_mono s).1
      rw [Category.assoc, ht, hu, Category.id_comp]
  have hp : IsPullback k (l ≫ r) q i :=
    ((IsPullback.of_hasPullback U.ι j).flip.paste_horiz (IsPullback.of_hasPullback p i).flip).flip
  let : IsIso (pullback.snd q i) := by
    rw [← isIso_comp_left_iff hp.isoPullback.hom, hp.isoPullback_hom_snd]
    infer_instance
  let : IsIso q := isIso_of_closedFiber g q
  refine ⟨inv q ≫ U.ι, by simp [q, Category.assoc], ?_⟩
  have hunit : u ≫ l ≫ r = 𝟙 _ := by rw [← Category.assoc, hu, hs']
  have hek : u ≫ k = i ≫ inv q := by
    apply (cancel_mono q).1
    rw [Category.assoc, hp.w, ← Category.assoc, hunit, Category.id_comp,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← hek, Category.assoc, pullback.condition (f := U.ι) (g := j),
    ← Category.assoc, hu]

/-- An over-base map from the closed fiber of a proper scheme to a finite
étale target extends uniquely over the proper scheme. -/
theorem existsUnique_map_of_closedFiber {U V X : Scheme.{u}} (g : U ⟶ Spec (.of A)) [IsProper g]
    (p : U ⟶ X) (q : V ⟶ X) [IsFinite q] [Etale q]
    (hConn : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
      [IsProper f] [PreconnectedSpace Y], _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint A}))
    (b : pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g ⟶ V)
    (hb : b ≫ q = closedFiberι g ≫ p) :
    ∃! a : U ⟶ V, a ≫ q = p ∧ closedFiberι g ≫ a = b := by
  let i := closedFiberι g
  let r := pullback.fst p q
  let t := pullback.snd p q
  let : IsFinite r := inferInstanceAs (IsFinite (pullback.fst p q))
  let : Etale r := inferInstanceAs (Etale (pullback.fst p q))
  let d := pullback.lift i b hb.symm
  have hdr : d ≫ r = i := pullback.lift_fst ..
  have hdt : d ≫ t = b := pullback.lift_snd ..
  let s := pullback.lift d (𝟙 _) (hdr.trans (Category.id_comp i).symm)
  have hs : s ≫ pullback.snd r i = 𝟙 _ := pullback.lift_snd ..
  obtain ⟨l, hl, hli⟩ := exists_section_of_closedFiber g r hConn s hs
  have hst : s ≫ pullback.fst r i = d := pullback.lift_fst ..
  have htq : t ≫ q = r ≫ p := pullback.condition.symm
  have h₁ : (l ≫ t) ≫ q = p := by
    rw [Category.assoc, htq, ← Category.assoc, hl, Category.id_comp]
  have h₂ : i ≫ l ≫ t = b := by rw [← Category.assoc, hli, hst, hdt]
  refine ⟨l ≫ t, ⟨h₁, h₂⟩, ?_⟩
  intro a ha
  exact PhilipponFiniteEtaleClosedFiberConservative.eq_of_comp_closedFiber g q
    (ha.1.trans h₁.symm) (ha.2.trans h₂.symm)

end PhilipponFiniteEtaleClosedFiberSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedFiberSections (closedFiberι)
open PhilipponFiniteEtaleClosedFiberConservative (eq_of_comp_closedFiber)
open PhilipponFiniteEtaleClosedFiberSections (existsUnique_map_of_closedFiber)


namespace PhilipponFiniteEtaleClosedFiberMaps

universe u

/-- On finite étale charts, restriction to the closed fiber is fully faithful
when proper preconnected schemes have preconnected closed fibers. -/
theorem bijective_map {A : Type u} [CommRing A] [IsLocalRing A] {X T : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g]
    (j : T ⟶ X) (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (hConn : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
      [IsProper f] [PreconnectedSpace Y], _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint A}))
    (U V : X.Etale) [IsFinite U.hom] [IsFinite V.hom] :
    Function.Bijective ((baseChange j).map : (U ⟶ V) → _) := by
  let f := U.hom ≫ g
  let : IsProper f := inferInstanceAs (IsProper (U.hom ≫ g))
  let k := pullback.fst U.hom j
  let l := pullback.fst V.hom j
  have hU := ((IsPullback.of_hasPullback U.hom j).paste_vert h.flip).flip
  let e := hU.isoPullback
  have heh : e.hom ≫ closedFiberι f = k := hU.isoPullback_hom_snd
  have hek : e.inv ≫ k = closedFiberι f := by
    rw [← heh, Iso.inv_hom_id_assoc]
  have hmap (a : U ⟶ V) : k ≫ a.left = ((baseChange j).map a).left ≫ l :=
    (map_isPullback j a).w
  constructor
  · intro a b hab
    have hLeft (a : U ⟶ V) : closedFiberι f ≫ a.left = e.inv ≫ ((baseChange j).map a).left ≫ l :=
      calc
        _ = e.inv ≫ (k ≫ a.left) := by rw [← Category.assoc, hek]
        _ = _ := congrArg (fun t => e.inv ≫ t) (hmap a)
    have he := congrArg (fun t => e.inv ≫ t.left ≫ l) hab
    apply MorphismProperty.Over.Hom.ext
    exact eq_of_comp_closedFiber f V.hom
      ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
      ((hLeft a).trans (he.trans (hLeft b).symm))
  · intro b
    let c := e.inv ≫ b.left ≫ l
    have hc : c ≫ V.hom = closedFiberι f ≫ U.hom := by
      have hb := MorphismProperty.Over.w b
      change b.left ≫ pullback.snd V.hom j = pullback.snd U.hom j at hb
      have hl : l ≫ V.hom = pullback.snd V.hom j ≫ j := pullback.condition
      have hk : k ≫ U.hom = pullback.snd U.hom j ≫ j := pullback.condition
      calc
        c ≫ V.hom = e.inv ≫ b.left ≫ (l ≫ V.hom) := by simp only [c, Category.assoc]
        _ = e.inv ≫ (b.left ≫ pullback.snd V.hom j) ≫ j := by rw [hl, Category.assoc]
        _ = e.inv ≫ k ≫ U.hom := by rw [hb, hk]
        _ = _ := by rw [← Category.assoc, hek]
    obtain ⟨a, ha, _⟩ := existsUnique_map_of_closedFiber f U.hom V.hom hConn c hc
    let a' : U ⟶ V := MorphismProperty.Over.homMk a ha.1 trivial
    refine ⟨a', MorphismProperty.Over.Hom.ext ?_⟩
    apply pullback.hom_ext
    · have hki : e.inv ≫ (k ≫ a) = e.inv ≫ b.left ≫ l := by
        rw [← Category.assoc, hek]
        exact ha.2
      exact (hmap a').symm.trans ((cancel_epi e.inv).mp hki)
    · exact (MorphismProperty.Over.w ((baseChange j).map a')).trans
        (MorphismProperty.Over.w b).symm

end PhilipponFiniteEtaleClosedFiberMaps

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers (Torsor)
open PhilipponTorsorInvariantDescent (presence)


namespace PhilipponTorsorRepresentableLift

universe u v w

variable {C : Type u} {E : Type v} [Category.{w} C] [Category.{w} E]
variable {J : GrothendieckTopology C} {L : GrothendieckTopology E}
variable {G : Sheaf J AddCommGrpCat.{w}} {H : Sheaf L AddCommGrpCat.{w}}

private def sectionsMap (F : C ⥤ E) {W : C} {B : Torsor H}
    (e : yoneda.obj (F.obj W) ≅ B.D.P) : yoneda.obj W ⟶ F.op ⋙ B.D.P where
  app U := ↾fun q => e.hom.app (op (F.obj U.unop)) (F.map q)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro q
    change e.hom.app (op (F.obj V.unop)) (F.map (f.unop ≫ q)) =
      B.D.P.map (F.map f.unop).op (e.hom.app (op (F.obj U.unop)) (F.map q))
    rw [F.map_comp]
    exact NatTrans.naturality_apply e.hom (F.map f.unop).op (F.map q)

/-- A lift of the scheme representing a torsor acquires the torsor operations
by lifting the universal difference and the universal translation. -/
theorem exists_torsor_of_representable [HasBinaryProducts C]
    (F : C ⥤ E) (α : G.obj ⟶ F.op ⋙ H.obj) {B : Torsor H} (W K : C)
    (e : yoneda.obj (F.obj W) ≅ B.D.P) (c : yoneda.obj K ≅ G.obj ⋙ forget AddCommGrpCat.{w})
    (hSheaf : Presheaf.IsSheaf J (yoneda.obj W))
    (hPresence : ∀ U, presence (yoneda.obj W) U ∈ J U)
    (h₂ : Function.Surjective (α.app (op (W ⨯ W))))
    (h₃ : Function.Injective (α.app (op (W ⨯ (W ⨯ W)))))
    (hK : Function.Injective (α.app (op (K ⨯ W))))
    (hMaps : Function.Injective (F.map : (W ⨯ W ⟶ W) → _))
    (hTranslate : Function.Surjective (F.map : (K ⨯ W ⟶ W) → _)) :
    ∃ (D : Torsor G) (d : D.D.P ⟶ F.op ⋙ B.D.P), ∀ U x y,
      B.D.diff (F.op.obj U) (d.app U x) (d.app U y) = α.app U (D.D.diff U x y) := by
  let P := yoneda.obj W
  let d := sectionsMap F e
  let mapped {U : C} (x : U ⟶ W) := d.app (op U) x
  have mapped_comp {U V : C} (g : U ⟶ V) (x : V ⟶ W) :
      mapped (g ≫ x) = B.D.P.map (F.map g).op (mapped x) :=
    NatTrans.naturality_apply d g.op x
  have α_map {U V : C} (g : U ⟶ V) (a : G.obj.obj (op V)) :
      α.app (op U) (G.obj.map g.op a) = H.obj.map (F.map g).op (α.app (op V) a) :=
    NatTrans.naturality_apply α g.op a
  obtain ⟨v, hv⟩ := h₂ (B.D.diff (op (F.obj (W ⨯ W))) (mapped prod.fst) (mapped prod.snd))
  let δ {U : C} (x y : U ⟶ W) := G.obj.map (prod.lift x y).op v
  have δ_map {U V : C} (g : U ⟶ V) (x y : V ⟶ W) :
      G.obj.map g.op (δ x y) = δ (g ≫ x) (g ≫ y) := by
    dsimp only [δ]
    rw [← Functor.map_comp_apply, ← op_comp, prod.comp_lift]
  have δ_eq {U : C} (x y : U ⟶ W) :
      α.app (op U) (δ x y) = B.D.diff (op (F.obj U)) (mapped x) (mapped y) := by
    have hx := (mapped_comp (prod.lift x y) (prod.fst : W ⨯ W ⟶ W)).symm
    have hy := (mapped_comp (prod.lift x y) (prod.snd : W ⨯ W ⟶ W)).symm
    rw [prod.lift_fst] at hx
    rw [prod.lift_snd] at hy
    dsimp only [δ]
    rw [α_map, hv, B.D.map_diff]
    exact congrArg₂ (B.D.diff (op (F.obj U))) hx hy
  have δ_add {U : C} (x y z : U ⟶ W) : δ x y + δ y z = δ x z := by
    let a : W ⨯ (W ⨯ W) ⟶ W := prod.fst
    let b : W ⨯ (W ⨯ W) ⟶ W := prod.snd ≫ prod.fst
    let c' : W ⨯ (W ⨯ W) ⟶ W := prod.snd ≫ prod.snd
    have h : δ a b + δ b c' = δ a c' := by
      apply h₃
      rw [map_add, δ_eq, δ_eq, δ_eq]
      exact B.D.diff_add_diff _ _ _ _
    have h' := congrArg (G.obj.map (prod.lift x (prod.lift y z)).op) h
    simpa only [map_add, δ_map, a, b, c', prod.lift_fst, prod.lift_snd, prod.lift_snd_assoc] using h'
  let a₀ : G.obj.obj (op (K ⨯ W)) := c.hom.app _ prod.fst
  let y₀ : K ⨯ W ⟶ W := prod.snd
  obtain ⟨b₀, hb₀⟩ := (B.diff_bijective _ (mapped y₀)).2 (α.app (op (K ⨯ W)) a₀)
  change B.D.diff (op (F.obj (K ⨯ W))) b₀ (mapped y₀) = α.app (op (K ⨯ W)) a₀ at hb₀
  obtain ⟨k, hk⟩ := hTranslate (e.inv.app (op (F.obj (K ⨯ W))) b₀)
  have hk' : mapped k = b₀ := by
    change e.hom.app (op (F.obj (K ⨯ W))) (F.map k) = _
    rw [hk]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app (op (F.obj (K ⨯ W)))) b₀
  let pair {U : C} (a : G.obj.obj (op U)) (y : U ⟶ W) : U ⟶ K ⨯ W :=
    prod.lift (c.inv.app (op U) a) y
  let τ {U : C} (a : G.obj.obj (op U)) (y : U ⟶ W) := pair a y ≫ k
  have pair_fst {U : C} (a : G.obj.obj (op U)) (y : U ⟶ W) :
      G.obj.map (pair a y).op a₀ = a := by
    have h := (NatTrans.naturality_apply c.hom (pair a y).op (prod.fst : K ⨯ W ⟶ K)).symm
    change G.obj.map (pair a y).op a₀ = c.hom.app (op U) (pair a y ≫ prod.fst) at h
    rw [h]
    dsimp only [pair]
    rw [prod.lift_fst]
    exact ConcreteCategory.congr_hom (c.inv_hom_id_app (op U)) a
  have τ_map {U V : C} (g : U ⟶ V) (a : G.obj.obj (op V)) (y : V ⟶ W) :
      g ≫ τ a y = τ (G.obj.map g.op a) (g ≫ y) := by
    have h := (NatTrans.naturality_apply c.inv g.op a).symm
    change g ≫ c.inv.app (op V) a = c.inv.app (op U) (G.obj.map g.op a) at h
    dsimp only [τ, pair]
    rw [← Category.assoc, prod.comp_lift, h]
  have τ_eq {U : C} (a : G.obj.obj (op U)) (y : U ⟶ W) :
      B.D.diff (op (F.obj U)) (mapped (τ a y)) (mapped y) = α.app (op U) a := by
    have h := congrArg (H.obj.map (F.map (pair a y)).op) hb₀
    have hys : pair a y ≫ y₀ = y := prod.lift_snd _ _
    rw [B.D.map_diff] at h
    have hx := (congrArg (B.D.P.map (F.map (pair a y)).op) hk'.symm).trans
      (mapped_comp (pair a y) k).symm
    have hy := (mapped_comp (pair a y) y₀).symm.trans (congrArg (fun t => mapped t) hys)
    have ha := (α_map (pair a y) a₀).symm.trans (congrArg (α.app (op U)) (pair_fst a y))
    exact (congrArg₂ (B.D.diff (op (F.obj U))) hx hy).symm.trans (h.trans ha)
  have right_inv {U : C} (a : G.obj.obj (op U)) (y : U ⟶ W) : δ (τ a y) y = a := by
    have h : δ (τ a₀ y₀) y₀ = a₀ := hK ((δ_eq _ _).trans (τ_eq _ _))
    have h' := congrArg (G.obj.map (pair a y).op) h
    have hys : pair a y ≫ y₀ = y := prod.lift_snd _ _
    simpa only [δ_map, τ_map, pair_fst, hys] using h'
  have left_inv {U : C} (x y : U ⟶ W) : τ (δ x y) y = x := by
    let x' : W ⨯ W ⟶ W := prod.fst
    let y' : W ⨯ W ⟶ W := prod.snd
    have h : τ (δ x' y') y' = x' := by
      apply hMaps
      apply (e.app _).toEquiv.injective
      apply (B.diff_bijective _ (mapped y')).1
      exact (τ_eq _ _).trans (δ_eq x' y')
    have h' := congrArg (fun t => prod.lift x y ≫ t) h
    simpa only [τ_map, δ_map, x', y', prod.lift_fst, prod.lift_snd] using h'
  let D : Torsor G := {
    D := {
      P := P
      diff := fun _ => δ
      diff_add_diff := fun _ => δ_add
      map_diff := fun f => δ_map f.unop }
    isSheaf := hSheaf
    locally_nonempty := hPresence
    diff_bijective := by
      intro U y
      change Function.Bijective (fun x : U.unop ⟶ W => δ x y)
      exact ⟨Function.LeftInverse.injective (g := fun a => τ a y) (fun x => left_inv x y),
        Function.RightInverse.surjective (g := fun a => τ a y) (fun a => right_inv a y)⟩ }
  exact ⟨D, d, fun _ x y => (δ_eq x y).symm⟩

end PhilipponTorsorRepresentableLift

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedFiberCovers (eq_univ_of_contains_closedFiber)
open PhilipponEtaleClosedFiberSections (closedFiberι range_closedFiberι)
open PhilipponEtaleConstantFiniteRepresentability (constantChart representsConstant isFinite_constantChart)
open PhilipponEtaleConstantRestriction (unit_app_bijective)
open PhilipponEtaleRepresentablePresence (isSheaf_yoneda presence_mem_of_surjective surjective_of_presence)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFiniteEtaleClosedFiberMaps (bijective_map)
open PhilipponTorsorRepresentableLift (exists_torsor_of_representable)
open PhilipponTorsorSectionFibers (Torsor)


namespace PhilipponEtaleTorsorFromCover

universe u

private theorem isFinite_prod {X : Scheme.{u}} (U V : X.Etale) [IsFinite U.hom] [IsFinite V.hom] :
    IsFinite (U ⨯ V).hom := by
  let F := Scheme.Etale.forget X
  let a : U ⨯ V ⟶ U := prod.fst
  let b : U ⨯ V ⟶ V := prod.snd
  have hl := mapIsLimitOfPreservesOfIsLimit F a b (prodIsProd U V)
  have hp : IsPullback a.left b.left U.hom V.hom := Over.isPullback_of_binaryFan_isLimit _ hl
  let : IsFinite a.left := MorphismProperty.of_isPullback hp.flip (inferInstance : IsFinite V.hom)
  rw [← MorphismProperty.Over.w a]
  infer_instance

private theorem surjective_of_baseChange {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g] (j : Y ⟶ X)
    (s : Y ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (W : X.Etale) [Surjective ((baseChange j).obj W).hom] : Surjective W.hom := by
  have hj : h.isoPullback.hom ≫ closedFiberι g = j := h.isoPullback_hom_snd
  have hr : Set.range j = g ⁻¹' {IsLocalRing.closedPoint A} := by
    rw [← hj, ← range_closedFiberι g]
    change Set.range (closedFiberι g ∘ h.isoPullback.hom) = _
    rw [Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]
  have hClosed : g ⁻¹' {IsLocalRing.closedPoint A} ⊆ Set.range W.hom := by
    rw [← hr]
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Set.range (pullback.snd W.hom j) :=
      (inferInstance : Surjective ((baseChange j).obj W).hom).surj y
    rwa [Scheme.Pullback.range_snd] at hy
  exact ⟨Set.range_eq_univ.mp (eq_univ_of_contains_closedFiber g W.hom.isOpenMap.isOpen_range hClosed)⟩

private abbrev K (M : Type u) [AddCommGroup M] (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)

/-- A finite étale lift of a representing scheme gives a lift of the
torsor with its difference map over the constant coefficient unit. -/
theorem exists_equivariant_lift_of_represented {A : Type u} [CommRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g] (j : Y ⟶ X)
    (s : Y ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (hConn : ∀ {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
      [IsProper f] [PreconnectedSpace V], _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint A}))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    (B : Torsor ((pullbackSheaves j).obj (K M X)))
    (W : X.Etale) [IsFinite W.hom] (e : yoneda.obj ((baseChange j).obj W) ≅ B.D.P) :
    ∃ (D : Torsor (K M X)) (d : D.D.P ⟶ (baseChange j).op ⋙ B.D.P), ∀ U x y,
      B.D.diff ((baseChange j).op.obj U) (d.app U x) (d.app U y) =
        ((pullbackAdjunction j).unit.app (K M X)).hom.app U (D.D.diff U x y) := by
  let R := constantChart X M
  let : IsFinite R.hom := isFinite_constantChart X M
  let : IsFinite (W ⨯ W).hom := isFinite_prod W W
  let : IsFinite (W ⨯ (W ⨯ W)).hom := isFinite_prod W (W ⨯ W)
  let : IsFinite (R ⨯ W).hom := isFinite_prod R W
  let : Surjective ((baseChange j).obj W).hom := surjective_of_presence e.symm (B.locally_nonempty _)
  let : Surjective W.hom := surjective_of_baseChange g j s h W
  let α := ((pullbackAdjunction j).unit.app (K M X)).hom
  have hUnit (U : X.Etale) [IsFinite U.hom] : Function.Bijective (α.app (op U)) :=
    unit_app_bijective j M g s h hConn U
  exact exists_torsor_of_representable (baseChange j) α W R e (representsConstant X M)
    (isSheaf_yoneda W) (fun U => presence_mem_of_surjective W U)
    (hUnit (W ⨯ W)).2 (hUnit (W ⨯ (W ⨯ W))).1
    (hUnit (R ⨯ W)).1 (bijective_map g j s h hConn (W ⨯ W) W).1 (bijective_map g j s h hConn (R ⨯ W) W).2

end PhilipponEtaleTorsorFromCover

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponSchemeIdempotents

universe u

/-- The characteristic section of a clopen subset is a global idempotent. -/
theorem exists_idempotent_of_clopen (X : Scheme.{u}) {s : Set X} (hs : IsClopen s) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x ∈ s, X.presheaf.Γgerm x e = 1) ∧
      (∀ x ∉ s, X.presheaf.Γgerm x e = 0) := by
  classical
  let U : Bool → X.Opens := fun i => if i then ⟨s, hs.2⟩ else ⟨sᶜ, hs.1.isOpen_compl⟩
  let a (i : Bool) : Γ(X, U i) := if i then 1 else 0
  let k (i : Bool) : U i ⟶ ⊤ := homOfLE le_top
  have hDisj : ∀ i j : Bool, i ≠ j → U i ⊓ U j = ⊥ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [U]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ s
    · exact ⟨true, by simpa [U] using hx⟩
    · exact ⟨false, by simpa [U] using hx⟩
  have hCompatible : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · exact (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (hDisj i j hij))).elim _ _
  obtain ⟨e, hRes, hUnique⟩ := X.sheaf.existsUnique_gluing' U ⊤ k hcover a hCompatible
  have hRes' (i : Bool) : (X.presheaf.map (k i).op).hom e = a i := hRes i
  have he : IsIdempotentElem e := by
    change e * e = e
    apply hUnique
    intro i
    let g := (X.presheaf.map (k i).op).hom
    calc
      g (e * e) = g e * g e := map_mul g e e
      _ = a i * a i := congrArg (fun z : Γ(X, U i) => z * z) (hRes' i)
      _ = a i := by cases i <;> simp [a]
  have hg (i : Bool) (x : X) (hx : x ∈ U i) :
      X.presheaf.Γgerm x e = X.presheaf.germ (U i) x hx (a i) := by
    rw [← hRes' i]
    exact (X.presheaf.germ_res_apply (k i) x hx e).symm
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ U true := by simpa [U] using hx
    simpa only [a, if_true, map_one] using hg true x hx'
  · intro x hx
    have hx' : x ∈ U false := by simpa [U] using hx
    simpa only [a, Bool.false_eq_true, if_false, map_zero] using hg false x hx'

/-- A scheme whose global functions have only trivial idempotents has
preconnected underlying space. -/
theorem preconnectedSpace_of_trivial_idempotents (X : Scheme.{u})
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.2
  intro s hs
  obtain ⟨e, he, h1, h0⟩ := exists_idempotent_of_clopen X hs
  rcases h e he with he₀ | he₁
  · left
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact zero_ne_one (by simpa only [he₀, map_zero] using h1 x hx)
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact one_ne_zero (by simpa only [he₁, map_one] using h0 x hx)

end PhilipponSchemeIdempotents

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponClosedFiberIdempotents

universe u

private theorem idempotent_of_scalar {K B : Type u} [Field K] [CommRing B] (g : K →+* B)
    (c : K) (hc : IsIdempotentElem (g c)) : g c = 0 ∨ g c = 1 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Or.inl (hB.elim _ _)
  have hi : c * c = c := g.injective (by rw [map_mul]; exact hc.eq)
  have hZero : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hi, sub_self]
  rcases mul_eq_zero.mp hZero with h | h
  · exact Or.inl (by rw [h, map_zero])
  · exact Or.inr (by rw [sub_eq_zero.mp h, map_one])

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R))

private abbrev residue := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
private abbrev Fiber := pullback (residue (R := R)) f
private abbrev inclusion : Fiber f ⟶ X := pullback.snd (residue (R := R)) f

/-- When a map to a local spectrum induces an isomorphism on global
functions, lifting idempotents suffices for closed-fiber connectedness. -/
theorem closedFiber_preconnected_of_idempotents_lift [IsIso f.appTop]
    (hLift : ∀ e : Γ(Fiber f, ⊤), IsIdempotentElem e →
      ∃ x : Γ(X, ⊤), (inclusion f).appTop.hom x = e) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  let K := IsLocalRing.ResidueField R
  let i := inclusion f
  let q : Fiber f ⟶ Spec (.of K) := pullback.fst (residue (R := R)) f
  let r := residue (R := R)
  let eK := Scheme.ΓSpecIso (CommRingCat.of K)
  let scalar : K →+* Γ(Fiber f, ⊤) := q.appTop.hom.comp eK.inv.hom
  have hComp : f.appTop ≫ i.appTop = r.appTop ≫ q.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    exact congrArg Scheme.Hom.appTop (pullback.condition (f := r) (g := f)).symm
  let : PreconnectedSpace (Fiber f) := by
    apply PhilipponSchemeIdempotents.preconnectedSpace_of_trivial_idempotents
    intro e he
    obtain ⟨x, hx⟩ := hLift e he
    let b := (inv f.appTop).hom x
    let c := eK.hom.hom (r.appTop.hom b)
    have hb : f.appTop.hom b = x := ConcreteCategory.congr_hom (IsIso.inv_hom_id f.appTop) x
    have hc : scalar c = e := by
      change q.appTop.hom (eK.inv.hom (eK.hom.hom (r.appTop.hom b))) = e
      calc
        _ = q.appTop.hom (r.appTop.hom b) :=
          congrArg q.appTop.hom (ConcreteCategory.congr_hom eK.hom_inv_id (r.appTop.hom b))
        _ = i.appTop.hom (f.appTop.hom b) := (ConcreteCategory.congr_hom hComp b).symm
        _ = e := by rw [hb]; exact hx
    rw [← hc]
    exact idempotent_of_scalar scalar c (hc.symm ▸ he)
  rw [← PhilipponEtaleClosedFiberSections.range_closedFiberι f]
  exact isPreconnected_range i.continuous

end PhilipponClosedFiberIdempotents

end

section

set_option autoImplicit false

namespace PhilipponHenselianIntegralConnectedness

universe u

private theorem trivial_idempotents {B : Type u} [CommRing B]
    [PreconnectedSpace (PrimeSpectrum B)] (e : B) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  let φ := PrimeSpectrum.isIdempotentElemEquivClopens (R := B)
  let V := φ ⟨e, he⟩
  rcases preconnectedSpace_iff_clopen.mp inferInstance (V : Set (PrimeSpectrum B)) V.isClopen with h | h
  · have hb : V = ⊥ := SetLike.coe_injective h
    have hx := congrArg (fun C => (φ.symm C).val) hb
    left
    simpa only [V, φ, OrderIso.symm_apply_apply, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] using hx
  · have ht : V = ⊤ := SetLike.coe_injective h
    have hx := congrArg (fun C => (φ.symm C).val) ht
    right
    simpa only [V, φ, OrderIso.symm_apply_apply, PrimeSpectrum.isIdempotentElemEquivClopens_symm_top] using hx

private theorem local_of_components {A : Type u} [CommRing A] [Nontrivial A]
    [Fintype (MaximalSpectrum A)] (e : MaximalSpectrum A → A)
    (he : CompleteOrthogonalIdempotents e)
    (hLocal : ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i}))
    (hTrivial : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1) : IsLocalRing A := by
  have hOne (i : MaximalSpectrum A) : e i = 1 := (hTrivial (e i) (he.idem i)).resolve_left (by
    intro h
    have hTop : Ideal.span {1 - e i} = ⊤ := by rw [h, sub_zero, Ideal.span_singleton_one]
    have hNontrivial : Nontrivial (A ⧸ Ideal.span {1 - e i}) := (hLocal i).toNontrivial
    exact (Ideal.Quotient.nontrivial_iff.mp hNontrivial) hTop)
  let : Subsingleton (MaximalSpectrum A) :=
    ⟨fun i j => Classical.byContradiction fun h =>
      one_ne_zero (by simpa only [hOne i, hOne j, one_mul] using he.ortho h)⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- A nonzero integral algebra with preconnected spectrum over a base
whose finite algebras split into local factors is local. -/
theorem isLocalRing_of_integral_of_preconnected
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] [Nontrivial B] [PreconnectedSpace (PrimeSpectrum B)]
    (decompose : ∀ (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A],
      ∃ (_ : Fintype (MaximalSpectrum A)) (e : MaximalSpectrum A → A),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) :
    IsLocalRing B := by
  let : Subsingleton (MaximalSpectrum B) := ⟨fun m n => by
    apply MaximalSpectrum.ext
    apply SetLike.ext
    intro b
    let A := Algebra.adjoin R ({b} : Set B)
    let : Module.Finite R A := .of_fg (Algebra.IsIntegral.isIntegral (R := R) b).fg_adjoin_singleton
    let a : A := ⟨b, Algebra.subset_adjoin rfl⟩
    have hTrivial (x : A) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
      rcases trivial_idempotents (x : B) (hx.map A.val) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    obtain ⟨_, e, he, hLocal⟩ := decompose A
    let : IsLocalRing A := local_of_components e he hLocal hTrivial
    let : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top (R := R)
    have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m.asIdeal
    have hn := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) n.asIdeal
    have hEq := (IsLocalRing.eq_maximalIdeal hm).trans (IsLocalRing.eq_maximalIdeal hn).symm
    exact iff_of_eq (congrArg (fun I : Ideal A => a ∈ I) hEq)⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

end PhilipponHenselianIntegralConnectedness

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace PhilipponHenselianClosedFiberConnectedness

universe u

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [IsLocalRing R] [Algebra.IsIntegral R B]

private theorem comap_eq_closedPoint [IsLocalRing B] :
    PrimeSpectrum.comap (algebraMap R B) (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (IsLocalRing.maximalIdeal B))

private theorem eq_closedPoint_of_comap_eq [IsLocalRing B] (b : PrimeSpectrum B)
    (hb : PrimeSpectrum.comap (algebraMap R B) b = IsLocalRing.closedPoint R) :
    b = IsLocalRing.closedPoint B := by
  apply PrimeSpectrum.ext
  have hI : b.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
    congrArg PrimeSpectrum.asIdeal hb
  have hMax : (b.asIdeal.comap (algebraMap R B)).IsMaximal :=
    hI ▸ IsLocalRing.maximalIdeal.isMaximal R
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap b.asIdeal hMax)

set_option maxRecDepth 4096 in
/-- A surjective factorization through an integral algebra transfers
preconnectedness of its closed fiber to the original closed fiber. -/
theorem closedFiber_preconnected_of_integral_factorization
    {Y : Scheme.{u}} [PreconnectedSpace Y] (f : Y ⟶ Spec (.of R))
    (g : Y ⟶ Spec (.of B)) [Surjective g]
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = f)
    (hConnected : ∀ [IsLocalRing B], _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint B}))
    (decompose : ∀ (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A],
      ∃ (_ : Fintype (MaximalSpectrum A)) (e : MaximalSpectrum A → A),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · let : IsEmpty Y := hY
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' {IsLocalRing.closedPoint R})]
    exact isPreconnected_empty
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨g (Classical.choice hY)⟩
  let : PreconnectedSpace (PrimeSpectrum B) := ⟨by
    change _root_.IsPreconnected (Set.univ : Set (Spec (.of B)))
    rw [← g.surjective.range_eq]
    exact isPreconnected_range g.continuous⟩
  let : IsLocalRing B :=
    PhilipponHenselianIntegralConnectedness.isLocalRing_of_integral_of_preconnected R B decompose
  have h : f ⁻¹' {IsLocalRing.closedPoint R} = g ⁻¹' {IsLocalRing.closedPoint B} := by
    ext y
    simp only [Set.mem_preimage]
    rw [← hg, Scheme.Hom.comp_apply]
    change PrimeSpectrum.comap (algebraMap R B) (g y) = IsLocalRing.closedPoint R ↔
      g y = IsLocalRing.closedPoint B
    exact ⟨eq_closedPoint_of_comap_eq (g y), fun h => h ▸ comap_eq_closedPoint⟩
  rw [h]
  exact hConnected

/-- For a proper scheme, its global-section algebra is integral over the
base. It suffices to check closed-fiber connectedness for proper maps
over a local ring that induce an isomorphism on global sections. -/
theorem closedFiber_preconnected_of_affinization
    {Y : Scheme.{u}} [PreconnectedSpace Y] (f : Y ⟶ Spec (.of R)) [IsProper f]
    (hConnected : ∀ {A : Type u} [CommRing A] [IsLocalRing A] {V : Scheme.{u}}
      (g : V ⟶ Spec (.of A)) [IsProper g] [IsIso g.appTop],
      _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint A}))
    (decompose : ∀ (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A],
      ∃ (_ : Fintype (MaximalSpectrum A)) (e : MaximalSpectrum A → A),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  let B := Γ(Y, ⊤)
  let φ : CommRingCat.of R ⟶ B := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop
  let : Algebra R B := φ.hom.toAlgebra
  have hφ : φ.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  let : Algebra.IsIntegral R B := ⟨hφ⟩
  have h : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = f := by
    change Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  let : CompactSpace Y := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsProper (Y.toSpecΓ ≫ Spec.map φ) := by
    change IsProper (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [h]
    infer_instance
  let : IsProper Y.toSpecΓ := IsProper.of_comp Y.toSpecΓ (Spec.map φ)
  let : IsIso Y.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  exact closedFiber_preconnected_of_integral_factorization f Y.toSpecΓ h
    (fun [_] => hConnected Y.toSpecΓ) decompose

end PhilipponHenselianClosedFiberConnectedness

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponClosedFiberDegreeZeroReduction
universe u
theorem closedFiber_preconnected {R : Type u} [CommRing R] [HenselianLocalRing R]
    {V : Scheme.{u}} (g : V ⟶ Spec (.of R)) [IsProper g] [PreconnectedSpace V] :
    _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint R}) := by
  apply PhilipponHenselianClosedFiberConnectedness.closedFiber_preconnected_of_affinization g
  · intro A _ _ W a _ _
    exact PhilipponClosedFiberIdempotents.closedFiber_preconnected_of_idempotents_lift a
      (Scheme.exists_appTop_eq_idempotent_closed_fiber_of_isProper a)
  · intro A _ _ _
    obtain ⟨hI, e, hE, _, _, hLocal⟩ :=
      HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
        (R := R) (S := A)
    exact ⟨hI, e, hE, hLocal⟩

end PhilipponClosedFiberDegreeZeroReduction

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem solution
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g) (N : ℕ) (hN : N.Prime)
    (B : PhilipponTorsorSectionFibers.Torsor ((PhilipponEtaleSmallSite.pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))) :
    ∃ (D : PhilipponTorsorSectionFibers.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))) (d : D.D.P ⟶ (PhilipponEtaleBaseChangeComparison.baseChange j).op ⋙ B.D.P),
      ∀ (U : Y.Etaleᵒᵖ) (x y : D.D.P.obj U),
        B.D.diff ((PhilipponEtaleBaseChangeComparison.baseChange j).op.obj U) (d.app U x) (d.app U y) =
          ((PhilipponEtaleSmallSite.pullbackAdjunction j).unit.app ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))).hom.app U (D.D.diff U x y) := by
  let : NeZero N := ⟨hN.ne_zero⟩
  let M := ULift.{u} (ZMod N)
  let : Finite M := inferInstanceAs (Finite (ULift.{u} (ZMod N)))
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨V, hV, ⟨e⟩⟩ := AlgebraicGeometry.Scheme.exists_finite_etale_representation_constant_torsor_of_ne_zero j N hN.ne_zero B
  let : IsFinite V.hom := hV
  obtain ⟨W, hW, ⟨f⟩⟩ := AlgebraicGeometry.Scheme.exists_finite_etale_cover_lift_of_proper_closed_fiber A g s j h V
  let : IsFinite W.hom := hW
  exact PhilipponEtaleTorsorFromCover.exists_equivariant_lift_of_represented g j s h
    (fun p => PhilipponClosedFiberDegreeZeroReduction.closedFiber_preconnected p) M B W
    (yoneda.mapIso f ≪≫ e)

end

end
