-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_integral_zariski_refinement_of_surjective_etale
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T06:14:28.589697+00:00
-- url     : https://prove2.me/submissions/e49edc1a-0c05-4425-bbb4-2010fde0eb8f

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Topology.Spectral.ConstructibleTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section

namespace PhilipponEtaleGeometricStalks
universe u
/-- A geometric point given by a separable closure of the residue field. -/
def geometricMap {X : Scheme.{u}} (x : X) :
    Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ X :=
  (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

@[simp] theorem geometricMap_apply {X : Scheme.{u}} (x : X) : geometricMap x default = x := by
  simp [geometricMap, Scheme.SpecToEquivOfField]

end PhilipponEtaleGeometricStalks

namespace PhilipponEtaleStalkPullback
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}} (f : Y ⟶ X)
theorem exists_point_lift_of_mem_range [IsClosedImmersion f] (t : Spec (CommRingCat.of K) ⟶ X)
    (ht : t default ∈ Set.range f) : ∃ s' : Spec (CommRingCat.of K) ⟶ Y, s' ≫ f = t := by
  let p := pullback.fst t f
  have hp : (default : Spec (CommRingCat.of K)) ∈ Set.range p := by
    rw [show Set.range p = t ⁻¹' Set.range f from Scheme.Pullback.range_fst t f]
    exact ht
  have : Surjective p :=
    ⟨fun x => (Subsingleton.elim (default : Spec (CommRingCat.of K)) x) ▸ hp⟩
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst t f))
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  refine ⟨inv p ≫ pullback.snd t f, ?_⟩
  rw [Category.assoc, ← pullback.condition]
  exact IsIso.inv_hom_id_assoc p t
end PhilipponEtaleStalkPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace PhilipponEtaleCoverRefinement

universe u
variable {U X Y : Scheme.{u}} {f : U ⟶ X} {p : Y ⟶ X} {j : U ⟶ Y}

/-- The graph of a factorization through a scheme over the base. -/
def factorGraph (h : j ≫ p = f) : U ⟶ pullback f p :=
  pullback.lift (𝟙 U) j ((Category.id_comp f).trans h.symm)

theorem factorGraph_isOpenImmersion (h : j ≫ p = f) [Etale f] [IsOpenImmersion j] :
    IsOpenImmersion (factorGraph h) := by
  have hfst : factorGraph h ≫ pullback.fst f p = 𝟙 U := pullback.lift_fst _ _ _
  have hsnd : factorGraph h ≫ pullback.snd f p = j := pullback.lift_snd _ _ _
  have : Mono (factorGraph h) := mono_of_mono_fac hfst
  have : Etale (factorGraph h ≫ pullback.snd f p) := hsnd.symm ▸ inferInstanceAs (Etale j)
  have : Etale (factorGraph h) := Etale.of_comp (factorGraph h) (pullback.snd f p)
  exact IsOpenImmersion.of_flat_of_mono _

theorem factorGraph_isClosedImmersion (h : j ≫ p = f) [IsSeparated p] :
    IsClosedImmersion (factorGraph h) := by
  have hfst : factorGraph h ≫ pullback.fst f p = 𝟙 U := pullback.lift_fst _ _ _
  have : Mono (factorGraph h) := mono_of_mono_fac hfst
  have : IsProper (factorGraph h ≫ pullback.fst f p) :=
    hfst.symm ▸ inferInstanceAs (IsProper (𝟙 U))
  exact (IsClosedImmersion.iff_isProper_and_mono (f := factorGraph h)).mpr
    ⟨IsProper.of_comp (factorGraph h) (pullback.fst f p), inferInstance⟩

/-- The open complement of the graph inside the changed étale cover. -/
def complement (h : j ≫ p = f) [IsSeparated p] : (pullback f p).Opens :=
  letI := factorGraph_isClosedImmersion h
  ⟨(Set.range (factorGraph h))ᶜ, (factorGraph h).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The complementary sheets still cover the boundary of the open
factorization. -/
theorem boundary_subset_range_complement (h : j ≫ p = f) [Surjective f] [IsSeparated p] :
    (Set.range j)ᶜ ⊆ Set.range ((complement h).ι ≫ pullback.snd f p) := by
  intro y hy
  obtain ⟨v, hv⟩ := (inferInstance : Surjective (pullback.snd f p)).surj y
  have hvW : v ∈ complement h := by
    rintro ⟨x, rfl⟩
    have hsnd : factorGraph h ≫ pullback.snd f p = j := pullback.lift_snd _ _ _
    apply hy
    exact ⟨x, (congrArg (fun k : U ⟶ Y => k x) hsnd).symm.trans hv⟩
  exact ⟨⟨v, hvW⟩, hv⟩

theorem complement_etale (h : j ≫ p = f) [Etale f] [IsSeparated p] :
    Etale ((complement h).ι ≫ pullback.snd f p) := inferInstance

section Degree

open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply)

/-- Lifts of a specified scheme point through a morphism. -/
abbrev Lifts {S : Scheme.{u}} (f : U ⟶ X) (s : S ⟶ X) :=
  {g : S ⟶ U // g ≫ f = s}

/-- Lifts of the point with residue field the separable closure of `κ(x)`. -/
abbrev GeometricLifts (f : U ⟶ X) (x : X) :=
  Lifts f (geometricMap x)

/-- The locus where the geometric fiber admits at least `n` distinct points. -/
def geometricLiftLocus (f : U ⟶ X) (n : ℕ) : Set X :=
  {x | Nonempty (Fin n ↪ GeometricLifts f x)}

private theorem isOpenImmersion_section {S : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (l : S ⟶ U) (hl : l ≫ p = 𝟙 S) : IsOpenImmersion l := by
  have : Mono l := mono_of_mono_fac hl
  have : Etale (l ≫ p) := hl.symm ▸ inferInstanceAs (Etale (𝟙 S))
  have : Etale l := Etale.of_comp l p
  exact IsOpenImmersion.of_flat_of_mono l

private theorem range_field_point {K : Type u} [Field K] (l : Spec (CommRingCat.of K) ⟶ U) :
    Set.range l = {l default} := by
  ext z
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨t, ht⟩ => ht.symm.trans (congrArg l (Subsingleton.elim t _)),
    fun hz => ⟨default, hz.symm⟩⟩

private theorem exists_section_at {K : Type u} [Field K] [IsSepClosed K]
    (p : U ⟶ Spec (CommRingCat.of K)) [Etale p] (y : U) :
    ∃ l : Spec (CommRingCat.of K) ⟶ U, l ≫ p = 𝟙 _ ∧ l default = y :=
  Scheme.exists_fac_of_etale_of_isSepClosed p (𝟙 _) y (Subsingleton.elim _ _)

/-- Over a separably closed field an étale scheme is discrete. -/
theorem discreteTopology_of_etale_field {K : Type u} [Field K] [IsSepClosed K]
    (p : U ⟶ Spec (CommRingCat.of K)) [Etale p] : DiscreteTopology U := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro y
  obtain ⟨l, hl, hy⟩ := exists_section_at p y
  have : IsOpenImmersion l := isOpenImmersion_section p l hl
  rw [← hy, ← range_field_point]
  exact l.isOpenMap.isOpen_range

/-- Points of an étale scheme over a separably closed field can be evaluated
over any extension field. The field of definition and the extension give
the same set of lifts. -/
noncomputable def liftToPointEquiv {K E : Type u} [Field K] [IsSepClosed K] [Field E]
    (p : U ⟶ Spec (CommRingCat.of K)) [Etale p] (a : K →+* E) :
    Lifts p (Spec.map (CommRingCat.ofHom a)) ≃ U := by
  let A := Spec.map (CommRingCat.ofHom a)
  have hFactor (l : Spec (CommRingCat.of K) ⟶ U) (hl : l ≫ p = 𝟙 _)
      (g : Lifts p A) (hg : g.val default = l default) : A ≫ l = g.val := by
    have : IsOpenImmersion l := isOpenImmersion_section p l hl
    have hRange : Set.range g.val ⊆ Set.range l := by
      rw [range_field_point, range_field_point, hg]
    let b := IsOpenImmersion.lift l g.val hRange
    have hb : b ≫ l = g.val := IsOpenImmersion.lift_fac _ _ _
    have hab : b = A := by
      calc
        b = b ≫ (l ≫ p) := by rw [hl, Category.comp_id]
        _ = A := by rw [← Category.assoc, hb, g.property]
    exact (congrArg (· ≫ l) hab).symm.trans hb
  apply Equiv.ofBijective (fun g : Lifts p A => g.val default)
  constructor
  · intro g h heq
    obtain ⟨l, hl, hpt⟩ := exists_section_at p (g.val default)
    exact Subtype.ext ((hFactor l hl g hpt.symm).symm.trans
      (hFactor l hl h (heq.symm.trans hpt.symm)))
  · intro y
    obtain ⟨l, hl, hy⟩ := exists_section_at p y
    exact ⟨⟨A ≫ l, by rw [Category.assoc, hl, Category.comp_id]⟩,
      (congrArg l (Subsingleton.elim _ _)).trans hy⟩

/-- Lifting a composited point is equivalent to lifting through the pullback. -/
def liftsPullbackEquiv {S T : Scheme.{u}} (f : U ⟶ X) (s : S ⟶ X) (a : T ⟶ S) :
    Lifts f (a ≫ s) ≃ Lifts (pullback.snd f s) a where
  toFun g := ⟨pullback.lift g.val a g.property, pullback.lift_snd _ _ _⟩
  invFun g := ⟨g.val ≫ pullback.fst f s, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, g.property]⟩
  left_inv g := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv g := Subtype.ext (pullback.hom_ext
    (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans g.property.symm))

/-- A separably closed base point identifies the lift sets of all its field
extensions with the underlying points of a single fiber scheme. -/
noncomputable def liftsEquivPointsOfFiber {K E : Type u} [Field K] [IsSepClosed K] [Field E]
    (f : U ⟶ X) [Etale f] (s : Spec (CommRingCat.of K) ⟶ X) (a : K →+* E) :
    Lifts f (Spec.map (CommRingCat.ofHom a) ≫ s) ≃ ↥(pullback f s) :=
  (liftsPullbackEquiv f s _).trans (liftToPointEquiv (pullback.snd f s) a)

private noncomputable def liftsEquivPointsOfOwnFiber {K : Type u} [Field K] [IsSepClosed K]
    (f : U ⟶ X) [Etale f] (s : Spec (CommRingCat.of K) ⟶ X) :
    Lifts f s ≃ ↥(pullback f s) := by
  have he : Spec.map (CommRingCat.ofHom (RingHom.id K)) ≫ s = s := by
    rw [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  exact (Equiv.cast (congrArg (Lifts f) he.symm)).trans
    (liftsEquivPointsOfFiber f s (RingHom.id K))

theorem finite_geometricLifts (f : U ⟶ X) [Etale f] [QuasiCompact f] (x : X) :
    Finite (GeometricLifts f x) := by
  let S := Spec (CommRingCat.of (SeparableClosure (X.residueField x)))
  let s := geometricMap x
  let P := pullback f s
  let p : P ⟶ S := pullback.snd f s
  have : Etale p := inferInstanceAs (Etale (pullback.snd f s))
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (pullback.snd f s))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : DiscreteTopology P := discreteTopology_of_etale_field p
  have : Finite P := finite_of_compact_of_discrete
  exact Finite.of_injective _ (liftsEquivPointsOfOwnFiber f s).injective

/-- A quasi-compact étale morphism is locally quasi-finite. -/
theorem locallyQuasiFinite_of_quasiCompact_etale (f : U ⟶ X) [Etale f] [QuasiCompact f] :
    LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro x
  have := finite_geometricLifts f x
  let eval : GeometricLifts f x → ↥(f ⁻¹' ({x} : Set X)) := fun g =>
    ⟨g.val default, (congrArg (fun h : _ ⟶ X => h default) g.property).trans (geometricMap_apply x)⟩
  apply Set.finite_coe_iff.mp
  apply Finite.of_surjective eval
  intro y
  obtain ⟨g, hg, hy⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f (geometricMap x) y.val
    ((Set.mem_singleton_iff.mp y.property).trans (geometricMap_apply x).symm)
  exact ⟨⟨g, hg⟩, Subtype.ext hy⟩

private theorem geometricPoint_factors {K : Type u} [Field K] [IsSepClosed K]
    (t : Spec (CommRingCat.of K) ⟶ X) (x : X) (hx : t default = x) :
    ∃ a : SeparableClosure (X.residueField x) →+* K,
      Spec.map (CommRingCat.ofHom a) ≫ geometricMap x = t := by
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective t
  have hy : ((Scheme.SpecToEquivOfField K X).symm ⟨y, b⟩) default = y := by
    simp [Scheme.SpecToEquivOfField]
  rw [hy] at hx
  subst x
  algebraize [b.hom]
  let a : SeparableClosure (X.residueField y) →ₐ[X.residueField y] K := IsSepClosed.lift
  have hb : CommRingCat.ofHom (algebraMap (X.residueField y) _) ≫
      CommRingCat.ofHom a.toRingHom = b := by
    ext1
    exact a.comp_algebraMap
  refine ⟨a.toRingHom, ?_⟩
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y) =
    Spec.map b ≫ X.fromSpecResidueField y
  rw [← Category.assoc, ← Spec.map_comp, hb]

/-- The lift set at any separably closed point agrees with that at the
separable closure of the residue field of its image. -/
noncomputable def liftsEquivGeometricLifts {K : Type u} [Field K] [IsSepClosed K]
    (f : U ⟶ X) [Etale f] (t : Spec (CommRingCat.of K) ⟶ X) :
    Lifts f t ≃ GeometricLifts f (t default) := by
  classical
  let a := (geometricPoint_factors t (t default) rfl).choose
  have ha := (geometricPoint_factors t (t default) rfl).choose_spec
  let s := geometricMap (t default)
  exact (Equiv.cast (congrArg (Lifts f) ha.symm)).trans
    ((liftsEquivPointsOfFiber f s a).trans (liftsEquivPointsOfOwnFiber f s).symm)

/-- Geometric lift sets are preserved by arbitrary base change. -/
noncomputable def geometricLiftsPullbackEquiv (f : U ⟶ X) [Etale f] (p : Y ⟶ X) (y : Y) :
    GeometricLifts (pullback.snd f p) y ≃ GeometricLifts f (p y) := by
  let t := geometricMap y
  have hy : (t ≫ p) default = p y := by simp [t]
  exact ((liftsPullbackEquiv f p t).symm.trans (liftsEquivGeometricLifts f (t ≫ p))).trans
    (Equiv.cast (congrArg (GeometricLifts f) hy))

variable (f) [Etale f] (n : ℕ)

private def powerChart : X.Etale :=
  ∏ᶜ fun _ : Fin n => Scheme.Etale.mk f

private def eval (k : Fin n) : (powerChart f n).left ⟶ U :=
  (Pi.π (fun _ : Fin n => Scheme.Etale.mk f) k).left

private theorem eval_comp (k : Fin n) : eval f n k ≫ f = (powerChart f n).hom :=
  MorphismProperty.Over.w (Pi.π (fun _ : Fin n => Scheme.Etale.mk f) k)

private def pair (a b : Fin n) : (powerChart f n).left ⟶ pullback f f :=
  pullback.lift (eval f n a) (eval f n b) ((eval_comp f n a).trans (eval_comp f n b).symm)

private def coincidence (a b : Fin n) :
    pullback (pullback.diagonal f) (pair f n a b) ⟶ (powerChart f n).left :=
  pullback.snd _ _

private instance (a b : Fin n) : IsOpenImmersion (coincidence f n a b) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd (pullback.diagonal f) (pair f n a b)))

variable [IsSeparated f]

private instance (a b : Fin n) : IsClosedImmersion (coincidence f n a b) :=
  inferInstanceAs (IsClosedImmersion (pullback.snd (pullback.diagonal f) (pair f n a b)))

private theorem mem_coincidence_iff {K : Type u} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ (powerChart f n).left) (a b : Fin n) :
    t default ∈ Set.range (coincidence f n a b) ↔ t ≫ eval f n a = t ≫ eval f n b := by
  let P := pair f n a b
  let c := coincidence f n a b
  constructor
  · intro ht
    obtain ⟨q, hq⟩ := PhilipponEtaleStalkPullback.exists_point_lift_of_mem_range c t ht
    have he : c ≫ eval f n a = c ≫ eval f n b := by
      have h₁ := congrArg (· ≫ pullback.fst f f) (pullback.condition
        (f := pullback.diagonal f) (g := P))
      have h₂ := congrArg (· ≫ pullback.snd f f) (pullback.condition
        (f := pullback.diagonal f) (g := P))
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
        P, pair, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
      exact h₁.symm.trans h₂
    simpa only [← hq, Category.assoc] using congrArg (q ≫ ·) he
  · intro ht
    have he : (t ≫ eval f n a) ≫ pullback.diagonal f = t ≫ P := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, P, pair, pullback.lift_fst]
      · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, P, pair, pullback.lift_snd]
          using ht
    let v := pullback.lift (t ≫ eval f n a) t he
    have hv : v ≫ c = t := pullback.lift_snd _ _ _
    exact ⟨v default, congrArg (fun k : Spec (CommRingCat.of K) ⟶ (powerChart f n).left => k default) hv⟩

private def configuration : (powerChart f n).left.Opens :=
  ⟨⋂ p : {p : Fin n × Fin n // p.1 ≠ p.2}, (Set.range (coincidence f n p.val.1 p.val.2))ᶜ,
    isOpen_iInter_of_finite fun p =>
      (coincidence f n p.val.1 p.val.2).isClosedEmbedding.isClosed_range.isOpen_compl⟩

private def configurationMap : (configuration f n).toScheme ⟶ X :=
  (configuration f n).ι ≫ (powerChart f n).hom

private instance : Etale (configurationMap f n) := inferInstanceAs
  (Etale ((configuration f n).ι ≫ (powerChart f n).hom))

private theorem geometricLiftLocus_eq_range :
    geometricLiftLocus f n = Set.range (configurationMap f n) := by
  classical
  let C := configuration f n
  let D := configurationMap f n
  ext x
  let S := Spec (CommRingCat.of (SeparableClosure (X.residueField x)))
  constructor
  · rintro ⟨l⟩
    let F := Scheme.Etale.forget X
    have : PreservesFiniteLimits F := inferInstanceAs
      (PreservesFiniteLimits (MorphismProperty.Over.forget (@Etale) ⊤ X))
    let P := isLimitOfHasProductOfPreservesLimit F (fun _ : Fin n => Scheme.Etale.mk f)
    let E : Fan (fun _ : Fin n => Over.mk f) :=
      Fan.mk (Over.mk (geometricMap x)) (fun k => Over.homMk (l k).val (l k).property)
    let t := P.lift E
    have ht (k : Fin n) : t.left ≫ eval f n k = (l k).val :=
      congrArg Over.Hom.left (P.fac E ⟨k⟩)
    have hC : t.left (default : S) ∈ C := by
      apply Set.mem_iInter.mpr
      intro k hk
      have h := (mem_coincidence_iff f n t.left k.val.1 k.val.2).mp hk
      have he : (l k.val.1).val = (l k.val.2).val :=
        (ht k.val.1).symm.trans (h.trans (ht k.val.2))
      exact k.property (l.injective (Subtype.ext he))
    refine ⟨⟨t.left (default : S), hC⟩, ?_⟩
    have he := congrArg (fun m : S ⟶ X => m default) (Over.w t)
    exact he.trans (geometricMap_apply x)
  · rintro ⟨y, hy⟩
    obtain ⟨v, hv, hyv⟩ := Scheme.exists_fac_of_etale_of_isSepClosed D (geometricMap x) y
      (hy.trans (geometricMap_apply x).symm)
    let t := v ≫ C.ι
    have ht (k : Fin n) : (t ≫ eval f n k) ≫ f = geometricMap x := by
      rw [Category.assoc, eval_comp]
      exact (Category.assoc _ _ _).trans hv
    refine ⟨⟨fun k => ⟨t ≫ eval f n k, ht k⟩, ?_⟩⟩
    intro a b hab
    by_contra hne
    have hCoin := (mem_coincidence_iff f n t a b).mpr (congrArg Subtype.val hab)
    have hz : t default = y.val := congrArg Subtype.val hyv
    rw [hz] at hCoin
    exact (Set.mem_iInter.mp y.property ⟨(a, b), hne⟩) hCoin

/-- The geometric fiber cardinality has open upper level sets, since the
locus is the image of the space of ordered distinct lifts. -/
theorem isOpen_geometric_lifts : IsOpen (geometricLiftLocus f n) := by
  rw [geometricLiftLocus_eq_range]
  exact (configurationMap f n).isOpenMap.isOpen_range

private theorem quasiCompact_powerChart [QuasiCompact f] : QuasiCompact (powerChart f n).hom := by
  let Q : MorphismProperty Scheme.{u} := @QuasiCompact ⊓ @IsSeparated
  have : Q.IsMultiplicative := inferInstanceAs
    ((@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{u}).IsMultiplicative)
  have : Q.IsStableUnderBaseChange := inferInstanceAs
    ((@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{u}).IsStableUnderBaseChange)
  have : Q.HasOfPostcompProperty Q := by
    constructor
    intro A B C g h hh hgh
    have : IsSeparated h := hh.2
    have : QuasiCompact (g ≫ h) := hgh.1
    have : IsSeparated (g ≫ h) := hgh.2
    exact ⟨QuasiCompact.of_comp g h, IsSeparated.of_comp g h⟩
  let A : Fin n → X.Etale := fun _ => Scheme.Etale.mk f
  let B : Fin n → Q.Over ⊤ X := fun _ =>
    MorphismProperty.Over.mk ⊤ f (show Q f from ⟨inferInstance, inferInstance⟩)
  let F := Scheme.Etale.forget X
  have : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.forget (@Etale) ⊤ X))
  let G := MorphismProperty.Over.forget Q ⊤ X
  let e : F.obj (∏ᶜ A) ≅ G.obj (∏ᶜ B) :=
    PreservesProduct.iso F A ≪≫ (PreservesProduct.iso G B).symm
  have : IsIso ((Over.forget X).map e.hom) := inferInstance
  have : QuasiCompact (∏ᶜ B).hom := (∏ᶜ B).prop.1
  have he : (Over.forget X).map e.hom ≫ (∏ᶜ B).hom = (powerChart f n).hom :=
    Over.w e.hom
  rw [← he]
  infer_instance

/-- The locus is also quasi-compact for a quasi-compact separated étale
morphism over a spectral base. -/
theorem isCompact_geometric_lifts [SpectralSpace X] [QuasiCompact f] :
    IsCompact (geometricLiftLocus f n) := by
  have : QuasiCompact (powerChart f n).hom := quasiCompact_powerChart f n
  have : CompactSpace (powerChart f n).left :=
    QuasiCompact.compactSpace_of_compactSpace (Y := X) (powerChart f n).hom
  have hC : IsClosed ((configuration f n : (powerChart f n).left.Opens) :
      Set (powerChart f n).left) :=
    isClosed_iInter fun a => (coincidence f n a.val.1 a.val.2).isOpenMap.isOpen_range.isClosed_compl
  have : CompactSpace (configuration f n).toScheme := isCompact_iff_compactSpace.mp hC.isCompact
  rw [geometricLiftLocus_eq_range]
  exact isCompact_range (configurationMap f n).continuous

/-- A uniform bound on geometric fiber cardinalities. The compactness step
uses the constructible topology, in which the upper level sets are closed. -/
theorem exists_bound_geometric_lifts [SpectralSpace X] [QuasiCompact f] :
    ∃ d : ℕ, ∀ x : X, Nat.card (GeometricLifts f x) ≤ d := by
  classical
  suffices h : ∃ n, geometricLiftLocus f n = ∅ by
    obtain ⟨n, hn⟩ := h
    refine ⟨n, fun x => ?_⟩
    have := finite_geometricLifts f x
    by_contra! hc
    let E := Finite.equivFin (GeometricLifts f x)
    have hmem : x ∈ geometricLiftLocus f n :=
      ⟨(Fin.castLEEmb hc.le).trans E.symm.toEmbedding⟩
    simp [hn] at hmem
  by_contra! h
  let P (n : ℕ) : Set (WithConstructibleTopology X) :=
    WithTopology.ofTopology ⁻¹' geometricLiftLocus f n
  have hclosed (n : ℕ) : IsClosed (P n) := by
    apply isOpen_compl_iff.mp
    apply WithConstructibleTopology.isOpen_iff.mpr
    simpa [P, Set.preimage_preimage] using IsCompact.isOpen_constructibleTopology_of_isClosed
      (by simpa using isCompact_geometric_lifts f n) (isOpen_geometric_lifts f n).isClosed_compl
  have hmono (n : ℕ) : P (n + 1) ⊆ P n := by
    rintro x ⟨e⟩
    exact ⟨(Fin.castLEEmb (Nat.le_succ n)).trans e⟩
  have hne (n : ℕ) : (P n).Nonempty := by
    obtain ⟨x, hx⟩ := h n
    exact ⟨WithTopology.toTopology _ x, hx⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    P hmono hne (hclosed 0).isCompact hclosed
  let x := WithTopology.ofTopology a
  have := finite_geometricLifts f x
  let m := Nat.card (GeometricLifts f x)
  obtain ⟨e⟩ := Set.mem_iInter.mp ha (m + 1)
  have hc := Nat.card_le_card_of_injective e e.injective
  rw [Nat.card_fin] at hc
  exact Nat.not_succ_le_self m hc

end Degree

section RemoveGraph

variable [Etale f] [IsSeparated f] [IsSeparated p] [IsOpenImmersion j]

open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply)

/-- If the geometric fibers have fewer than `n + 1` points, removing the
graph of a dense open factorization leaves fibers with fewer than `n`
points over the whole new base. -/
theorem geometricLiftLocus_complement_empty_of_dense (h : j ≫ p = f) (n : ℕ)
    (hdense : DenseRange j) (hbound : geometricLiftLocus f (n + 1) = ∅) :
    geometricLiftLocus ((complement h).ι ≫ pullback.snd f p) n = ∅ := by
  let c := (complement h).ι
  let r := pullback.snd f p
  let B := geometricLiftLocus (c ≫ r) n
  by_contra! hn
  have hB : IsOpen B := by
    have : Etale (c ≫ r) := complement_etale h
    exact isOpen_geometric_lifts (c ≫ r) n
  obtain ⟨y, hyB, x, hxy⟩ := hdense.inter_open_nonempty B hB hn
  obtain ⟨e⟩ := hyB
  let S := Spec (CommRingCat.of (SeparableClosure (Y.residueField y)))
  let t := geometricMap y
  have ht : Set.range t ⊆ Set.range j := by
    rw [range_field_point, geometricMap_apply]
    exact Set.singleton_subset_iff.mpr ⟨x, hxy⟩
  let k := IsOpenImmersion.lift j t ht
  have hk : k ≫ j = t := IsOpenImmersion.lift_fac _ _ _
  let a : GeometricLifts r y :=
    ⟨k ≫ factorGraph h, by
      rw [Category.assoc, show factorGraph h ≫ r = j from pullback.lift_snd _ _ _, hk]⟩
  let b (i : Fin n) : GeometricLifts r y :=
    ⟨(e i).val ≫ c, (Category.assoc _ _ _).trans (e i).property⟩
  have hne (i : Fin n) : a ≠ b i := by
    intro hab
    have he := congrArg (fun l : GeometricLifts r y => l.val (default : S)) hab
    have hnot : c ((e i).val (default : S)) ∉ Set.range (factorGraph h) :=
      ((e i).val (default : S)).property
    apply hnot
    refine ⟨k (default : S), ?_⟩
    exact he
  have hb : Function.Injective b := by
    intro i i' he
    apply e.injective
    apply Subtype.ext
    exact (cancel_mono c).mp (congrArg Subtype.val he)
  let d : Option (Fin n) ↪ GeometricLifts r y :=
    ⟨fun i => i.elim a b, by
      intro i i' he
      cases i with
      | none =>
        cases i' with
        | none => rfl
        | some i' => exact (hne i' he).elim
      | some i =>
        cases i' with
        | none => exact (hne i he.symm).elim
        | some i' => exact congrArg some (hb he)⟩
  have hm : p y ∈ geometricLiftLocus f (n + 1) :=
    ⟨((finSuccEquiv n).toEmbedding.trans d).trans (geometricLiftsPullbackEquiv f p y).toEmbedding⟩
  simp [hbound] at hm

end RemoveGraph

end PhilipponEtaleCoverRefinement


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace PhilipponIntegralEtaleRefinement

universe u

variable {A B S T : Scheme.{u}}

/-- Every point of the domain has an open neighborhood on which the map
factors through the specified morphism over the base. -/
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

/-- An integral morphism to a quasi-compact open extends to an integral
morphism to the entire scheme via relative normalization. -/
theorem isPullback_toNormalization_of_integral_over_open
    (V : S.Opens) (g : T ⟶ V.toScheme) [IsIntegralHom g] [QuasiCompact V.ι] :
    IsPullback (g ≫ V.ι).toNormalization g (g ≫ V.ι).fromNormalization V.ι := by
  let f := g ≫ V.ι
  let P := pullback f V.ι
  let p : P ⟶ V.toScheme := pullback.snd f V.ι
  let e : T ≅ P :=
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 T) (snd := g) (f := f) (g := V.ι)
      ⟨Category.id_comp _⟩).isoPullback
  have hfst : e.hom ≫ pullback.fst f V.ι = 𝟙 T := by simp [e]
  have hsnd : e.hom ≫ p = g := by simp [e, p]
  have hp : p = e.inv ≫ g := ((Iso.inv_comp_eq e).mpr hsnd.symm).symm
  have hInt : IsIntegralHom p := by
    rw [hp]
    infer_instance
  let k := e.hom ≫ p.toNormalization ≫ f.normalizationPullback V.ι
  have : IsIso k := inferInstanceAs
    (IsIso (e.hom ≫ p.toNormalization ≫ f.normalizationPullback V.ι))
  apply IsPullback.of_iso_pullback ⟨f.toNormalization_fromNormalization⟩ (asIso k)
  · change k ≫ pullback.fst f.fromNormalization V.ι = f.toNormalization
    simp only [k, p, Category.assoc, Scheme.Hom.toNormalization_normalizationPullback_fst]
    rw [← Category.assoc, hfst, Category.id_comp]
  · change k ≫ pullback.snd f.fromNormalization V.ι = g
    simp only [k, p, Category.assoc, Scheme.Hom.normalizationPullback_snd,
      Scheme.Hom.toNormalization_fromNormalization]
    exact hsnd

/-- An integral cover of an open set extends to an integral cover of the
scheme when a second open already admits the desired factorization and
contains the boundary. -/
theorem exists_integral_cover_of_open_and_boundary
    {f : B ⟶ S} (a : A ⟶ S) (j : B ⟶ A) [IsOpenImmersion j] (hj : j ≫ a = f)
    (V : A.Opens) [QuasiCompact V.ι] (g : T ⟶ V.toScheme) [IsIntegralHom g] [Surjective g]
    (hlocal : LocallyFactorsThrough ((g ≫ V.ι) ≫ a) f)
    (hboundary : (V : Set A)ᶜ ⊆ Set.range j) :
    ∃ (P : Scheme.{u}) (p : P ⟶ A), IsIntegralHom p ∧ Surjective p ∧
      LocallyFactorsThrough (p ≫ a) f := by
  let v := g ≫ V.ι
  let q := v.fromNormalization
  let l := v.toNormalization
  have hlq : l ≫ q = v := v.toNormalization_fromNormalization
  let pb := isPullback_toNormalization_of_integral_over_open V g
  have hl : l = pb.isoPullback.hom ≫ pullback.fst q V.ι := pb.isoPullback_hom_fst.symm
  have : IsOpenImmersion l := by
    rw [hl]
    infer_instance
  have hRange : Set.range l = q ⁻¹' (V : Set A) := by
    rw [hl]
    change Set.range ((pullback.fst q V.ι) ∘ pb.isoPullback.hom) = _
    rw [Function.Surjective.range_comp (inferInstance : Surjective pb.isoPullback.hom).surj,
      Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  have hNorm : LocallyFactorsThrough (q ≫ a) f := by
    intro y
    by_cases hy : q y ∈ V
    · have hy' : y ∈ Set.range l := by rwa [hRange]
      obtain ⟨t, rfl⟩ := hy'
      obtain ⟨W, i, hi, ht, b, hb⟩ := hlocal t
      obtain ⟨w, hw⟩ := ht
      refine ⟨W, i ≫ l, inferInstance, ⟨w, ?_⟩, b, ?_⟩
      · rw [Scheme.Hom.comp_apply, hw]
      · rw [hb, Category.assoc i l, ← Category.assoc l, hlq]
    · have hmem : y ∈ Set.range (pullback.fst q j) := by
        rw [Scheme.Pullback.range_fst]
        exact hboundary hy
      refine ⟨_, pullback.fst q j, inferInstance, hmem, pullback.snd q j, ?_⟩
      rw [← hj, ← pullback.condition_assoc]
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨(V : Set A)ᶜ, V.isOpen.isClosed_compl⟩ :
    TopologicalSpace.Closeds A)
  let c := I.subschemeι
  have hc : Set.range c = (V : Set A)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let b := IsOpenImmersion.lift j c (hc ▸ hboundary)
  have hb : b ≫ f = c ≫ a := by
    rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac]
  let p := coprod.desc q c
  refine ⟨_, p, inferInstanceAs (IsIntegralHom (coprod.desc q c)), ⟨?_⟩, ?_⟩
  · intro y
    by_cases hy : y ∈ V
    · obtain ⟨t, ht⟩ := (inferInstance : Surjective g).surj ⟨y, hy⟩
      refine ⟨(coprod.inl : v.normalization ⟶ v.normalization ⨿ I.subscheme) (l t), ?_⟩
      change (coprod.inl ≫ p) (l t) = y
      rw [show coprod.inl ≫ p = q from coprod.inl_desc q c, ← Scheme.Hom.comp_apply, hlq]
      exact congrArg Subtype.val ht
    · have hy' : y ∈ Set.range c := by rw [hc]; exact hy
      obtain ⟨z, hz⟩ := hy'
      refine ⟨(coprod.inr : I.subscheme ⟶ v.normalization ⨿ I.subscheme) z, ?_⟩
      change (coprod.inr ≫ p) z = y
      rw [show coprod.inr ≫ p = c from coprod.inr_desc q c]
      exact hz
  · intro z
    obtain ⟨z | z, rfl⟩ := (coprodMk v.normalization I.subscheme).surjective z
    · obtain ⟨W, i, hi, hz, d, hd⟩ := hNorm z
      obtain ⟨w, hw⟩ := hz
      refine ⟨W, i ≫ coprod.inl, inferInstance, ⟨w, ?_⟩, d, ?_⟩
      · rw [Scheme.Hom.comp_apply, hw, coprodMk_inl]
      · rw [hd, Category.assoc, ← Category.assoc coprod.inl, show coprod.inl ≫ p = q from
          coprod.inl_desc q c]
    · exact ⟨_, coprod.inr, inferInstance, ⟨z, (coprodMk_inr ..).symm⟩, b, by
        rw [hb, ← Category.assoc, show coprod.inr ≫ p = c from coprod.inr_desc q c]⟩

open PhilipponEtaleCoverRefinement
open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply)

private theorem exists_integral_refinement_of_bound
    (f : A ⟶ S) [SpectralSpace S] [QuasiCompact f] [IsSeparated f] [Etale f] [Surjective f]
    (n : ℕ) (hn : geometricLiftLocus f n = ∅) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S), IsIntegralHom p ∧ Surjective p ∧
      LocallyFactorsThrough p f := by
  induction n generalizing A S with
  | zero =>
    refine ⟨S, 𝟙 S, inferInstance, inferInstance, fun x => ?_⟩
    have hx : x ∈ geometricLiftLocus f 0 := ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩
    simp [hn] at hx
  | succ n ih =>
    have : LocallyQuasiFinite f := locallyQuasiFinite_of_quasiCompact_etale f
    let Y := f.normalization
    let p : Y ⟶ S := f.fromNormalization
    let j : A ⟶ Y := f.toNormalization
    have hj : j ≫ p = f := f.toNormalization_fromNormalization
    have : IsIntegralHom p := inferInstanceAs (IsIntegralHom f.fromNormalization)
    have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion f.toNormalization)
    have : Surjective p := by
      constructor
      intro s
      obtain ⟨x, hx⟩ := (inferInstance : Surjective f).surj s
      refine ⟨j x, ?_⟩
      exact (congrArg (fun k : A ⟶ S => k x) hj).trans hx
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y := S) p
    have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y := S) p
    let W := complement hj
    let r := W.ι ≫ pullback.snd f p
    have hW : IsClosed (W : Set ↥(pullback f p)) := by
      have : IsOpenImmersion (factorGraph hj) := factorGraph_isOpenImmersion hj
      exact (factorGraph hj).isOpenMap.isOpen_range.isClosed_compl
    have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW.isCompact
    have : QuasiCompact r := quasiCompact_of_compactSpace r
    have : Etale r := complement_etale hj
    have : IsSeparated r := inferInstanceAs (IsSeparated (W.ι ≫ pullback.snd f p))
    let V : Y.Opens := ⟨Set.range r, r.isOpenMap.isOpen_range⟩
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp (isCompact_range r.continuous)
    have : SpectralSpace V.toScheme := {
      toCompactSpace := inferInstance
      toQuasiSeparatedSpace := quasiSeparatedSpace_of_quasiSeparated V.ι }
    have : QuasiCompact V.ι := quasiCompact_of_compactSpace V.ι
    let v := IsOpenImmersion.lift V.ι r (by rw [Scheme.Opens.range_ι]; rfl)
    have hv : v ≫ V.ι = r := IsOpenImmersion.lift_fac _ _ _
    have : Etale (v ≫ V.ι) := hv.symm ▸ inferInstanceAs (Etale r)
    have : QuasiCompact (v ≫ V.ι) := hv.symm ▸ inferInstanceAs (QuasiCompact r)
    have : IsSeparated (v ≫ V.ι) := hv.symm ▸ inferInstanceAs (IsSeparated r)
    have : Etale v := Etale.of_comp v V.ι
    have : QuasiCompact v := QuasiCompact.of_comp v V.ι
    have : IsSeparated v := IsSeparated.of_comp v V.ι
    have : Surjective v := by
      constructor
      intro y
      obtain ⟨x, hx⟩ : y.val ∈ Set.range r := y.property
      refine ⟨x, Subtype.ext ?_⟩
      exact (congrArg (fun k : W.toScheme ⟶ Y => k x) hv).trans hx
    have hb : geometricLiftLocus r n = ∅ := geometricLiftLocus_complement_empty_of_dense
      hj n (inferInstance : IsDominant f.toNormalization).denseRange hn
    have hbV : geometricLiftLocus v n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨e⟩
      let t := geometricMap y ≫ V.ι
      let i : GeometricLifts v y ↪ Lifts r t :=
        ⟨fun g => ⟨g.val, by rw [← hv, ← Category.assoc, g.property]⟩,
          fun _ _ he => Subtype.ext (congrArg (fun z : Lifts r t => z.val) he)⟩
      have hmem : t default ∈ geometricLiftLocus r n :=
        ⟨(e.trans i).trans (liftsEquivGeometricLifts r t).toEmbedding⟩
      simp [hb] at hmem
    obtain ⟨Z, g, hgInt, hgSurj, hgLocal⟩ := ih v hbV
    have hLocal : LocallyFactorsThrough ((g ≫ V.ι) ≫ p) f := by
      intro z
      obtain ⟨D, i, hi, hz, k, hk⟩ := hgLocal z
      have hk' : k ≫ r = i ≫ g ≫ V.ι := by
        rw [← hv, ← Category.assoc, hk, Category.assoc]
      refine ⟨D, i, hi, hz, k ≫ W.ι ≫ pullback.fst f p, ?_⟩
      calc
        (k ≫ W.ι ≫ pullback.fst f p) ≫ f = k ≫ r ≫ p := by
          simp only [r, Category.assoc, pullback.condition]
        _ = i ≫ (g ≫ V.ι) ≫ p := by
          rw [← Category.assoc k r, hk']
          simp only [Category.assoc]
    have hboundary : (V : Set Y)ᶜ ⊆ Set.range j := by
      intro y hy
      by_contra h'y
      exact hy (boundary_subset_range_complement hj h'y)
    obtain ⟨P, q, hqInt, hqSurj, hqLocal⟩ :=
      exists_integral_cover_of_open_and_boundary p j hj V g hLocal hboundary
    exact ⟨P, q ≫ p, inferInstance, inferInstance, hqLocal⟩

/-- A quasi-compact separated surjective étale morphism over a spectral
scheme admits a surjective integral cover which locally factors through it. -/
theorem exists_integral_refinement
    (f : A ⟶ S) [SpectralSpace S] [QuasiCompact f] [IsSeparated f] [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ S), IsIntegralHom p ∧ Surjective p ∧
      LocallyFactorsThrough p f := by
  obtain ⟨n, hn⟩ := exists_bound_geometric_lifts f
  refine exists_integral_refinement_of_bound f (n + 1) ?_
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨e⟩
  have := finite_geometricLifts f x
  have he := Nat.card_le_card_of_injective e e.injective
  rw [Nat.card_fin] at he
  exact Nat.not_succ_le_self n (he.trans (hn x))

/-- An étale surjection onto a spectral scheme admits a surjective integral
cover which locally factors through it. -/
theorem exists_integral_refinement_of_etale
    (f : A ⟶ S) [SpectralSpace S] [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ S), IsIntegralHom p ∧ Surjective p ∧
      LocallyFactorsThrough p f := by
  classical
  let C := A.affineCover
  let V (i : C.I₀) : Set S := Set.range (C.f i ≫ f)
  have hCover : (Set.univ : Set S) ⊆ ⋃ i, V i := by
    intro s _
    obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj s
    obtain ⟨i, y, hy⟩ := C.exists_eq x
    exact Set.mem_iUnion.mpr ⟨i, y, congrArg f hy⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover V
    (fun i => (C.f i ≫ f).isOpenMap.isOpen_range) hCover
  let U (i : ↥I) := C.X i.val
  have (i : ↥I) : IsAffine (U i) := inferInstanceAs (IsAffine (A.affineCover.X i.val))
  let c := Sigma.desc (fun i : ↥I => C.f i.val)
  have : Etale c := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)
  have : Surjective (c ≫ f) := by
    constructor
    intro s
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (Set.mem_univ s))
    obtain ⟨hiI, x, hx⟩ := Set.mem_iUnion.mp hi
    refine ⟨Sigma.ι U ⟨i, hiI⟩ x, ?_⟩
    change (Sigma.ι U ⟨i, hiI⟩ ≫ c ≫ f) x = s
    rw [Sigma.ι_desc_assoc]
    exact hx
  obtain ⟨P, p, hi, hs, hp⟩ := exists_integral_refinement (c ≫ f)
  refine ⟨P, p, hi, hs, fun y => ?_⟩
  obtain ⟨W, i, hOpen, hy, h, hh⟩ := hp y
  exact ⟨W, i, hOpen, hy, h ≫ c, (Category.assoc _ _ _).trans hh⟩

end PhilipponIntegralEtaleRefinement


universe u

theorem solution {U X : Scheme.{u}} [SpectralSpace X]
    (f : U ⟶ X) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsIntegralHom p ∧ Surjective p ∧
      ∀ x : P, ∃ (W : Scheme.{u}) (i : W ⟶ P), IsOpenImmersion i ∧ x ∈ Set.range i ∧
        ∃ g : W ⟶ U, g ≫ f = i ≫ p := by 
  exact PhilipponIntegralEtaleRefinement.exists_integral_refinement_of_etale f