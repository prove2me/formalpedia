-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_relative_constant_etale_cohomology_succ_equiv_of_proper_excision
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T20:23:54.929703+00:00
-- url     : https://prove2.me/submissions/a7498b43-f77d-4999-a449-1ef7a0616f0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Theorems.Thm_AlgebraicGeometry_Scheme_isZero_relative_constant_etale_higher_direct_image_of_proper_excision
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_equiv_of_isZero_higher_direct_image

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

/-- Descent of a continuous function along a closed map that has singleton
fibres off a closed set, when the function vanishes over that set. -/
theorem existsUnique_descend_zero [Zero A] {p : Y → X} (hp : Continuous p)
    (hclosed : IsClosedMap p) {S : Set X} (hS : IsClosed S)
    (hcover : range p ∪ S = univ)
    (hinj : ∀ {y z : Y}, p y = p z → p y ∉ S → y = z)
    (a : C(Y, A)) (ha : ∀ y, p y ∈ S → a y = 0) :
    ∃! b : C(X, A), (∀ x ∈ S, b x = 0) ∧ ∀ y, b (p y) = a y := by
  let r : C(Y, range p) := ⟨rangeFactorization p, continuous_rangeFactorization_iff.mpr hp⟩
  have hr : IsClosedMap r := by
    intro T hT
    have h : r '' T = Subtype.val ⁻¹' (p '' T) := by
      ext x
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, congrArg Subtype.val h⟩,
        fun ⟨y, hy, h⟩ => ⟨y, hy, Subtype.ext h⟩⟩
    rw [h]
    exact (hclosed T hT).preimage continuous_subtype_val
  let hq := hr.isQuotientMap r.continuous rangeFactorization_surjective
  have hfactor : Function.FactorsThrough a r := by
    intro y z he
    have he' : p y = p z := congrArg Subtype.val he
    by_cases h : p y ∈ S
    · rw [ha y h, ha z (he' ▸ h)]
    · rw [hinj he' h]
  let c := hq.lift a hfactor
  have hc (y : Y) : c (r y) = a y := DFunLike.congr_fun (hq.lift_comp a hfactor) y
  have hagree (y : range p) (z : S) (h : y.val = z.val) : c y = (0 : A) := by
    obtain ⟨t, ht⟩ := hq.surjective y
    rw [← ht, hc]
    apply ha
    change (r t).val ∈ S
    rw [ht, h]
    exact z.property
  obtain ⟨b, hb, hb₀⟩ := exists_glue hclosed.isClosed_range.isClosedEmbedding_subtypeVal
    hS.isClosedEmbedding_subtypeVal (by rwa [Subtype.range_coe, Subtype.range_coe])
    c (ContinuousMap.const S 0) hagree
  refine ⟨b, ⟨fun x hx => hb₀ ⟨x, hx⟩, fun y => (hb (r y)).trans (hc y)⟩, ?_⟩
  intro b' hb'
  ext x
  have hx : x ∈ range p ∪ S := hcover.symm ▸ mem_univ x
  rcases hx with ⟨y, rfl⟩ | hx
  · exact (hb'.2 y).trans ((hb (r y)).trans (hc y)).symm
  · exact (hb'.1 x hx).trans (hb₀ ⟨x, hx⟩).symm

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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponEtaleProperRelativeMaps

universe u v

/-- Being an isomorphism on an open subset survives arbitrary base change. -/
theorem isIso_restrict_baseChange {X Y V : Scheme.{u}} (f : Y ⟶ X) (v : V ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] : IsIso (pullback.fst v f ∣_ (v ⁻¹ᵁ U)) := by
  have h₁ := (isPullback_morphismRestrict (pullback.fst v f) (v ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback v f).flip
  have h₂ := (IsPullback.of_hasPullback (v ∣_ U) (f ∣_ U)).flip.paste_horiz
    (isPullback_morphismRestrict f U).flip
  rw [morphismRestrict_ι] at h₂
  let e := h₁.isoIsPullback _ _ h₂
  have he : e.hom ≫ pullback.fst (v ∣_ U) (f ∣_ U) = pullback.fst v f ∣_ (v ⁻¹ᵁ U) :=
    h₁.isoIsPullback_hom_snd _ _ h₂
  rw [← he]
  infer_instance

/-- A function on the modification that vanishes on the exceptional
inverse image descends uniquely to a function vanishing on the center. -/
theorem existsUnique_descend_zero {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ)
    {A : Type v} [TopologicalSpace A] [Zero A] (a : C(Y, A))
    (ha : ∀ t : ↥(pullback f i), a (pullback.fst f i t) = 0) :
    ∃! b : C(X, A), (∀ x ∈ Set.range i, b x = 0) ∧ ∀ y, b (f y) = a y := by
  have point (y : (f ⁻¹ᵁ U).toScheme) : ((f ∣_ U) y).val = f y.val :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ X => k y) (morphismRestrict_ι f U)
  have hcover : Set.range f ∪ Set.range i = Set.univ := by
    rw [hU]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨y, hy⟩ := (f ∣_ U).surjective ⟨x, hx⟩
      exact Or.inl ⟨y.val, (point y).symm.trans (congrArg Subtype.val hy)⟩
    · exact Or.inr hx
  have hinj {y z : Y} (h : f y = f z) (hy : f y ∉ Set.range i) : y = z := by
    rw [hU] at hy
    have hy' : f y ∈ (U : Set X) := by simpa only [Set.mem_compl_iff, not_not] using hy
    have hz' : f z ∈ (U : Set X) := h ▸ hy'
    let y' : (f ⁻¹ᵁ U).toScheme := ⟨y, hy'⟩
    let z' : (f ⁻¹ᵁ U).toScheme := ⟨z, hz'⟩
    have hs : (f ∣_ U) y' = (f ∣_ U) z' := Subtype.ext ((point y').trans (h.trans (point z').symm))
    exact congrArg (fun t : (f ⁻¹ᵁ U).toScheme => t.val) ((f ∣_ U).homeomorph.injective hs)
  refine PhilipponClosedCoverContinuousMaps.existsUnique_descend_zero
    f.continuous f.isClosedMap i.isClosedEmbedding.isClosed_range hcover hinj a ?_
  rintro y ⟨z, hz⟩
  obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback f i) y z hz.symm
  rw [← ht]
  exact ha t

section Additive

variable {X Y Z : Scheme.{u}} (A : Type v) [AddCommGroup A] [TopologicalSpace A]
  [DiscreteTopology A]

/-- The subgroup of continuous coefficient functions that vanish along a
given scheme morphism. -/
def vanishingFunctions (i : Z ⟶ X) : AddSubgroup C(X, A) where
  carrier := {a | ∀ z : Z, a (i z) = 0}
  zero_mem' := fun _ => rfl
  add_mem' ha hb z := by
    change _ + _ = (0 : A)
    rw [ha z, hb z, add_zero]
  neg_mem' ha z := by
    change -_ = (0 : A)
    rw [ha z, neg_zero]

private def pullbackFunctions (f : Y ⟶ X) (i : Z ⟶ X) :
    vanishingFunctions A i →+ vanishingFunctions A (pullback.fst f i) where
  toFun a := ⟨a.val.comp ⟨f, f.continuous⟩, by
    intro t
    change a.val (f (pullback.fst f i t)) = 0
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact a.property (pullback.snd f i t)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Degree-zero relative coefficient functions are unchanged by pullback
along a proper modification over the complement. -/
noncomputable def functionsEquiv (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ) :
    vanishingFunctions A i ≃+ vanishingFunctions A (pullback.fst f i) := by
  apply AddEquiv.ofBijective (pullbackFunctions A f i)
  apply (Function.bijective_iff_existsUnique _).mpr
  intro a
  obtain ⟨b, hb, hu⟩ := existsUnique_descend_zero f i U hU a.val a.property
  refine ⟨⟨b, fun z => hb.1 (i z) (Set.mem_range_self z)⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    exact hb.2 y
  · intro c hc
    apply Subtype.ext
    refine hu c.val ⟨?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact c.property z
    · intro y
      exact congrArg (fun k : vanishingFunctions A (pullback.fst f i) => k.val y) hc

/-- The descent equivalence holds after any base change of a proper
excision square. -/
noncomputable def functionsEquiv_baseChange {V : Scheme.{u}} (v : V ⟶ X) (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ) :
    vanishingFunctions A (pullback.fst v i) ≃+
      vanishingFunctions A (pullback.fst (pullback.fst v f) (pullback.fst v i)) := by
  have : IsIso (pullback.fst v f ∣_ (v ⁻¹ᵁ U)) := isIso_restrict_baseChange f v U
  refine functionsEquiv A (pullback.fst v f) (pullback.fst v i) (v ⁻¹ᵁ U) ?_
  rw [Scheme.Pullback.range_fst, hU, Set.preimage_compl]
  rfl

end Additive

end PhilipponEtaleProperRelativeMaps

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleClosedCover (restriction)
namespace PhilipponEtaleRelativeCohomology
universe u
variable {X Z : Scheme.{u}} (i : Z ⟶ X)
variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
/-- Sections of the relative sheaf are exactly the kernel of the
restriction map on the chosen étale object. -/
def relativeSections (W : X.Etaleᵒᵖ) :
    (relativeSheaf i A).obj.obj W ≃+
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj W).map
        (restriction A i)).hom.ker := by
  let F := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj W
  have : F.Additive := ⟨by intros; rfl⟩
  let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ (evaluation _ _).obj W
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso (Iso.refl _ : G ≅ F)
  exact ((PreservesKernel.iso F (restriction A i)) ≪≫
    AddCommGrpCat.kernelIsoKer (F.map (restriction A i))).addCommGroupIsoToAddEquiv

end PhilipponEtaleRelativeCohomology

end

section

set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleProperRelativeMaps (vanishingFunctions functionsEquiv_baseChange)
open PhilipponEtaleRelativeCohomology (relativeSheaf relativeSections relativeConstant)


namespace PhilipponEtaleRelativeDirectImage

universe u

private def subgroupEquiv {B : Type u} [AddCommGroup B] {P Q : AddSubgroup B} (h : P = Q) : P ≃+ Q := by
  subst Q
  exact AddEquiv.refl P

@[simp] private theorem subgroupEquiv_val {B : Type u} [AddCommGroup B] {P Q : AddSubgroup B}
    (h : P = Q) (b : P) : (subgroupEquiv h b).val = b.val := by
  subst Q
  rfl

variable {X Y Z : Scheme.{u}} (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private theorem vanishingFunctions_eq_of_range {B C D : Scheme.{u}}
    (a : C ⟶ B) (b : D ⟶ B) (h : Set.range a = Set.range b) :
    vanishingFunctions A a = vanishingFunctions A b := by
  ext w
  change (∀ x : C, w (a x) = 0) ↔ (∀ x : D, w (b x) = 0)
  constructor
  · intro hw x
    obtain ⟨y, hy⟩ := h.symm ▸ Set.mem_range_self (f := b) x
    exact hy ▸ hw y
  · intro hw x
    obtain ⟨y, hy⟩ := h ▸ Set.mem_range_self (f := a) x
    exact hy ▸ hw y

private abbrev sectionsAt (W : X.Etale) := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op W)

private theorem sectionKernel (i : Z ⟶ X) (W : X.Etale) :
    (((sectionsAt W).map (restriction A i)).hom.ker : AddSubgroup C(W.left, A)) =
      vanishingFunctions A (pullback.fst W.hom i) := by
  ext a
  change C(W.left, A) at a
  change ((sectionsAt W).map (restriction A i)).hom a = 0 ↔
    ∀ z : ↥(pullback W.hom i), a (pullback.fst W.hom i z) = 0
  constructor
  · intro h z
    exact congrArg (fun s : C(↥(pullback W.hom i), A) => s z) h
  · intro h
    exact ContinuousMap.ext h

/-- Evaluate the relative sheaf as functions vanishing along the closed
inverse image in an étale object. -/
def sectionFunctions (i : Z ⟶ X) (W : X.Etale) :
    (relativeSheaf i A).obj.obj (op W) ≃+ vanishingFunctions A (pullback.fst W.hom i) :=
  (relativeSections i A (op W)).trans (subgroupEquiv (sectionKernel A i W))

private theorem sectionFunctions_val (i : Z ⟶ X) (W : X.Etale) (s : (relativeSheaf i A).obj.obj (op W)) :
    (sectionFunctions A i W s).val = ((kernel.ι (restriction A i)).hom.app (op W)) s := by
  calc
    _ = (relativeSections i A (op W) s).val := subgroupEquiv_val _ _
    _ = _ := by
      let F := sectionsAt W
      let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op W)
      have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
      have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso (Iso.refl _ : G ≅ F)
      have eq : ((PreservesKernel.iso F (restriction A i)).hom ≫
          (AddCommGrpCat.kernelIsoKer (F.map (restriction A i))).hom) ≫
          AddCommGrpCat.ofHom (AddSubgroup.subtype (F.map (restriction A i)).hom.ker) =
          F.map (kernel.ι (restriction A i)) := by
        simp only [Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
          PreservesKernel.iso_hom, kernelComparison_comp_ι]
      exact ConcreteCategory.congr_hom eq s

private theorem sectionFunctions_map (i : Z ⟶ X) {V W : X.Etale} (g : V ⟶ W)
    (s : (relativeSheaf i A).obj.obj (op W)) (x : V.left) :
    (sectionFunctions A i V ((relativeSheaf i A).obj.map g.op s)).val x =
      (sectionFunctions A i W s).val (g.left x) := by
  rw [sectionFunctions_val, sectionFunctions_val]
  have h := congrArg (fun t : C(V.left, A) => t x)
    (NatTrans.naturality_apply (kernel.ι (restriction A i)).hom g.op s)
  exact h

private theorem range_pullback_centers (v : X.Etale) (f : Y ⟶ X) (i : Z ⟶ X) :
    Set.range (pullback.fst (pullback.fst v.hom f) (pullback.fst v.hom i)) =
      Set.range (pullback.fst (pullback.snd v.hom f) (pullback.fst f i)) := by
  ext x
  simp only [Scheme.Pullback.range_fst, Set.mem_preimage]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rfl

variable (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
  (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)

private def sectionComparison (W : X.Etale) :
    (relativeSheaf i A).obj.obj (op W) ≃+
      (relativeSheaf (pullback.fst f i) A).obj.obj (op ((baseChange f).obj W)) :=
  (sectionFunctions A i W).trans ((functionsEquiv_baseChange A W.hom f i U hU).trans
    ((subgroupEquiv (vanishingFunctions_eq_of_range A _ _ (range_pullback_centers W f i))).trans
      (sectionFunctions A (pullback.fst f i) ((baseChange f).obj W)).symm))

private theorem sectionComparison_apply (W : X.Etale) (s : (relativeSheaf i A).obj.obj (op W))
    (y : ((baseChange f).obj W).left) :
    (sectionFunctions A (pullback.fst f i) ((baseChange f).obj W)
      (sectionComparison A f i U hU W s)).val y =
      (sectionFunctions A i W s).val (pullback.fst W.hom f y) := by
  let b := functionsEquiv_baseChange A W.hom f i U hU (sectionFunctions A i W s)
  let e := sectionFunctions A (pullback.fst f i) ((baseChange f).obj W)
  let c := subgroupEquiv (vanishingFunctions_eq_of_range A _ _ (range_pullback_centers W f i)) b
  calc
    _ = c.val y := congrArg (fun z => z.val y) (e.apply_symm_apply c)
    _ = b.val y := congrArg (fun z : C((pullback W.hom f : Scheme.{u}), A) => z y)
      (subgroupEquiv_val _ b)
    _ = _ := rfl

/-- The relative sheaf on the target is the direct image of the relative
sheaf on the source of a proper excision square. -/
def relativeDirectImageIso :
    relativeSheaf i A ≅ (pushforward f).obj (relativeSheaf (pullback.fst f i) A) := by
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  refine NatIso.ofComponents (fun W => (sectionComparison A f i U hU W.unop).toAddCommGrpIso) ?_
  intro W V g
  apply ConcreteCategory.hom_ext
  intro s
  apply (sectionFunctions A (pullback.fst f i) ((baseChange f).obj V.unop)).injective
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (sectionFunctions A (pullback.fst f i) ((baseChange f).obj V.unop)
      (sectionComparison A f i U hU V.unop ((relativeSheaf i A).obj.map g s))).val y =
    (sectionFunctions A (pullback.fst f i) ((baseChange f).obj V.unop)
      ((relativeSheaf (pullback.fst f i) A).obj.map ((baseChange f).map g.unop).op
        (sectionComparison A f i U hU W.unop s))).val y
  rw [sectionComparison_apply, sectionFunctions_map, sectionComparison_apply]
  calc
    _ = (sectionFunctions A i W.unop s).val (g.unop.left (pullback.fst V.unop.hom f y)) :=
      sectionFunctions_map A i g.unop s (pullback.fst V.unop.hom f y)
    _ = _ := congrArg (sectionFunctions A i W.unop s).val
      (congrArg (fun k : ((baseChange f).obj V.unop).left ⟶ W.unop.left => k y)
        (map_isPullback f g.unop).w)

/-- The direct-image comparison with the canonical discrete topology. -/
def relativeConstantDirectImageIso :
    relativeConstant i A ≅ (pushforward f).obj (relativeConstant (pullback.fst f i) A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact relativeDirectImageIso A f i U hU

end PhilipponEtaleRelativeDirectImage

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ) (q : ℕ) :
    Nonempty ((PhilipponEtaleRelativeCohomology.relativeConstant i A).H (q + 1) ≃+
      (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A).H (q + 1)) := by
  let e := PhilipponEtaleRelativeDirectImage.relativeConstantDirectImageIso A f i U hU
  let P := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))
  let m := ((CategoryTheory.Abelian.extFunctorObj P (q + 1)).mapIso e).addCommGroupIsoToAddEquiv
  exact ⟨m.trans (Classical.choice (AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_of_isZero_higher_direct_image f _ (AlgebraicGeometry.Scheme.isZero_relative_constant_etale_higher_direct_image_of_proper_excision A f i U hU) (q + 1)))⟩


end
