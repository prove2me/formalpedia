-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_proper_excision
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T19:56:38.185174+00:00
-- url     : https://prove2.me/submissions/3691b4c2-faef-4cf8-83ff-b6e95876377f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_of_relative_comparison
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_relative_constant_etale_cohomology_succ_equiv_of_proper_excision

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

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleClosedCover (restriction)


namespace PhilipponEtaleRelativeCohomology

universe u

private abbrev AbelianSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{u}) :
    HasExt.{u} (AbelianSheaves X) := inferInstance

private abbrev H {W : Scheme.{u}} (F : AbelianSheaves W) (q : ℕ) : Type u := F.H q

section Restriction

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

end Restriction
end PhilipponEtaleRelativeCohomology

end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleProperRelativeMaps (vanishingFunctions functionsEquiv)
open PhilipponEtaleRelativeCohomology (relativeSheaf relativeSections relativeConstant)


namespace PhilipponEtaleRelativeDegreeZero

universe u

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{u}) :
    HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := inferInstance

/-- Relative étale cohomology in degree zero is the subgroup of continuous
functions that vanish on the closed subscheme. -/
def globalSections {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Type u) [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] :
    (relativeSheaf i A).H 0 ≃+ vanishingFunctions A i := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let F := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)
  have hproj : pullback.fst (𝟙 X) i = pullback.snd (𝟙 X) i ≫ i := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 X) (g := i))
  have hpoint (t : ↥(pullback (𝟙 X) i)) :
      pullback.fst (𝟙 X) i t = i (pullback.snd (𝟙 X) i t) :=
    congrArg (fun k : pullback (𝟙 X) i ⟶ X => k t) hproj
  have hker : ((F.map (restriction A i)).hom.ker : AddSubgroup C(X, A)) =
      vanishingFunctions A i := by
    ext a
    change C(X, A) at a
    change (F.map (restriction A i)).hom a = 0 ↔ ∀ z : Z, a (i z) = 0
    constructor
    · intro h z
      obtain ⟨t, ht⟩ := (pullback.snd (𝟙 X) i).surjective z
      have hx := congrArg (fun b : C(↥(pullback (𝟙 X) i), A) => b t) h
      change a (pullback.fst (𝟙 X) i t) = 0 at hx
      rwa [hpoint, ht] at hx
    · intro h
      apply ContinuousMap.ext
      intro t
      change a (pullback.fst (𝟙 X) i t) = 0
      rw [hpoint, h]
  refine (Sheaf.H.equiv₀ (relativeSheaf i A) hT).trans ?_
  have e := relativeSections i A (op T)
  change (relativeSheaf i A).obj.obj (op T) ≃+ (F.map (restriction A i)).hom.ker at e
  rw [hker] at e
  exact e

/-- Relative étale cohomology in degree zero is invariant under proper excision. -/
def excisionEquiv {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ) (A : Type u) [AddCommGroup A] :
    (relativeConstant i A).H 0 ≃+ (relativeConstant (pullback.fst f i) A).H 0 := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact (globalSections i A).trans
    ((functionsEquiv A f i U hU).trans (globalSections (pullback.fst f i) A).symm)

end PhilipponEtaleRelativeDegreeZero

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    (hY : ∀ q, Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (hZ : ∀ q, Finite (((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q))
    (hE : ∀ q, Finite (((constantSheaf (pullback f i).smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) := by
  refine AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_relative_comparison A f i ?_ hY hZ hE q
  intro r
  cases r with
  | zero => exact ⟨PhilipponEtaleRelativeDegreeZero.excisionEquiv f i U hU A⟩
  | succ r => exact AlgebraicGeometry.Scheme.nonempty_relative_constant_etale_cohomology_succ_equiv_of_proper_excision A f i U hU r


end
