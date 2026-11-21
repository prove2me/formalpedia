-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_relative_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T19:49:23.414535+00:00
-- url     : https://prove2.me/submissions/8686b983-b697-41d2-9462-7e9b8a812a19

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
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
  Classical.choice (AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_closed_direct_image i F q)
end PhilipponEtaleClosedCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PhilipponEtaleClosedCover
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleClosedCohomology (cohomologyEquiv)
open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso)


namespace PhilipponEtaleClosedCoverFiniteness

universe u
private abbrev AbelianSheaves (W : Scheme.{u}) := Sheaf W.smallEtaleTopology AddCommGrpCat.{u}

private abbrev H {W : Scheme.{u}} (F : AbelianSheaves W) (q : ℕ) : Type u := F.H q

theorem finite_of_shortExact_succ {W : Scheme.{u}} {S : ShortComplex (AbelianSheaves W)}
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

end PhilipponEtaleClosedCoverFiniteness

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
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedCoverFiniteness (finite_of_shortExact_succ)
open PhilipponEtaleClosedCohomology (cohomologyEquiv)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)


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

/-- Restriction to a closed subscheme is locally surjective for the
constant sheaf, in its model by maps to a discrete group. -/
theorem epi_restriction [IsClosedImmersion i] : Epi (restriction A i) := by
  apply (Sheaf.isLocallySurjective_iff_epi' (J := X.smallEtaleTopology)
    AddCommGrpCat.{u} (restriction A i)).mp
  constructor
  intro W s
  let p := pullback.fst W.hom i
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst W.hom i))
  change C(↥(pullback W.hom i), A) at s
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
  refine ⟨ContinuousMap.const (V x).left (a x), ?_⟩
  apply ContinuousMap.ext
  intro y
  let z := ((baseChange i).map (f x)).left y
  have hz : p z ∈ U x := by
    have h := congrArg (fun k : (_ : Scheme) ⟶ W.left => k y) (map_isPullback i (f x)).w.symm
    change p z = (D x).ι (pullback.fst (V x).hom i y) at h
    rw [h]
    exact (pullback.fst (V x).hom i y).property
  change a x = s z
  exact (ha x z hz).symm

private def restrictionSequence : ShortComplex (AbelianSheaves X) :=
  ShortComplex.mk (kernel.ι (restriction A i)) (restriction A i) (kernel.condition _)

private theorem restrictionSequence_shortExact [IsClosedImmersion i] :
    (restrictionSequence i A).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (restriction A i)) ?_ (epi_restriction i A)
  change Mono (kernel.ι (restriction A i))
  infer_instance

end Restriction

private theorem finite_left_of_shortExact {W : Scheme.{u}} {S : ShortComplex (AbelianSheaves W)}
    (hS : S.ShortExact) (q : ℕ) (h₂ : Finite (H S.X₂ q))
    (h₃ : ∀ r < q, Finite (H S.X₃ r)) : Finite (H S.X₁ q) := by
  cases q with
  | zero =>
    let : Finite (H S.X₂ 0) := h₂
    have : Mono S.f := hS.mono_f
    exact Finite.of_injective (Sheaf.H.map S.f 0) (Ext.postcomp_mk₀_injective_of_mono _ S.f)
  | succ q =>
    exact finite_of_shortExact_succ hS q h₂ (h₃ q (Nat.lt_succ_self q))

private theorem finite_middle_of_shortExact {W : Scheme.{u}} {S : ShortComplex (AbelianSheaves W)}
    (hS : S.ShortExact) (q : ℕ) (h₁ : Finite (H S.X₁ q)) (h₃ : Finite (H S.X₃ q)) :
    Finite (H S.X₂ q) := by
  let Q := (constantSheaf W.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let f : H S.X₁ q →+ H S.X₂ q := Sheaf.H.map S.f q
  let g : H S.X₂ q →+ H S.X₃ q := Sheaf.H.map S.g q
  have hex : g.ker ≤ f.range := by
    intro x hx
    exact Ext.covariant_sequence_exact₂ Q hS x hx
  let : Fintype (H S.X₁ q) := @Fintype.ofFinite _ h₁
  let : Fintype (H S.X₃ q) := @Fintype.ofFinite _ h₃
  exact @Finite.of_fintype _ (AddGroup.fintypeOfKerLeRange f g hex)

private abbrev constantH (X : Scheme.{u}) (A : Type u) [AddCommGroup A] (q : ℕ) : Type u :=
  ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).H q

/-- The relative cohomology comparison gives the finiteness implication
in proper excision by the two short exact restriction sequences. -/
theorem finite_of_relative_comparison {X Y Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (A : Type u) [AddCommGroup A]
    (hrel : ∀ q, Nonempty ((relativeConstant i A).H q ≃+
      (relativeConstant (pullback.fst f i) A).H q))
    (hY : ∀ q, Finite (constantH Y A q)) (hZ : ∀ q, Finite (constantH Z A q))
    (hE : ∀ q, Finite (constantH (pullback f i) A q)) (q : ℕ) :
    Finite (constantH X A q) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have compare (W : Scheme.{u}) (r : ℕ) :
      Finite (constantH W A r) ↔ Finite ((continuousSheaf W A).H r) :=
    ((Sheaf.functorH W.smallEtaleTopology r).mapIso
      (constantSheafIso W A)).addCommGroupIsoToAddEquiv.toEquiv.finite_iff
  let j := pullback.fst f i
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (pullback.fst f i))
  have hrelY : Finite ((relativeConstant j A).H q) :=
    finite_left_of_shortExact (restrictionSequence_shortExact j A) q
      ((compare Y q).mp (hY q)) (fun r _ =>
        (cohomologyEquiv j (continuousSheaf (pullback f i) A) r).toEquiv.finite_iff.mp
          ((compare _ r).mp (hE r)))
  have hrelX : Finite ((relativeConstant i A).H q) :=
    (Classical.choice (hrel q)).toEquiv.finite_iff.mpr hrelY
  exact (compare X q).mpr
    (finite_middle_of_shortExact (restrictionSequence_shortExact i A) q hrelX
      ((cohomologyEquiv i (continuousSheaf Z A) q).toEquiv.finite_iff.mp ((compare Z q).mp (hZ q))))

end PhilipponEtaleRelativeCohomology

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [AddCommGroup A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    (hrel : ∀ q, Nonempty ((PhilipponEtaleRelativeCohomology.relativeConstant i A).H q ≃+
      (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A).H q))
    (hY : ∀ q, Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (hZ : ∀ q, Finite (((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q))
    (hE : ∀ q, Finite (((constantSheaf (pullback f i).smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) := by
  exact PhilipponEtaleRelativeCohomology.finite_of_relative_comparison f i A hrel hY hZ hE q


end
