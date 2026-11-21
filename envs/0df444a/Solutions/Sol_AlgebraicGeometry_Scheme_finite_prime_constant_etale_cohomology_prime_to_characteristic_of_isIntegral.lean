-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T19:23:20.997929+00:00
-- url     : https://prove2.me/submissions/8c70a685-a37a-4e1b-828e-113b135d4e87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_iff_of_surjective_closed_immersion
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_of_proper_excision
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_succ_of_closed_cover
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic_of_projective_embedding

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

/-- Global degree-zero étale cohomology of discrete constant coefficients. -/
def degreeZeroEquiv : ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of A)).H 0 ≃+ C(X, A) := by
  let T := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let e := ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)).mapIso
    (constantSheafIso X A)
  exact (Sheaf.H.equiv₀ _ hT).trans e.addCommGroupIsoToAddEquiv

/-- A continuous function to a discrete set is determined by one value
on each irreducible component. -/
theorem finite_degreeZero [NoetherianSpace X] [Finite A] :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).H 0) := by
  let : Finite (irreducibleComponents X) := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let choosePoint (Z : irreducibleComponents X) : Z.val :=
    ⟨Z.property.1.nonempty.choose, Z.property.1.nonempty.choose_spec⟩
  let sample (f : C(X, A)) (Z : irreducibleComponents X) := f (choosePoint Z)
  apply Finite.of_injective (sample ∘ degreeZeroEquiv X A)
  apply Function.Injective.comp _ (degreeZeroEquiv X A).injective
  intro f g h
  ext x
  have hx : x ∈ ⋃₀ irreducibleComponents X := by rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
  let i : irreducibleComponents X := ⟨Z, hZ⟩
  have hconst (a : C(X, A)) : a x = a (choosePoint i) :=
    (hZ.1.2.isPreconnected.image a a.continuous.continuousOn).subsingleton
      ⟨x, hxZ, rfl⟩ ⟨choosePoint i, (choosePoint i).property, rfl⟩
  exact (hconst f).trans ((congrFun h i).trans (hconst g).symm)

/-- Finite constant coefficients have finite degree-zero étale cohomology
on every quasi-compact scheme locally of finite type over a field. -/
theorem finite_degreeZero_of_finiteType {K : Type u} [Field K] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π]
    (B : Type u) [AddCommGroup B] [Finite B] :
    Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of B)).H 0) := by
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian π
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace π }
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  exact finite_degreeZero Y B

end PhilipponEtaleConstantDegreeZero

end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace PhilipponReducedClosedSubscheme

theorem radical_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  apply (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mpr
  exact isReduced_of_injective (I.subschemeObjIso U).inv.hom
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.radical = I) : IsReduced I.subscheme := by
  have hU (U : X.affineOpens) : (I.ideal U).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    exact congrArg (fun J : X.IdealSheafData => J.ideal U) h
  haveI (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hU U)
  haveI (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem isReduced_iff_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsReduced I.subscheme ↔ I.radical = I :=
  ⟨fun h => @radical_eq_of_isReduced X I h, isReduced_of_radical_eq I⟩

theorem integral_of_prime_top {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)
    [(I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime] : IsIntegral I.subscheme := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  haveI : (I.ideal U).IsPrime :=
    (inferInstance : (I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime)
  haveI : IsDomain (Γ(X, U) ⧸ I.ideal U) := inferInstance
  let f := I.subschemeCover.f U
  haveI : Surjective f := by
    constructor
    intro x
    have hx : x ∈ f.opensRange := by
      change x ∈ (I.subschemeCover.f U).opensRange
      rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
      trivial
    exact hx
  haveI : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : IsIntegral (Spec (I.subschemeCover.X U)) := by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsIntegral.of_isIso f

theorem radical_comap_open {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : (I.comap f).radical = I.radical.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((I.comap f).ideal U).radical = (I.radical.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Ideal.comap_radical _ _).symm

theorem eq_of_reduced_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : I.radical = I) (hJ : J.radical = J) (hs : I.support = J.support) : I = J := by
  rw [← hI, ← Scheme.IdealSheafData.vanishingIdeal_support, hs,
    Scheme.IdealSheafData.vanishingIdeal_support, hJ]

end PhilipponReducedClosedSubscheme

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
set_option maxHeartbeats 360000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.IdealSheafData


namespace PhilipponEtaleIntegralReduction

universe u

variable {X : Scheme.{u}}

private def piece (S : Closeds X) : Scheme.{u} := (vanishingIdeal S).subscheme

private def ι (S : Closeds X) : piece S ⟶ X := (vanishingIdeal S).subschemeι

private instance closed_ι (S : Closeds X) : IsClosedImmersion (ι S) := by
  change IsClosedImmersion (vanishingIdeal S).subschemeι
  infer_instance

private theorem range_ι (S : Closeds X) : Set.range (ι S) = (S : Set X) := by
  change Set.range (vanishingIdeal S).subschemeι = (S : Set X)
  rw [range_subschemeι, coe_support_vanishingIdeal]

private instance reduced_piece (S : Closeds X) : AlgebraicGeometry.IsReduced (piece S) :=
  PhilipponReducedClosedSubscheme.isReduced_of_radical_eq _ (vanishingIdeal_support.symm)

private theorem integral_piece (S : Closeds X) (hS : IsIrreducible (S : Set X)) :
    IsIntegral (piece S) := by
  have h : IrreducibleSpace (Set.range (ι S)) := isIrreducible_iff_irreducibleSpace.mp
    ((range_ι S).symm ▸ hS)
  have : IrreducibleSpace (piece S) :=
    (ι S).isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced (piece S)

private def incl {S C : Closeds X} (h : S ≤ C) : piece S ⟶ piece C :=
  inclusion (vanishingIdeal_antimono h)

private theorem incl_ι {S C : Closeds X} (h : S ≤ C) : incl h ≫ ι C = ι S :=
  inclusion_subschemeι _

private instance incl_closed {S C : Closeds X} (h : S ≤ C) : IsClosedImmersion (incl h) := by
  have : IsClosedImmersion (incl h ≫ ι C) := by
    rw [incl_ι h]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (incl h) (ι C)

private theorem closed_cover {S T C : Closeds X} (hs : S ≤ C) (ht : T ≤ C) (h : S ⊔ T = C) :
    Set.range (incl hs) ∪ Set.range (incl ht) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  have hx : ι C x ∈ (C : Set X) := (range_ι C) ▸ Set.mem_range_self x
  have h' : (S : Set X) ∪ (T : Set X) = (C : Set X) :=
    congrArg (fun B : Closeds X => (B : Set X)) h
  have hx' : ι C x ∈ (S : Set X) ∪ (T : Set X) := h'.symm ▸ hx
  rcases hx' with hx | hx
  · obtain ⟨y, hy⟩ := (range_ι S).symm ▸ hx
    refine Or.inl ⟨y, (ι C).isClosedEmbedding.injective ?_⟩
    rwa [← Scheme.Hom.comp_apply, incl_ι]
  · obtain ⟨y, hy⟩ := (range_ι T).symm ▸ hx
    refine Or.inr ⟨y, (ι C).isClosedEmbedding.injective ?_⟩
    rwa [← Scheme.Hom.comp_apply, incl_ι]

section Intersection

variable {S T C : Closeds X} (hs : S ≤ C) (ht : T ≤ C)

private abbrev intersection := pullback (incl hs) (incl ht)

private abbrev intersectionι : intersection hs ht ⟶ piece C :=
  pullback.fst (incl hs) (incl ht) ≫ incl hs

private def intersectionReduction : piece (S ⊓ T) ⟶ intersection hs ht :=
  pullback.lift (incl inf_le_left) (incl inf_le_right) (by
    apply (cancel_mono (ι C)).mp
    simp only [Category.assoc, incl_ι])

private theorem intersectionReduction_comp :
    intersectionReduction hs ht ≫ intersectionι hs ht ≫ ι C = ι (S ⊓ T) := by
  rw [← Category.assoc, ← Category.assoc, intersectionReduction, pullback.lift_fst,
    Category.assoc, incl_ι, incl_ι]

private instance : IsClosedImmersion (intersectionReduction hs ht) := by
  have : IsClosedImmersion (intersectionReduction hs ht ≫ (intersectionι hs ht ≫ ι C)) := by
    rw [intersectionReduction_comp hs ht]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (intersectionReduction hs ht)
    (intersectionι hs ht ≫ ι C)

private instance : Surjective (intersectionReduction hs ht) where
  surj p := by
    let f := intersectionι hs ht ≫ ι C
    have : IsClosedImmersion f := inferInstanceAs (IsClosedImmersion (intersectionι hs ht ≫ ι C))
    have hpS : f p ∈ (S : Set X) := by
      change ((pullback.fst (incl hs) (incl ht) ≫ incl hs) ≫ ι C) p ∈ _
      rw [Category.assoc]
      rw [incl_ι, Scheme.Hom.comp_apply, ← range_ι S]
      exact Set.mem_range_self _
    have hpT : f p ∈ (T : Set X) := by
      change ((pullback.fst (incl hs) (incl ht) ≫ incl hs) ≫ ι C) p ∈ _
      rw [pullback.condition, Category.assoc, incl_ι, Scheme.Hom.comp_apply,
        ← range_ι T]
      exact Set.mem_range_self _
    obtain ⟨z, hz⟩ := (range_ι (S ⊓ T)).symm ▸ (show f p ∈ ((S ⊓ T : Closeds X) : Set X) from ⟨hpS, hpT⟩)
    refine ⟨z, f.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, show intersectionReduction hs ht ≫ f = ι (S ⊓ T) from
      intersectionReduction_comp hs ht, hz]

end Intersection

private abbrev constantH (Y : Scheme.{u}) (A : Type u) [AddCommGroup A] (q : ℕ) : Type u :=
  ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).H q

private theorem finite_empty {Y : Scheme.{u}} [IsEmpty Y] (A : Type u) [AddCommGroup A] (q : ℕ) :
    Finite (constantH Y A q) := by
  let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)
  have hz : IsZero F := by
    rw [IsZero.iff_id_eq_zero]
    apply Sheaf.hom_ext
    ext W s
    have hW : IsEmpty W.unop.left := ⟨fun w => ‹IsEmpty Y›.false (W.unop.hom w)⟩
    exact (Scheme.subsingleton_sections_of_isEmpty hW F).elim _ _
  have : Subsingleton (F.H q) := Sheaf.subsingleton_H_of_isZero hz q
  infer_instance

private theorem split_closed {C : Closeds X} (hne : (C : Set X).Nonempty)
    (hC : ¬ IsIrreducible (C : Set X)) :
    ∃ S T : Closeds X, S < C ∧ T < C ∧ S ⊔ T = C := by
  have h : ¬ IsPreirreducible (C : Set X) := fun hp => hC ⟨hne, hp⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at h
  simp only [not_forall, not_or] at h
  obtain ⟨S, T, hS, hT, hcover, hnS, hnT⟩ := h
  let s : Closeds X := ⟨S, hS⟩
  let t : Closeds X := ⟨T, hT⟩
  refine ⟨C ⊓ s, C ⊓ t, lt_of_le_of_ne inf_le_left ?_, lt_of_le_of_ne inf_le_left ?_, ?_⟩
  · intro he
    exact hnS (he ▸ inf_le_right : C ≤ s)
  · intro he
    exact hnT (he ▸ inf_le_right : C ≤ t)
  · rw [← inf_sup_left]
    exact inf_eq_left.mpr hcover

private theorem complement_piece (C : Closeds X) (U : (piece C).Opens) (hU : Nonempty U) :
    ∃ (S : Closeds X) (h : S < C), Set.range (incl h.le) = (U : Set (piece C))ᶜ := by
  let S : Closeds X := ⟨ι C '' (U : Set (piece C))ᶜ,
    (ι C).isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hle : S ≤ C := by
    rintro _ ⟨y, _, rfl⟩
    change (ι C) y ∈ (C : Set X)
    exact (range_ι C) ▸ Set.mem_range_self y
  have hproper : S < C := by
    refine lt_of_le_of_ne hle ?_
    intro he
    obtain ⟨x⟩ := hU
    have hxC : ι C x.val ∈ (C : Set X) := (range_ι C) ▸ Set.mem_range_self x.val
    have hxS : ι C x.val ∈ (S : Set X) := he.symm ▸ hxC
    obtain ⟨y, hy, hyx⟩ := hxS
    exact hy ((ι C).isClosedEmbedding.injective hyx ▸ x.property)
  refine ⟨S, hproper, ?_⟩
  ext x
  have hc : ι C x ∈ (S : Set X) ↔ x ∉ (U : Set (piece C)) := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (ι C).isClosedEmbedding.injective hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [Set.mem_compl_iff, ← hc, ← range_ι S]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, congrArg (fun f : piece S ⟶ X => f y) (incl_ι hproper.le).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (ι C).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, incl_ι, hy]

private theorem closed_induction (K : Type u) [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (P : Scheme.{u} → Prop)
    (hintegral : ∀ {Y : Scheme.{u}} [IsIntegral Y] (σ : Y ⟶ Spec (.of K)) [IsProper σ],
      (∀ (U : Y.Opens), Nonempty U → ∃ (Z : Scheme.{u}) (i : Z ⟶ Y),
        IsClosedImmersion i ∧ Set.range i = (U : Set Y)ᶜ ∧ P Z) → P Y)
    (hempty : ∀ {Y : Scheme.{u}} [IsEmpty Y], P Y)
    (hthicken : ∀ {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i],
      P Z → P Y)
    (hcover : ∀ {W Y Z : Scheme.{u}} (σ : W ⟶ Spec (.of K)) [IsProper σ]
      (i : Y ⟶ W) (j : Z ⟶ W) [IsClosedImmersion i] [IsClosedImmersion j],
      Set.range i ∪ Set.range j = Set.univ → P Y → P Z → P (pullback i j) → P W) : P X := by
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian π
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace π }
  have step : ∀ C : Closeds X, P (piece C) := by
    intro C
    refine wellFounded_lt.induction (C := fun C => P (piece C)) C ?_
    intro C ih
    let τ := ι C ≫ π
    have : IsProper τ := inferInstanceAs (IsProper (ι C ≫ π))
    by_cases hC : IsIrreducible (C : Set X)
    · have : IsIntegral (piece C) := integral_piece C hC
      refine hintegral τ fun U hU => ?_
      obtain ⟨S, hS, h⟩ := complement_piece C U hU
      exact ⟨piece S, incl hS.le, inferInstance, h, ih S hS⟩
    by_cases hne : (C : Set X).Nonempty
    · obtain ⟨S, T, hs, ht, hST⟩ := split_closed hne hC
      have hsT : S ⊓ T < C := lt_of_le_of_lt inf_le_left hs
      exact hcover τ (incl hs.le) (incl ht.le) (closed_cover hs.le ht.le hST)
        (ih _ hs) (ih _ ht) (hthicken (intersectionReduction hs.le ht.le) (ih _ hsT))
    · have : IsEmpty (piece C) := ⟨fun x => hne ⟨ι C x, (range_ι C) ▸ Set.mem_range_self x⟩⟩
      exact hempty
  have : Surjective (ι (⊤ : Closeds X)) := ⟨Set.range_eq_univ.mp (range_ι ⊤)⟩
  exact hthicken (ι (⊤ : Closeds X)) (step ⊤)

/-- In the integral case of proper finiteness, one may assume finiteness on
the reduced closed complement of any nonempty open subscheme. -/
theorem finite_constant_induction (K : Type u) [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (A : Type u) [AddCommGroup A] [Finite A]
    (hintegral : ∀ {Y : Scheme.{u}} [IsIntegral Y] (σ : Y ⟶ Spec (.of K)) [IsProper σ],
      (∀ (U : Y.Opens), Nonempty U → ∃ (Z : Scheme.{u}) (i : Z ⟶ Y),
        IsClosedImmersion i ∧ Set.range i = (U : Set Y)ᶜ ∧ ∀ n, Finite (constantH Z A n)) →
      ∀ q, Finite (constantH Y A q)) (q : ℕ) :
    Finite (constantH X A q) := by
  refine closed_induction K π (fun Y => ∀ n, Finite (constantH Y A n))
    hintegral (fun n => finite_empty A n) ?_ ?_ q
  · intro Y Z i _ _ h n
    exact (Scheme.finite_constant_etale_cohomology_iff_of_surjective_closed_immersion i A n).mpr (h n)
  · intro W Y Z σ _ i j _ _ h hy hz ht n
    cases n with
    | zero => exact PhilipponEtaleConstantDegreeZero.finite_degreeZero_of_finiteType σ A
    | succ n =>
      exact Scheme.finite_constant_etale_cohomology_succ_of_closed_cover i j h A n
        (hy _) (hz _) (ht _)

end PhilipponEtaleIntegralReduction

end

section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponEtaleProjectiveReduction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev ProjectiveSpace (K : Type u) [Field K] (n : ℕ) :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)

private abbrev constantH (Y : Scheme.{u}) (A : Type u) [AddCommGroup A] (q : ℕ) : Type u :=
  ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)).H q

/-- Proper excision reduces proper étale finiteness to projective finiteness.
The exceptional inverse image of the closed complement is projective because
it is a closed subscheme of the projective Chow modification. -/
theorem finite_constant_of_projective (K : Type u) [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (A : Type u) [AddCommGroup A] [Finite A]
    (hprojective : ∀ {Y : Scheme.{u}} (σ : Y ⟶ Spec (.of K)) (n : ℕ)
      (e : Y ⟶ ProjectiveSpace K n) [IsClosedImmersion e],
      e ≫ ProjSpace.π K n = σ → ∀ q, Finite (constantH Y A q))
    (hexcision : ∀ {W Y Z : Scheme.{u}} (p : Y ⟶ W) [IsProper p] (i : Z ⟶ W)
      [IsClosedImmersion i] (U : W.Opens) [IsIso (p ∣_ U)],
      Set.range i = (U : Set W)ᶜ →
      (∀ q, Finite (constantH Y A q)) → (∀ q, Finite (constantH Z A q)) →
      (∀ q, Finite (constantH (pullback p i) A q)) → ∀ q, Finite (constantH W A q))
    (q : ℕ) : Finite (constantH X A q) := by
  refine PhilipponEtaleIntegralReduction.finite_constant_induction K π A ?_ q
  intro W _ σ _ closedComplement
  obtain ⟨D⟩ := ChowDatumProj.nonempty_of σ (ChowDatum.nonempty σ)
  have hU : Nonempty D.U := by
    obtain ⟨x, hx⟩ := D.hU_dense.nonempty
    exact ⟨⟨x, hx⟩⟩
  have : IsIso (D.p ∣_ D.U) := by
    rw [morphismRestrict]
    infer_instance
  obtain ⟨Z, i, hi, hr, hZ⟩ := closedComplement D.U hU
  refine hexcision D.p i D.U hr (hprojective (D.p ≫ σ) D.Nd D.ιN D.hoverN) hZ ?_
  refine hprojective (pullback.fst D.p i ≫ D.p ≫ σ) D.Nd (pullback.fst D.p i ≫ D.ιN) ?_
  rw [Category.assoc, D.hoverN]

end PhilipponEtaleProjectiveReduction

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) ≠ 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by 
  let : NeZero p := ⟨hp.ne_zero⟩
  refine PhilipponEtaleProjectiveReduction.finite_constant_of_projective K π
    (ULift.{u} (ZMod p)) ?_ ?_ q
  · intro Y σ n e _ _ m
    exact Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_projective_embedding
      K n e p hp hK m
  · intro W Y Z f _ i _ U _ h hy hz he m
    exact Scheme.finite_constant_etale_cohomology_of_proper_excision
      (ULift.{u} (ZMod p)) f i U h hy hz he m


end
