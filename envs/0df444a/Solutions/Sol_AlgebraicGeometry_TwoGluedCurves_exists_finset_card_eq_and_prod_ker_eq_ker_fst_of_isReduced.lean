-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1e63fda3-9da5-55c2-b2c9-2c06a98440a7

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced.AlgebraicGeometry NeronModelInfra CategoryTheory.MonoidalCategory"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "pointOfClosedPoint_apply pointOfClosedPoint LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp IsClosedImmersion IsReduced Scheme.IdealSheafData"
namespace K7Impl
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData TopologicalSpace"

variable {k : Type u} [Field k]

theorem ker_eq_vanishingIdeal_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.ker = vanishingIdeal (Closeds.closure (Set.range f.base)) := by
  rw [← map_bot, ← nilradical_eq_bot (X := X), ← vanishingIdeal_top, map_vanishingIdeal]
  congr 1
  simp [Set.image_univ]

theorem ker_point_eq {X : Scheme.{u}} (p : Spec (CommRingCat.of k) ⟶ X)
    (hp : IsClosed ({p.base (IsLocalRing.closedPoint k)} : Set X)) :
    p.ker = vanishingIdeal ⟨{p.base (IsLocalRing.closedPoint k)}, hp⟩ := by
  rw [ker_eq_vanishingIdeal_of_isReduced]
  congr 1
  apply Closeds.ext
  show closure (Set.range p.base) = {p.base (IsLocalRing.closedPoint k)}
  have : Set.range p.base = {p.base (IsLocalRing.closedPoint k)} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim _ _; rfl
    · rintro rfl; exact ⟨_, rfl⟩
  rw [this, hp.closure_eq]

theorem support_vanishingIdeal_of_singleton {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    ((vanishingIdeal ⟨{x}, hx⟩).support : Set X) = {x} := by
  rw [coe_support_vanishingIdeal]
  rfl

theorem mul_eq_inf_of_disjoint_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : Disjoint (I.support : Set X) (J.support : Set X)) : I * J = I ⊓ J := by
  have hsup : I ⊔ J = ⊤ := by
    rw [← support_eq_bot_iff, support_sup]
    apply Closeds.ext
    show (I.support : Set X) ∩ (J.support : Set X) = ∅
    exact h.inter_eq
  apply IdealSheafData.ext
  funext U
  rw [ideal_mul, Pi.mul_apply, ideal_inf, Pi.inf_apply]
  apply Ideal.mul_eq_inf_of_isCoprime
  rw [Ideal.isCoprime_iff_sup_eq]
  have := congrArg (fun K : X.IdealSheafData => K.ideal U) hsup
  simpa [ideal_sup] using this

end AlgebraicGeometry.K7Impl

end

open AlgebraicGeometry.K7Impl _root_.AlgebraicGeometry.Scheme.IdealSheafData TopologicalSpace in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∃ N₁ : Finset {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _},
      N₁.card = n ∧ (∏ p ∈ N₁, p.1.ker) = (pullback.fst i₁.1 i₂.1).ker ∧
      (∀ p ∈ N₁, Set.range (p.1 ≫ i₁.1).base ⊆ Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base) ∧
      Set.range (pullback.fst i₁.1 i₂.1).base ⊆ ⋃ p ∈ N₁, Set.range p.1.base := by
  classical
  have hfin : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype ↥(pullback i₁.1 i₂.1) := Fintype.ofFinite _
  set f := pullback.fst i₁.1 i₂.1 with hf
  haveI : IsClosedImmersion f := MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  haveI : IsReduced (pullback i₁.1 i₂.1) := hred
  haveI : JacobsonSpace ↥C₁ := LocallyOfFiniteType.jacobsonSpace c₁

  have hRclosed : IsClosed (Set.range f.base) := f.isClosedEmbedding.isClosed_range
  have hRfin : (Set.range f.base).Finite := Set.finite_range _
  have hclpt : ∀ y ∈ Set.range f.base, IsClosed ({y} : Set ↥C₁) := by
    intro y hy
    have key := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := ↥C₁) hRclosed.isLocallyClosed
    have h1 : IsClosed (Set.range f.base ∩ closedPoints ↥C₁) := by
      rw [← Set.biUnion_of_singleton (Set.range f.base ∩ closedPoints ↥C₁)]
      exact (hRfin.inter_of_left _).isClosed_biUnion fun z hz => hz.2
    rw [h1.closure_eq, hRclosed.closure_eq] at key
    have : y ∈ Set.range f.base ∩ closedPoints ↥C₁ := key.symm ▸ hy
    exact this.2

  let pt : ↥(pullback i₁.1 i₂.1) → {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _} := fun z =>
    ⟨pointOfClosedPoint c₁ (f.base z) (hclpt _ ⟨z, rfl⟩), pointOfClosedPoint_comp _ _ _⟩
  have hpt_apply : ∀ z a, (pt z).1.base a = f.base z := fun z a => pointOfClosedPoint_apply _ _ _ a
  have hpt_inj : Function.Injective pt := by
    intro z z' h
    have := congrArg (fun q : {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _} => q.1.base (IsLocalRing.closedPoint k)) h
    simp only [hpt_apply] at this
    exact f.isClosedEmbedding.injective this
  refine ⟨Finset.univ.image pt, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hpt_inj, Finset.card_univ, ← Nat.card_eq_fintype_card, hn]
  ·

    have hker : ∀ z, (pt z).1.ker = vanishingIdeal ⟨{f.base z}, hclpt _ ⟨z, rfl⟩⟩ := fun z => by
      have h := ker_point_eq (pt z).1 (by rw [hpt_apply]; exact hclpt _ ⟨z, rfl⟩)
      rw [h]; congr 1; apply Closeds.ext
      show ({(pt z).1.base (IsLocalRing.closedPoint k)} : Set ↥C₁) = {f.base z}
      rw [hpt_apply]
    have hsupp : ∀ z, (((pt z).1.ker).support : Set ↥C₁) = {f.base z} := fun z => by
      rw [hker]; exact support_vanishingIdeal_of_singleton _ _

    rw [Finset.prod_image fun z _ z' _ h => hpt_inj h]

    have key : ∀ s : Finset ↥(pullback i₁.1 i₂.1),
        (∏ z ∈ s, (pt z).1.ker) = ⨅ z ∈ s, (pt z).1.ker ∧
          ((∏ z ∈ s, (pt z).1.ker).support : Set ↥C₁) = ⋃ z ∈ s, {f.base z} := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [support_top]
      | insert a s ha ih =>
        obtain ⟨ih1, ih2⟩ := ih
        rw [Finset.prod_insert ha]
        have hdisj : Disjoint (((pt a).1.ker).support : Set ↥C₁) (((∏ z ∈ s, (pt z).1.ker).support : Set ↥C₁)) := by
          rw [hsupp, ih2, Set.disjoint_singleton_left]
          simp only [Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
          intro z hz h
          exact ha (f.isClosedEmbedding.injective h ▸ hz)
        refine ⟨?_, ?_⟩
        · rw [mul_eq_inf_of_disjoint_support _ _ hdisj, ih1, Finset.iInf_insert]
        · rw [support_mul]
          show (((pt a).1.ker).support : Set ↥C₁) ∪ ((∏ z ∈ s, (pt z).1.ker).support : Set ↥C₁) = _
          rw [hsupp, ih2, Finset.set_biUnion_insert]
    obtain ⟨k1, -⟩ := key Finset.univ
    rw [k1]

    rw [ker_eq_vanishingIdeal_of_isReduced f]
    simp only [Finset.mem_univ, iInf_true, hker]
    rw [← vanishingIdeal_iSup]
    congr 1
    apply Closeds.ext
    show (↑(⨆ z, (⟨{f.base z}, hclpt _ ⟨z, rfl⟩⟩ : Closeds ↥C₁)) : Set ↥C₁) = closure (Set.range f.base)
    rw [hRclosed.closure_eq, ← Finset.sup_univ_eq_iSup, Closeds.coe_finset_sup]
    ext y
    simp only [Finset.sup_set_eq_biUnion, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨z, -, hz⟩
      have hz' : y ∈ ({f.base z} : Set ↥C₁) := hz
      exact ⟨z, (Set.mem_singleton_iff.mp hz').symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Finset.mem_univ z, show f.base z ∈ ({f.base z} : Set ↥C₁) from Set.mem_singleton _⟩
  · intro p hp
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
    rintro _ ⟨a, rfl⟩
    refine ⟨z, ?_⟩
    show i₁.1.base (f.base z) = i₁.1.base ((pt z).1.base a)
    rw [hpt_apply]
  · rintro _ ⟨z, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨pt z, Finset.mem_image_of_mem _ (Finset.mem_univ z), ⟨IsLocalRing.closedPoint k, hpt_apply z _⟩⟩

end S_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced (solution)
