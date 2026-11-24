-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleModuleCechExactness
-- name    : AlgebraicGeometry_EtaleModuleCechExactness
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-24T23:11:14.07229+00:00
-- url     : https://prove2.me/theorems/daa0b732-dd5c-45dc-bbae-ebab944c1e08
-- title:
--   Čech exactness for injective étale module sheaves
-- statement:
--   The underlying abelian sheaf of an injective module sheaf is acyclic over every étale object. The associated Čech cochains are exact in positive degrees for every singleton cover.
-- source:
--   Stacks Project, Theorem 59.19.2, https://stacks.math.columbia.edu/tag/03OU.

import Definitions.Def_AlgebraicGeometry_EtaleInjectiveModuleRestriction
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalAcyclicity
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1600000

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- When the two adjacent Ext groups of the middle object vanish, the
connecting map is an additive equivalence. -/
def connectingEquiv (F : C) (q : ℕ)
    [Subsingleton (Ext S.X₂ F q)] [Subsingleton (Ext S.X₂ F (q + 1))] :
    Ext S.X₁ F q ≃+ Ext S.X₃ F (q + 1) := by
  let hq : 1 + q = q + 1 := Nat.add_comm 1 q
  let δ := hS.extClass.precomp F hq
  refine AddEquiv.ofBijective δ ⟨?_, ?_⟩
  · apply (AddMonoidHom.ker_eq_bot_iff δ).mp
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS F x hq hx
    have : y = 0 := Subsingleton.elim _ _
    rw [this, Ext.comp_zero] at hy
    exact hy.symm
  · intro x
    have hx : (Ext.mk₀ S.g).comp x (zero_add (q + 1)) = 0 := Subsingleton.elim _ _
    exact Ext.contravariant_sequence_exact₃ hS F x hx hq

/-- The connecting equivalence commutes with maps on the coefficients. -/
theorem connectingEquiv_natural {F G : C} (f : F ⟶ G) (q : ℕ)
    [Subsingleton (Ext S.X₂ F q)] [Subsingleton (Ext S.X₂ F (q + 1))]
    [Subsingleton (Ext S.X₂ G q)] [Subsingleton (Ext S.X₂ G (q + 1))]
    (x : Ext S.X₁ F q) :
    connectingEquiv hS G q (x.comp (Ext.mk₀ f) (add_zero q)) =
      (connectingEquiv hS F q x).comp (Ext.mk₀ f) (add_zero (q + 1)) :=
  (Ext.comp_assoc_of_third_deg_zero hS.extClass x (Ext.mk₀ f) (Nat.add_comm 1 q)).symm

/-- The boundary from homomorphisms in the contravariant Ext sequence. -/
def homBoundary (F : C) : (S.X₁ ⟶ F) →+ Ext S.X₃ F 1 :=
  (hS.extClass.precomp F (rfl : 1 + 0 = 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom

theorem homBoundary_exact (F : C) :
    Function.Exact (fun y : S.X₂ ⟶ F => S.f ≫ y) (homBoundary hS F) := by
  intro x
  constructor
  · intro hx
    change hS.extClass.comp (Ext.mk₀ x) (rfl : 1 + 0 = 1) = 0 at hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS F (Ext.mk₀ x) rfl hx
    refine ⟨Ext.addEquiv₀ y, (Ext.mk₀_bijective _ _).injective ?_⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    change hS.extClass.comp (Ext.mk₀ (S.f ≫ y)) (rfl : 1 + 0 = 1) = 0
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ y)

theorem homBoundary_surjective (F : C) [Subsingleton (Ext S.X₂ F 1)] :
    Function.Surjective (homBoundary hS F) := by
  intro x
  have hx : (Ext.mk₀ S.g).comp x (zero_add 1) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ hS F x hx (rfl : 1 + 0 = 1)
  refine ⟨Ext.addEquiv₀ a, ?_⟩
  change hS.extClass.comp (Ext.mk₀ (Ext.addEquiv₀ a)) (rfl : 1 + 0 = 1) = x
  rwa [Ext.mk₀_addEquiv₀_apply]

theorem homBoundary_natural {F G : C} (f : F ⟶ G) (x : S.X₁ ⟶ F) :
    homBoundary hS G (x ≫ f) = (homBoundary hS F x).comp (Ext.mk₀ f) (add_zero 1) := by
  change hS.extClass.comp (Ext.mk₀ (x ≫ f)) (rfl : 1 + 0 = 1) =
    (hS.extClass.comp (Ext.mk₀ x) (rfl : 1 + 0 = 1)).comp (Ext.mk₀ f) (add_zero 1)
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

namespace Resolution

variable (R : Resolution (C := C))

/-- The section differential as a morphism of abelian groups. -/
def cochainHom (F : C) (n : ℕ) : (R.terms n ⟶ F) →+ (R.terms (n + 1) ⟶ F) where
  toFun := R.cochain F n
  map_zero' := by simp [cochain]
  map_add' x y := by simp [cochain, Preadditive.comp_add]

/-- A homomorphism from a cycle object pulls back to a cocycle. -/
def homToCocycle (F : C) (n : ℕ) :
    (R.cycles n ⟶ F) →+ (R.cochainHom F n).ker where
  toFun x := ⟨R.projection n ≫ x, by
    change R.cochain F n (R.projection n ≫ x) = 0
    unfold cochain
    rw [← Category.assoc (R.inclusion n), R.zero, zero_comp, comp_zero]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp only [AddSubgroup.coe_add, Preadditive.comp_add])

/-- A cocycle factors uniquely through the cycle object. -/
def homCocycleEquiv (F : C) (n : ℕ) :
    (R.cycles n ⟶ F) ≃+ (R.cochainHom F n).ker := by
  have : Epi (R.projection n) := (R.shortExact n).epi_g
  have : Epi (R.projection (n + 1)) := (R.shortExact (n + 1)).epi_g
  refine AddEquiv.ofBijective (R.homToCocycle F n) ⟨?_, ?_⟩
  · intro a b h
    exact (cancel_epi (R.projection n)).mp (congrArg Subtype.val h)
  · intro a
    have ha : R.inclusion n ≫ a.val = 0 := by
      apply (cancel_epi (R.projection (n + 1))).mp
      rw [comp_zero]
      exact a.property
    let T := CokernelCofork.ofπ a.val ha
    let hC := (R.shortExact n).gIsCokernel
    exact ⟨hC.desc T, Subtype.ext (hC.fac T WalkingParallelPair.one)⟩

omit [HasExt C] in
private theorem homCocycleEquiv_inclusion (F : C) (n : ℕ) (x : R.terms n ⟶ F) :
    (R.homCocycleEquiv F (n + 1) (R.inclusion n ≫ x)).val = R.cochain F n x := rfl

/-- The map from positive-degree cocycles to degree-one Ext on the
preceding cycle object. Its kernel consists of the coboundaries. -/
def cocycleBoundary (F : C) (n : ℕ) : (R.cochainHom F (n + 1)).ker →+ Ext (R.cycles n) F 1 :=
  (homBoundary (R.shortExact n) F).comp (R.homCocycleEquiv F (n + 1)).symm.toAddMonoidHom

theorem cocycleBoundary_eq_zero_iff (F : C) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) : R.cocycleBoundary F n x = 0 ↔
      ∃ y : R.terms n ⟶ F, R.cochain F n y = x.val := by
  let e := R.homCocycleEquiv F (n + 1)
  change homBoundary (R.shortExact n) F (e.symm x) = 0 ↔ _
  rw [homBoundary_exact (R.shortExact n) F (e.symm x)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hy' : R.inclusion n ≫ y = e.symm x := hy
    rw [← R.homCocycleEquiv_inclusion F, hy']
    exact congrArg Subtype.val (e.apply_symm_apply x)
  · rintro ⟨y, hy⟩
    refine ⟨y, e.injective ?_⟩
    rw [AddEquiv.apply_symm_apply]
    exact Subtype.ext hy

theorem cocycleBoundary_surjective (F : C) (n : ℕ) [Subsingleton (Ext (R.terms n) F 1)] :
    Function.Surjective (R.cocycleBoundary F n) :=
  (homBoundary_surjective (R.shortExact n) F).comp (R.homCocycleEquiv F (n + 1)).symm.surjective

/-- A coefficient morphism takes a cocycle to a cocycle by postcomposition. -/
def cocyclePost {F G : C} (f : F ⟶ G) (n : ℕ) (x : (R.cochainHom F n).ker) :
    (R.cochainHom G n).ker := ⟨x.val ≫ f, by
  change R.cochain G n (x.val ≫ f) = 0
  have hx : R.cochain F n x.val = 0 := x.property
  rw [show R.cochain G n (x.val ≫ f) = R.cochain F n x.val ≫ f by
    simp only [cochain, Category.assoc], hx, zero_comp]⟩

private theorem homCocycleEquiv_symm_post {F G : C} (f : F ⟶ G) (n : ℕ)
    (x : (R.cochainHom F n).ker) :
    (R.homCocycleEquiv G n).symm (R.cocyclePost f n x) =
      (R.homCocycleEquiv F n).symm x ≫ f := by
  apply (R.homCocycleEquiv G n).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  change x.val ≫ f = R.projection n ≫ (R.homCocycleEquiv F n).symm x ≫ f
  rw [← Category.assoc]
  exact congrArg (· ≫ f) (congrArg Subtype.val ((R.homCocycleEquiv F n).apply_symm_apply x)).symm

/-- The map from cocycles to degree-one Ext is natural in the coefficients. -/
theorem cocycleBoundary_natural {F G : C} (f : F ⟶ G) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) :
    R.cocycleBoundary G n (R.cocyclePost f (n + 1) x) =
      (R.cocycleBoundary F n x).comp (Ext.mk₀ f) (add_zero 1) := by
  change homBoundary (R.shortExact n) G
    ((R.homCocycleEquiv G (n + 1)).symm (R.cocyclePost f (n + 1) x)) = _
  rw [R.homCocycleEquiv_symm_post, homBoundary_natural]
  rfl

private def reindexExt (F : C) {i j : ℕ} (h : i = j) :
    Ext (R.cycles i) F 1 ≃+ Ext (R.cycles j) F 1 := by
  subst j
  exact AddEquiv.refl _

private theorem reindexExt_natural {F G : C} (f : F ⟶ G) {i j : ℕ} (h : i = j)
    (x : Ext (R.cycles i) F 1) :
    R.reindexExt G h (x.comp (Ext.mk₀ f) (add_zero 1)) =
      (R.reindexExt F h x).comp (Ext.mk₀ f) (add_zero 1) := by
  subst j
  rfl

/-- Positive-degree cohomology is transported to an Ext group of degree one
by cutting a resolution whose terms are acyclic for the coefficients. -/
def degreeOneEquiv (F : C) (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1))) :
    ∀ n j : ℕ, Ext (R.cycles (j + n)) F 1 ≃+ Ext (R.cycles j) F (n + 1)
  | 0, _ => AddEquiv.refl _
  | n + 1, j => by
      let : Subsingleton (Ext (R.terms j) F (n + 1)) := h j n
      let : Subsingleton (Ext (R.terms j) F (n + 1 + 1)) := h j (n + 1)
      exact (R.reindexExt F (show j + (n + 1) = (j + 1) + n by omega)).trans
        ((degreeOneEquiv F h n (j + 1)).trans (connectingEquiv (R.shortExact j) F (n + 1)))

/-- The iterated connecting equivalence is natural in the coefficient object. -/
theorem degreeOneEquiv_natural {F G : C} (f : F ⟶ G)
    (hF : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1)))
    (hG : ∀ j q, Subsingleton (Ext (R.terms j) G (q + 1))) (n j : ℕ)
    (x : Ext (R.cycles (j + n)) F 1) :
    R.degreeOneEquiv G hG n j (x.comp (Ext.mk₀ f) (add_zero 1)) =
      (R.degreeOneEquiv F hF n j x).comp (Ext.mk₀ f) (add_zero (n + 1)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      simp only [degreeOneEquiv, AddEquiv.trans_apply]
      rw [reindexExt_natural, ih, connectingEquiv_natural]

/-- The edge map from positive-degree cocycles for an acyclic resolution
to the corresponding Ext group of the augmentation object. -/
def positiveCocycleBoundary (F : C) (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1)))
    (n : ℕ) : (R.cochainHom F (n + 1)).ker →+ Ext (R.cycles 0) F (n + 1) :=
  ((R.reindexExt F (Nat.zero_add n).symm).trans (R.degreeOneEquiv F h n 0)).toAddMonoidHom.comp
    (R.cocycleBoundary F n)

theorem positiveCocycleBoundary_surjective (F : C)
    (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1))) (n : ℕ) :
    Function.Surjective (R.positiveCocycleBoundary F h n) := by
  let : Subsingleton (Ext (R.terms n) F 1) := h n 0
  exact ((R.reindexExt F (Nat.zero_add n).symm).trans (R.degreeOneEquiv F h n 0)).surjective.comp
    (R.cocycleBoundary_surjective F n)

theorem positiveCocycleBoundary_eq_zero_iff (F : C)
    (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1))) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) : R.positiveCocycleBoundary F h n x = 0 ↔
      ∃ y : R.terms n ⟶ F, R.cochain F n y = x.val := by
  change (R.degreeOneEquiv F h n 0) (R.reindexExt F (Nat.zero_add n).symm
    (R.cocycleBoundary F n x)) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff, R.cocycleBoundary_eq_zero_iff]

theorem positiveCocycleBoundary_natural {F G : C} (f : F ⟶ G)
    (hF : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1)))
    (hG : ∀ j q, Subsingleton (Ext (R.terms j) G (q + 1))) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) :
    R.positiveCocycleBoundary G hG n (R.cocyclePost f (n + 1) x) =
      (R.positiveCocycleBoundary F hF n x).comp (Ext.mk₀ f) (add_zero (n + 1)) := by
  change (R.degreeOneEquiv G hG n 0) (R.reindexExt G (Nat.zero_add n).symm
    (R.cocycleBoundary G n (R.cocyclePost f (n + 1) x))) = _
  rw [R.cocycleBoundary_natural, R.reindexExt_natural, R.degreeOneEquiv_natural]
  rfl

end Resolution

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {U V : C} (f : V ⟶ U)

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

variable [J.HasSheafCompose (forget AddCommGrpCat.{v})]

private def cechSectionsEquiv (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) :
    ((freeCechResolution f J h).terms j ⟶ F) ≃+
      F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))) :=
  PhilipponSheafCohomology.representedSectionsAddEquiv J F _

private theorem cechSectionsEquiv_cochain (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) (s : (freeCechResolution f J h).terms j ⟶ F) :
    cechSectionsEquiv f J h F (j + 1) ((freeCechResolution f J h).cochain F j s) =
      sectionCechD f J F j (cechSectionsEquiv f J h F j s) := by
  have hd : (freeCechResolution f J h).projection (j + 1) ≫ (freeCechResolution f J h).inclusion j =
      ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (PhilipponSheafCohomology.freeOn J).map ((Arrow.mk f).cechNerve.δ i) := by
    unfold freeCechResolution
    rw [Resolution.ofExact_differential, augmentedD,
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    rfl
  rw [Resolution.cochain, ← Category.assoc, hd, sum_comp]
  simp only [zsmul_comp, map_sum, map_zsmul, sectionCechD, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact PhilipponSheafCohomology.representedSections_restrict J ((Arrow.mk f).cechNerve.δ i) s

/-- Čech cochains are exact in positive degrees when the target and all
terms of the Čech nerve are acyclic for the coefficient sheaf. -/
theorem sectionCechD_exact_of_acyclic [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (h : Sieve.generate (Presieve.singleton f) ∈ J U) (F : Sheaf J AddCommGrpCat.{v})
    (hU : ∀ q, Subsingleton (F.H' (q + 1) U))
    (hN : ∀ n q, Subsingleton (F.H' (q + 1) ((Arrow.mk f).cechNerve.obj (op ⦋n⦌))))
    (j : ℕ) : Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1)) := by
  let R := freeCechResolution f J h
  let e := cechSectionsEquiv f J h F
  have termsAcyclic (n q : ℕ) : Subsingleton (Ext (R.terms n) F (q + 1)) := hN n q
  let : Subsingleton (Ext (R.cycles 0) F (j + 1)) := hU j
  intro y
  constructor
  · intro hy
    let z : (R.cochainHom F (j + 1)).ker := ⟨(e (j + 1)).symm y, by
      change R.cochain F (j + 1) ((e (j + 1)).symm y) = 0
      apply (e (j + 2)).injective
      rw [cechSectionsEquiv_cochain, AddEquiv.apply_symm_apply, hy, map_zero]⟩
    obtain ⟨x, hx⟩ := (R.positiveCocycleBoundary_eq_zero_iff F termsAcyclic j z).mp
      (Subsingleton.elim _ _)
    refine ⟨e j x, ?_⟩
    rw [← cechSectionsEquiv_cochain, hx]
    exact (e (j + 1)).apply_symm_apply y
  · rintro ⟨x, rfl⟩
    have hz : R.cochain F (j + 1) (R.cochain F j ((e j).symm x)) = 0 := by
      unfold Resolution.cochain
      rw [← Category.assoc (R.inclusion (j + 1)), R.zero, zero_comp, comp_zero]
    have hw := congrArg (e (j + 2)) hz
    rwa [cechSectionsEquiv_cochain, cechSectionsEquiv_cochain, AddEquiv.apply_symm_apply, map_zero] at hw

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponExtComparison

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {Q : C} {P : D} (p : P ⟶ R.obj Q)

/-- Apply an exact functor to Ext, then precompose with the comparison map. -/
def comparison (M : C) (n : ℕ) : Ext Q M n →+ Ext P (R.obj M) n :=
  ((Ext.mk₀ p).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom Q M n)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

theorem comparison_post {M N : C} (a : M ⟶ N) (n : ℕ) (x : Ext Q M n) :
    comparison R p N n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (comparison R p M n x).comp (Ext.mk₀ (R.map a)) (add_zero n) := by
  rw [comparison_comp, Ext.mapExactFunctor_mk₀]

theorem comparison_zero_bijective (M : C)
    (h : Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a)) :
    Function.Bijective (comparison R p M 0) := by
  have hz : (comparison R p M 0 : Ext Q M 0 → Ext P (R.obj M) 0) =
      fun x => Ext.mk₀ (p ≫ R.map (Ext.addEquiv₀ x)) := by
    funext x
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Q M).surjective x
    rw [show Ext.addEquiv₀ (Ext.mk₀ a) = a from Ext.addEquiv₀.apply_symm_apply a]
    exact comparison_mk₀ R p a
  rw [hz]
  exact (Ext.mk₀_bijective _ _).comp (h.comp Ext.addEquiv₀.bijective)

/-- A class of coefficients admits comparison in all degrees if each class
on either side can be killed by a monomorphism with cokernel in the class. -/
theorem comparison_bijective_of_effacement (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (left : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext Q M (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ i) (add_zero (n + 1)) = 0)
    (right : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext P (R.obj M) (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ (R.map i)) (add_zero (n + 1)) = 0)
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact comparison_zero_bijective R p M (h M hM)
  | succ n ih =>
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        obtain ⟨J, i, hi, hJ, hQ, hkill⟩ := left M hM n x
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x hkill (n₀ := n) rfl
        have hzero : (comparison R p S.X₃ n y).comp hSR.extClass rfl = 0 := by
          rw [← comparison_boundary R p hS n y, hy]
          exact hx'
        obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₃ P hSR _ rfl hzero
        obtain ⟨z, hz⟩ := (ih S.X₂ hJ).surjective z'
        have hyz : z.comp (Ext.mk₀ S.g) (add_zero n) = y := (ih S.X₃ hQ).injective (by
          rw [comparison_post, hz]
          exact hz')
        rw [← hy, ← hyz, Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      · intro x'
        obtain ⟨J, i, hi, _, hQ, hkill⟩ := right M hM n x'
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x' hkill (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃ hQ).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

/-- Acyclic embeddings give the class-by-class effacement criterion. -/
theorem comparison_bijective_of_acyclic_embeddings (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (emb : ∀ M : C, B M → ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
      ∀ n : ℕ, Subsingleton (Ext Q J (n + 1)) ∧ Subsingleton (Ext P (R.obj J) (n + 1)))
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  apply comparison_bijective_of_effacement R p B h _ _ n M hM
  · intro M hM q x
    obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
    exact ⟨J, i, hi, hJ, hQ, (hA q).1.elim _ _⟩
  · intro M hM q x
    obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
    exact ⟨J, i, hi, hJ, hQ, (hA q).2.elim _ _⟩

/-- A Hom comparison extends to all Ext degrees when the exact functor
also preserves injectives. -/
theorem comparison_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (h : ∀ M : C, Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (n : ℕ) (M : C) : Function.Bijective (comparison R p M n) := by
  refine comparison_bijective_of_acyclic_embeddings R p (fun _ => True) (fun M _ => h M) ?_ n M trivial
  intro A _
  refine ⟨Injective.under A, Injective.ι A, inferInstance, trivial, trivial, fun q => ?_⟩
  let : Injective (R.obj (Injective.under A)) := R.injective_obj_of_injective inferInstance
  exact ⟨⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩,
    ⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩⟩
end PhilipponExtComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped Simplicial
open PhilipponCech
open PhilipponModuleEtaleNeighborhoodRestriction (along restrict restrictionIso)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleModuleSkyscrapers (underlying underlying_H_succ)
open PhilipponSheafCohomology (freeOn representedSections representedSections_restrict
  representedSections_map terminalComparison)


namespace PhilipponEtaleModuleCech

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Cohomology over an object of the small étale site is the cohomology
of the sheaf restricted to that object's small étale site. -/
def objectComparison {X : Scheme.{u}} (U : X.Etale) (F : Ab X) (q : ℕ) :
    F.H' q U ≃+ ((restrict U.hom).obj F).H q := by
  let Y := U.left
  let g := U.hom
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal
  let e : (along g).obj T ≅ U := MorphismProperty.Over.isoMk (Iso.refl Y) (by simp [T, along, g])
  let L := restrict g
  let Q := (freeOn X.smallEtaleTopology).obj U
  let P := (freeOn Y.smallEtaleTopology).obj T
  let s := representedSections X.smallEtaleTopology Q ((along g).obj T)
    ((freeOn X.smallEtaleTopology).map e.hom)
  let a : P ⟶ L.obj Q := (representedSections Y.smallEtaleTopology (L.obj Q) T).symm s
  have h (M : Ab X) : Function.Bijective (fun b : Q ⟶ M => a ≫ L.map b) := by
    let r := representedSections Y.smallEtaleTopology (L.obj M) T
    let d := (M.obj.mapIso e.op).addCommGroupIsoToAddEquiv
    let t := representedSections X.smallEtaleTopology M U
    have hfun : (fun b : Q ⟶ M => a ≫ L.map b) = r.symm ∘ d ∘ t := by
      funext b
      apply r.injective
      rw [Function.comp_apply, Equiv.apply_symm_apply]
      change representedSections Y.smallEtaleTopology (L.obj M) T (a ≫ L.map b) =
        M.obj.map e.hom.op (representedSections X.smallEtaleTopology M U b)
      rw [representedSections_map]
      unfold a
      rw [Equiv.apply_symm_apply, ← representedSections_restrict]
      exact (representedSections_map X.smallEtaleTopology b _ _).symm
    rw [hfun]
    exact r.symm.bijective.comp (d.bijective.comp t.bijective)
  let : L.Additive := { map_add := rfl }
  let : (pullbackSheaves g).IsLeftAdjoint := (pullbackAdjunction g).isLeftAdjoint
  let : PreservesFiniteLimits L := preservesFiniteLimits_of_natIso (restrictionIso g).symm
  let : PreservesFiniteColimits L := preservesFiniteColimits_of_natIso (restrictionIso g).symm
  exact (AddEquiv.ofBijective (PhilipponExtComparison.comparison L a F q)
    (PhilipponExtComparison.comparison_bijective L a h q F)).trans
    (terminalComparison Y.smallEtaleTopology hT (L.obj F) q).symm

/-- The underlying abelian sheaf of an injective module sheaf is acyclic
over every object of the small étale site. -/
theorem subsingleton_H' {X : Scheme.{u}} {R : Type u} [Ring R]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) [Injective J] (U : X.Etale) (q : ℕ) :
    Subsingleton ((underlying.obj J).H' (q + 1) U) := by
  let Y := U.left
  let g : Y ⟶ X := U.hom
  let : Etale g := U.prop
  let L := (along g).sheafPushforwardContinuous (ModuleCat.{u} R)
    Y.smallEtaleTopology X.smallEtaleTopology
  let : L.PreservesInjectiveObjects := PhilipponModuleEtaleNeighborhoodRestriction.restriction_preservesInjectiveObjects g
  let : Injective (L.obj J) := L.injective_obj_of_injective inferInstance
  let h := underlying_H_succ (L.obj J) q
  let e := objectComparison U (underlying.obj J) (q + 1)
  exact ⟨fun x y => e.injective (h.elim (e x) (e y))⟩

/-- A covering arrow has exact Čech cochains with the underlying abelian
coefficients of an injective module sheaf. -/
theorem sectionCechD_exact {X : Scheme.{u}} {U V : X.Etale} (a : V ⟶ U)
    (h : Sieve.generate (Presieve.singleton a) ∈ X.smallEtaleTopology U)
    {R : Type u} [Ring R] (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) [Injective J] (n : ℕ) :
    Function.Exact (sectionCechD a X.smallEtaleTopology (underlying.obj J) n)
      (sectionCechD a X.smallEtaleTopology (underlying.obj J) (n + 1)) :=
  sectionCechD_exact_of_acyclic a X.smallEtaleTopology h (underlying.obj J)
    (subsingleton_H' J U) (fun j => subsingleton_H' J ((Arrow.mk a).cechNerve.obj (op ⦋j⦌))) n

end PhilipponEtaleModuleCech

end

end


