-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:56.497577+00:00
-- url     : https://prove2.me/theorems/cf3e7821-2707-4383-9d37-12b689e46ce9
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean

module
public import Mathlib.MeasureTheory.Measure.Map
set_option autoImplicit true
@[expose] public section
@[expose] public section
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite
noncomputable abbrev FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Fintype (Set.range X) := hX.finite.fintype
noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω
  → G) [hX : FiniteRange X] : Finset G :=
    @Set.toFinset _ _ hX.fintype
instance {Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)
example {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X := by infer_instance
lemma finiteRange_of_finset {Ω G : Type*} (f : Ω → G) (A : Finset G) (h : ∀ ω, f ω ∈ A) :
    FiniteRange f := by
  constructor
  apply Set.Finite.subset (Finset.finite_toSet A)
  intro y hy
  simp only [Set.mem_range] at hy
  rcases hy with ⟨ω, rfl⟩
  exact h ω
lemma FiniteRange.range {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Set.range X = FiniteRange.toFinset X := by simp [FiniteRange.toFinset]
lemma FiniteRange.mem {Ω G : Type*} (X : Ω → G) [FiniteRange X] (ω : Ω) :
    X ω ∈ FiniteRange.toFinset X := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range, exists_apply_eq_apply]
@[simp]
lemma FiniteRange.mem_iff {Ω G : Type*} (X : Ω → G) [FiniteRange X] (x : G) :
    x ∈ FiniteRange.toFinset X ↔ ∃ ω, X ω = x := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range]
instance {Ω G : Type*} (c : G) : FiniteRange (fun _ : Ω ↦ c) := by
  apply finiteRange_of_finset _ { c }
  simp
instance {Ω G H : Type*} (X : Ω → G) (f : G
  → H) [hX : FiniteRange X] : FiniteRange (f ∘ X) where
  finite := (Set.range_comp f X) ▸ Set.Finite.image f hX.finite
instance {Ω Ω' G : Type*} (X : Ω → G) (f : Ω'
  → Ω) [hX : FiniteRange X] : FiniteRange (X ∘ f) := by
  apply finiteRange_of_finset _ (FiniteRange.toFinset X)
  intro ω
  exact FiniteRange.mem X (f ω)
instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX : FiniteRange X] [hY : FiniteRange Y] :
    FiniteRange fun ω ↦ (X ω, Y ω) where
  finite := (hX.finite.prod hY.finite).subset (Set.range_pair_subset ..)
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.mul {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange (X * Y) := by
  change FiniteRange ((fun p ↦ p.1 * p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.mul' {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω * Y ω := FiniteRange.mul ..
@[to_additive /-- The difference of functions of finite range, has finite range. -/]
instance FiniteRange.div {Ω G : Type*} (X Y : Ω → G) [Div G]
    [hX : FiniteRange X] [hY : FiniteRange Y] : FiniteRange (X/Y) := by
  change FiniteRange ((fun p ↦ p.1 / p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.div' {Ω G : Type*} (X Y : Ω → G) [Div G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω / Y ω := FiniteRange.div ..
@[to_additive /-- The negation of a function of finite range, has finite range. -/]
instance FiniteRange.inv {Ω G : Type*} (X : Ω → G) [Inv G] [hX : FiniteRange X] :
    FiniteRange X⁻¹ := by
  change FiniteRange ((fun p ↦ p⁻¹) ∘ X)
  infer_instance
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.inv' {Ω G : Type*} (X : Ω → G) [Inv G] [FiniteRange X] :
    FiniteRange fun ω ↦ (X ω)⁻¹ := FiniteRange.inv _
@[to_additive /-- The multiple of a function of finite range by a constant, has finite range. -/]
instance FiniteRange.zpow {Ω G : Type*} (X : Ω → G) [Pow G ℤ] [hX : FiniteRange X] (n : ℤ) :
    FiniteRange (X ^ n) := by
  change FiniteRange ((· ^ n) ∘ X)
  infer_instance
@[to_additive /-- The multiple of a function of finite range by a constant, has finite range. -/]
instance FiniteRange.zpow' {Ω G : Type*} (X : Ω → G) [Pow G ℤ] [FiniteRange X] (n : ℤ) :
    FiniteRange fun ω ↦ X ω ^ n := FiniteRange.zpow ..
@[to_additive /-- The sum of a finite number of functions with finite range, has finite range. -/]
instance FiniteRange.finprod {Ω G I : Type*} [CommMonoid G] {s : Finset I} (X : I → Ω → G)
    [∀ i, FiniteRange (X i)] :
    FiniteRange (∏ i ∈ s, X i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    change FiniteRange (fun _ ↦ 1)
    infer_instance
  | @insert k s hk IH =>
    classical
    have h_eq : ∏ j ∈ insert k s, X j = X k * ∏ j ∈ s, X j := Finset.prod_insert hk
    suffices h : FiniteRange (X k * ∏ j ∈ s, X j) from by
      convert h
      exact h_eq
    exact FiniteRange.mul (X k) (∏ j ∈ s, X j)
open MeasureTheory


