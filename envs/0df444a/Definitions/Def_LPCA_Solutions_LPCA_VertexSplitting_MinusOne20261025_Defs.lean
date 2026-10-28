-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:30:28.374029+00:00
-- url     : https://prove2.me/theorems/17b98f7c-ef03-41b9-85ab-92ecafcd6905
-- title:
--   Vertex Splitting — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for vertex splitting, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_VertexSplitting.lean, selected declarations in lines 13–165; source SHA-256 3b0b6e9f06753fd93695c51b68d332f9d2e7586ec2c66c22e04c20881dac6d15; exact-source certificate Sapelo2 job 49311470.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

theorem criterion_zero_degree
    (K : Complex V) (i : V) (F : Finset V) (a : V → ℤ)
    (hF : i ∉ F) (ha : a i = 0) :
    LocalizationCriterion K F a ↔ LocalizationCriterion (deletion K i) F a := by
  constructor
  · rintro ⟨hn, hface⟩
    refine ⟨hn, Finset.mem_filter.mpr ⟨hface, ?_⟩⟩
    simp [positiveSupport, ha, hF]
  · rintro ⟨hn, hface⟩
    exact ⟨hn, (Finset.mem_filter.mp hface).1⟩

theorem nonnegative_update_iff
    (i : V) (F : Finset V) (a : V → ℤ) (ha : 0 ≤ a i) :
    (∀ j : V, j ∉ F → 0 ≤ a j) ↔
      ∀ j : V, j ∉ F → 0 ≤ Function.update a i 0 j := by
  constructor
  · intro h j hj
    by_cases hji : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hji] using h j hj
  · intro h j hj
    by_cases hji : j = i
    · subst j
      exact ha
    · simpa [Function.update_of_ne hji] using h j hj

theorem positive_support_update
    (i : V) (a : V → ℤ) (ha : 0 < a i) :
    positiveSupport a = insert i (positiveSupport (Function.update a i 0)) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [positiveSupport, ha]
  · simp [positiveSupport, Function.update_of_ne hji, hji]

theorem criterion_positive_degree
    (K : Complex V) (i : V) (F : Finset V) (a : V → ℤ)
    (hF : i ∉ F) (ha : 0 < a i) :
    LocalizationCriterion K F a ↔
      LocalizationCriterion (link K {i}) F (Function.update a i 0) := by
  let b := Function.update a i 0
  have hi : i ∉ positiveSupport b := by simp [positiveSupport, b]
  have hsupport : positiveSupport a ∪ F = (positiveSupport b ∪ F) ∪ {i} := by
    rw [positive_support_update i a ha]
    ext j
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hdisjoint : Disjoint (positiveSupport b ∪ F) {i} := by
    simp [hi, hF]
  constructor
  · rintro ⟨hn, hface⟩
    have hbig : (positiveSupport b ∪ F) ∪ {i} ∈ K.faces := hsupport ▸ hface
    refine ⟨(nonnegative_update_iff i F a (le_of_lt ha)).mp hn, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨K.down_closed hbig Finset.subset_union_left, hdisjoint, hbig⟩
  · rintro ⟨hn, hface⟩
    have hparts := Finset.mem_filter.mp hface
    exact ⟨(nonnegative_update_iff i F a (le_of_lt ha)).mpr hn,
      hsupport.symm ▸ hparts.2.2⟩

def zeroDegreeBasisEquiv
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i = 0) :
    CechBasis K T a p ≃ CechBasis (deletion K i) T a p where
  toFun F := ⟨F.1, F.2.1, F.2.2.1,
    (criterion_zero_degree K i F.1 a (fun hiF => hT (F.2.1 hiF)) ha).mp F.2.2.2⟩
  invFun F := ⟨F.1, F.2.1, F.2.2.1,
    (criterion_zero_degree K i F.1 a (fun hiF => hT (F.2.1 hiF)) ha).mpr F.2.2.2⟩
  left_inv F := Subtype.ext rfl
  right_inv F := Subtype.ext rfl

def positiveDegreeBasisEquiv
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : 0 < a i) :
    CechBasis K T a p ≃ CechBasis (link K {i}) T (Function.update a i 0) p where
  toFun F := ⟨F.1, F.2.1, F.2.2.1,
    (criterion_positive_degree K i F.1 a (fun hiF => hT (F.2.1 hiF)) ha).mp F.2.2.2⟩
  invFun F := ⟨F.1, F.2.1, F.2.2.1,
    (criterion_positive_degree K i F.1 a (fun hiF => hT (F.2.1 hiF)) ha).mpr F.2.2.2⟩
  left_inv F := Subtype.ext rfl
  right_inv F := Subtype.ext rfl



noncomputable def zeroDegreeTermEquiv
    (k : Type u) [Field k]
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i = 0) :
    (CechBasis K T a p → k) ≃ₗ[k] (CechBasis (deletion K i) T a p → k) :=
  LinearEquiv.funCongrLeft k k (zeroDegreeBasisEquiv K i T a p hT ha).symm

noncomputable def positiveDegreeTermEquiv
    (k : Type u) [Field k]
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : 0 < a i) :
    (CechBasis K T a p → k) ≃ₗ[k]
      (CechBasis (link K {i}) T (Function.update a i 0) p → k) :=
  LinearEquiv.funCongrLeft k k (positiveDegreeBasisEquiv K i T a p hT ha).symm





theorem zeroDegree_differential_compatibility
    (k : Type u) [Field k] (coefficient : Finset V → Finset V → k)
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i = 0) (x : CechBasis K T a p → k) :
    zeroDegreeTermEquiv k K i T a (p + 1) hT ha
        (basisDifferential k coefficient K T a p x) =
      basisDifferential k coefficient (deletion K i) T a p
        (zeroDegreeTermEquiv k K i T a p hT ha x) := by
  ext G
  change (∑ F : CechBasis K T a p, coefficient F.1 G.1 * x F) =
    ∑ F : CechBasis (deletion K i) T a p, coefficient F.1 G.1 *
      x ((zeroDegreeBasisEquiv K i T a p hT ha).symm F)
  exact (Equiv.sum_comp (zeroDegreeBasisEquiv K i T a p hT ha).symm
    (fun F : CechBasis K T a p => coefficient F.1 G.1 * x F)).symm

theorem positiveDegree_differential_compatibility
    (k : Type u) [Field k] (coefficient : Finset V → Finset V → k)
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : 0 < a i) (x : CechBasis K T a p → k) :
    positiveDegreeTermEquiv k K i T a (p + 1) hT ha
        (basisDifferential k coefficient K T a p x) =
      basisDifferential k coefficient (link K {i}) T (Function.update a i 0) p
        (positiveDegreeTermEquiv k K i T a p hT ha x) := by
  ext G
  change (∑ F : CechBasis K T a p, coefficient F.1 G.1 * x F) =
    ∑ F : CechBasis (link K {i}) T (Function.update a i 0) p, coefficient F.1 G.1 *
      x ((positiveDegreeBasisEquiv K i T a p hT ha).symm F)
  exact (Equiv.sum_comp (positiveDegreeBasisEquiv K i T a p hT ha).symm
    (fun F : CechBasis K T a p => coefficient F.1 G.1 * x F)).symm

end LPCA


