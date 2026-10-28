-- Prove2me | Definitions.Def_Sensitivity213981Formal_MarkedTwoProbability
-- name    : Sensitivity213981Formal_MarkedTwoProbability
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:09:23.559299+00:00
-- url     : https://prove2.me/theorems/2c57a174-7851-4ab2-9137-6a31a526ba44
-- title:
--   Marked Two Probability — sensitivity certificate definitions
-- statement:
--   The definitions for Marked Two Probability in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRefinedMarked.localProbability_weighted_le_two`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MarkedTwoProbability.lean, lines 1–74.

import Definitions.Def_Sensitivity213981Formal_MarkedTwoRows
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundRefinedMarked
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
noncomputable section
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
theorem localProbability_weighted_le_two
    (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M P : Finset V) (q B : ℕ) (hdis : Disjoint A M) (hm : M.card=2)
    (hs : F.support d = markedSupport R A M)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B)
    (u : ℚ) (C : ℕ → ℚ) (hu : 0 ≤  u) (hC : ∀ t ≤  q, 0 ≤  C t)
    (htan : ∀ k <  A.card, ∀ t ≤  q, (rowPatterns t k : ℚ) ≤  C t * u^k) :
    F.localProbability d ≤ 
      ((2 : ℚ)^A.card * headFactor q A.card * u^(A.card.choose 2) /
        (2 : ℚ)^(A.card.choose 2 + M.card * A.card)) *
      ∏ x ∈ A, orientationWeight q C (outOn R M x).card := by
  by_cases hadm : ∀ x ∈ A, (outOn R M x).card ≤  q
  · let H : ℚ := ∏ x : A,
      (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)
    let CP : ℚ := ∏ x : A, C (q-(outOn R M x.val).card)
    have hcount : F.localProbability d ≤ 
        (2 : ℚ)^A.card * (H * headFactor q A.card) /
          (2 : ℚ)^(markedSupport R A M).card := by
      apply (localProbability_le F d R A M P q B hs hb).trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := Nat.mul_le_mul_left (2^A.card) (pattern_product_le R hloop htour A M q hm)
      have hh' : ((2^A.card * ∏ i : A ⊕ M,
          rowPatterns (rowBudget R A M q i) (markedRows R A M i).card : ℕ) : ℚ) ≤ 
          ((2^A.card * ((∏ x : A, rowPatterns (q-(outOn R M x.val).card)
            (outOn R A x.val).card) * headFactor q A.card) : ℕ) : ℚ) := by
        exact_mod_cast hh
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_prod,H] using hh'
    have htanprod : H ≤  u^(A.card.choose 2) * CP :=
      tangent_ordinary_product R hloop htour A M q u C hu hC htan
    have hprodw : (∏ x ∈ A, orientationWeight q C (outOn R M x).card) =
        (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) * CP := by
      have hp := orientationWeight_product R A M q C hadm
      rw [Finset.prod_coe_sort (s := A)
        (f := fun x : V => orientationWeight q C (outOn R M x).card)] at hp
      exact hp
    have hsupport := markedSupport_card_add R hloop htour A M hdis
    have hpow : (2 : ℚ)^(A.card.choose 2 + M.card*A.card) =
        (2 : ℚ)^(markedSupport R A M).card *
          (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) := by
      rw [← pow_add,hsupport]
    calc
      F.localProbability d ≤ 
          (2 : ℚ)^A.card * (H * headFactor q A.card) /
            (2 : ℚ)^(markedSupport R A M).card := hcount
      _ ≤  (2 : ℚ)^A.card *
          ((u^(A.card.choose 2) * CP) * headFactor q A.card) /
            (2 : ℚ)^(markedSupport R A M).card := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htanprod (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        rw [hprodw,hpow]
        field_simp <;> ring
  · push_neg at hadm
    obtain ⟨x,hx,hq⟩ := hadm
    rw [marked_localProbability_eq_zero_of_degree F d R A M P q B hb x hx hq]
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun z _ => orientationWeight_nonneg q C hC _

end
end ThreeBoundRefinedMarked


end
end Sensitivity213981Formal


