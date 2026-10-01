-- Prove2me | Definitions.Def_Yukon_a9cebfaf25c2bf4c44008ec1
-- name    : Yukon_a9cebfaf25c2bf4c44008ec1
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:30.516201+00:00
-- url     : https://prove2.me/theorems/43ebed1f-37de-476d-bea8-053b76d09acb
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.AffineFactorAggregate6808.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.AffineFactorAggregate6808.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/AffineFactorAggregate6808.lean
--
--   provider-v8:88c199e223dc73261b17d6b7af25793a6b3ed62923df1b629115b29bfa7fe0be
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODo4OGMxOTllMjIzZGM3MzI2MWIxN2Q2YjdhZjI1NzkzYTZiM2VkNjI5MjNkZjFiNjI5MTE1YjI5YmZhN2ZlMGJlIiwiaGFzaCI6IjMwYzc5YTNlZGZjOWY1ODRhZDkyMWMyZWY0M2NlNWI4MWYxMDgyY2FmZjI4OWI0NWQwYjBmODdhMmMwOGU1MWIiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2E5Y2ViZmFmMjVjMmJmNGM0NDAwOGVjMSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic


import Init
set_option backward.isDefEq.respectTransparency.types false
/-! A finite max-plus receipt carries affine single-factor bounds to an entire
factor family. No convexity or monotonicity of the single-factor cost is assumed.
The theorem has no mathematical source assumptions beyond its explicit inputs. -/
namespace ProximityPrize.SubmissionLower.AffineFactorAggregate6808
open scoped BigOperators
set_option autoImplicit false

/-- Each row absorbs one factor into the remaining coordinate budgets. -/
def BellmanRows (Rcap Ycap : ℕ) (b B : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v R V, 1 ≤ r → r + R ≤ Rcap → r + v + R + V ≤ Ycap →
    b r v + B R V ≤ B (r + R) (v + V)

theorem sum_intercepts_le {ι : Type*} [DecidableEq ι]
    (Rcap Ycap : ℕ) (b B : ℕ → ℕ → ℕ)
    (hrows : BellmanRows Rcap Ycap b B)
    (s : Finset ι) (r v : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i)
    (hR : (∑ i ∈ s, r i) ≤ Rcap)
    (hY : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ Ycap) :
    (∑ i ∈ s, b (r i) (v i)) ≤ B (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hRi : r a + (∑ i ∈ s, r i) ≤ Rcap := by
      simpa only [Finset.sum_insert ha] using hR
    have hYi : (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ Ycap := by
      simpa only [Finset.sum_insert ha] using hY
    have hrec := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
      (by omega) (by omega)
    have hrow := hrows (r a) (v a) (∑ i ∈ s, r i) (∑ i ∈ s, v i)
      (hr a (Finset.mem_insert_self a s)) hRi (by omega)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Nat.add_le_add_left hrec _).trans hrow

/-- Single-factor affine receipts imply a bound for every finite factor family. -/
theorem sum_count_le {ι : Type*} [DecidableEq ι]
    (Rcap Ycap slope : ℕ) (b B : ℕ → ℕ → ℕ)
    (hrows : BellmanRows Rcap Ycap b B)
    (s : Finset ι) (r v z count : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i)
    (hR : (∑ i ∈ s, r i) ≤ Rcap)
    (hY : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ Ycap)
    (hcost : ∀ i ∈ s, count i ≤ slope * z i + b (r i) (v i)) :
    (∑ i ∈ s, count i) ≤ slope * (∑ i ∈ s, z i) +
      B (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  calc
    (∑ i ∈ s, count i) ≤ ∑ i ∈ s, (slope * z i + b (r i) (v i)) :=
      Finset.sum_le_sum hcost
    _ = slope * (∑ i ∈ s, z i) + ∑ i ∈ s, b (r i) (v i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add_left (sum_intercepts_le Rcap Ycap b B hrows s r v hr hR hY) _

/-- On a singleton, a strict helper split charges the only factor directly. -/
theorem singleton_helper {ι : Type*} [DecidableEq ι] (a : ι)
    (count helper : ι → ℕ)
    (hsplit : ∃ U : Finset ι, U ⊂ {a} ∧ ∀ i ∈ ({a} : Finset ι) \ U,
      count i ≤ helper i) : count a ≤ helper a := by
  obtain ⟨U, hU, hcount⟩ := hsplit
  have ha : a ∉ U := by
    intro ha
    apply hU.2
    exact Finset.singleton_subset_iff.mpr ha
  exact hcount a (Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self a, ha⟩)







end ProximityPrize.SubmissionLower.AffineFactorAggregate6808


