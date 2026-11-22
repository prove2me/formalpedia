-- Prove2me | solution 1 for Autoconvolutions.Blocks.goodVectors_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:22.793809+00:00
-- url     : https://prove2.me/submissions/709dc5db-ffaf-49a6-9265-3b9bf0992b1a

module
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_Autoconvolutions_Occupancy

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Blocks
variable {ι : Type*} [DecidableEq ι]
namespace Autoconvolutions.Blocks
theorem _root_.solution {I : Finset ι} {k : ℕ} {a : ι → ℕ} (ha : a ∈ goodVectors I k) :
    a ∈ I.piAntidiag k ∧ ∀ i, a i ≤ 1 := by
  classical
  obtain ⟨T,hT,rfl⟩ := mem_map.mp ha
  obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hT
  constructor
  · apply mem_piAntidiag.mpr
    constructor
    · simp only [indicatorVector, Function.Embedding.coeFn_mk, sum_boole, Nat.cast_id,
        Finset.filter_mem_eq_inter, inter_eq_right.mpr hsub, hcard]
    · intro i hi
      by_contra hin
      have hT' : i ∉ T := fun h => hin (hsub h)
      simp [indicatorVector, hT'] at hi
  · intro i
    simp [indicatorVector]
    split <;> decide
end Autoconvolutions.Blocks
