-- Prove2me | solution 1 for AME125.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:42.199249+00:00
-- url     : https://prove2.me/submissions/d9dbdb2f-92ec-4c29-8b20-618058657193

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState

set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ i, f i = ∑ i : Fin m, f (leftIndex hm i) + ∑ j : Fin (n - m), f (rightIndex hm j) := by
  have e : m + (n - m) = n := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add]
  rfl
end AME125
