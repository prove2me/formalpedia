-- Prove2me | solution 1 for AddUN.iUnion_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:33:22.181855+00:00
-- url     : https://prove2.me/submissions/0abe4028-57c8-4f97-b10f-a16ce70c7f58

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_inner_subset

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution (hU : IsOpen U) : ⋃ n, inner U n = U := by
  refine Subset.antisymm (iUnion_subset fun n ↦ inner_subset n) fun x hx ↦ ?_
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU x hx
  refine mem_iUnion.2 ⟨I.sup id + 1, fun y hy ↦ hsub fun i hi ↦ ?_⟩
  rw [hy i (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))]
  exact (hu i hi).2
end AddUN
