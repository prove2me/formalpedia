-- Prove2me | solution 1 for AddUN.isOpen_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:29.186315+00:00
-- url     : https://prove2.me/submissions/dba72433-c781-4338-a2c3-57f21e9d12a1

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_determined_inner
public import Theorems.Thm_MeasureTheory_isClopen_cylinderOn


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution (n : ℕ) : IsOpen (inner U n) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨cylinderOn (Finset.range n) x,
    fun y hy ↦ determined_inner n (fun i hi ↦ (hy i hi).symm) hx,
    (isClopen_cylinderOn _ _).isOpen, fun _ _ ↦ rfl⟩
end AddUN
