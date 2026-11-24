-- Prove2me | solution 1 for AddUN.exists_between_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:53.652671+00:00
-- url     : https://prove2.me/submissions/69ad86f9-4b05-4bbb-b377-d544d273ec42

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution {φ : ℕ → ℕ} (hφ : StrictMono φ) {N i : ℕ} (hi : φ N ≤ i) :
    ∃ n, N ≤ n ∧ φ n ≤ i ∧ i < φ (n + 1) := by
  have hN : N ≤ i := (hφ.le_apply).trans hi
  refine ⟨Nat.findGreatest (fun m ↦ φ m ≤ i) i, Nat.le_findGreatest hN hi,
    Nat.findGreatest_spec (P := fun m ↦ φ m ≤ i) hN hi, ?_⟩
  by_contra hcon
  have hle : Nat.findGreatest (fun m ↦ φ m ≤ i) i + 1 ≤ i :=
    (hφ.le_apply).trans (not_lt.1 hcon)
  exact Nat.findGreatest_is_greatest (P := fun m ↦ φ m ≤ i) (Nat.lt_succ_self _) hle
    (not_lt.1 hcon)
end AddUN
