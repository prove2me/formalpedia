-- Prove2me | solution 1 for AddUN.exists_clopens_limsup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:04.324805+00:00
-- url     : https://prove2.me/submissions/d41b0fe4-6e58-4af8-b32d-ada31d2e8b2f

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
public import Theorems.Thm_AddUN_exists_clopens_summable
public import Theorems.Thm_AddUN_exists_between_of_strictMono
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    {G : Set (ℕ → Bool)} (hG : μ G = 0) {ε : ℕ → ℝ≥0∞}
    (hε : ∀ n, ε n ≠ 0) :
    ∃ C : ℕ → Clopens (ℕ → Bool), (∀ n, μ (C n) ≤ ε n) ∧
      ∀ x ∈ G, ∃ᶠ n in atTop, x ∈ C n := by
  obtain ⟨B, hB, hGB⟩ := exists_clopens_summable μ hG
  have htail : ∀ n, ∀ᶠ k in atTop, ∑' i, μ (B (i + k)) ≤ ε n := fun n ↦
    (ENNReal.tendsto_sum_nat_add _ hB).eventually_le_const (pos_iff_ne_zero.2 (hε n))
  obtain ⟨φ, hφ, hφε⟩ := extraction_forall_of_eventually htail
  have hCc : ∀ n, IsClopen (⋃ i ∈ Finset.Ico (φ n) (φ (n + 1)), (B i : Set (ℕ → Bool))) :=
    fun n ↦ (Finset.Ico (φ n) (φ (n + 1))).finite_toSet.isClopen_biUnion fun i _ ↦ (B i).isClopen
  refine ⟨fun n ↦ ⟨_, hCc n⟩, fun n ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [Clopens.coe_mk]
    refine (measure_biUnion_finset_le _ _).trans (le_trans ?_ (hφε n))
    rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [add_comm (φ n)]
    exact ENNReal.sum_le_tsum _
  · rw [frequently_atTop]
    intro N
    obtain ⟨i, hi, hxi⟩ := (frequently_atTop.1 (hGB x hx)) (φ N)
    obtain ⟨n, hNn, hn1, hn2⟩ := exists_between_of_strictMono hφ hi
    refine ⟨n, hNn, ?_⟩
    change x ∈ ⋃ i ∈ Finset.Ico (φ n) (φ (n + 1)), (B i : Set (ℕ → Bool))
    exact mem_biUnion (Finset.mem_Ico.2 ⟨hn1, hn2⟩) hxi
end AddUN
