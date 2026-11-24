-- Prove2me | solution 1 for AddUN.exists_clopens_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:18.272748+00:00
-- url     : https://prove2.me/submissions/4b0f4c49-4245-4245-92f3-44bb07c21f2c

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
public import Theorems.Thm_AddUN_exists_clopens_iUnion_eq
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
    {G : Set (ℕ → Bool)} (hG : μ G = 0) :
    ∃ B : ℕ → Clopens (ℕ → Bool), ∑' i, μ (B i) ≠ ∞ ∧
      ∀ x ∈ G, ∃ᶠ i in atTop, x ∈ B i := by
  have hU : ∀ j : ℕ, ∃ U ⊇ G, IsOpen U ∧ μ U ≤ 2⁻¹ ^ j := fun j ↦ by
    simpa [hG] using G.exists_isOpen_le_add μ (ε := 2⁻¹ ^ j) (by simp)
  choose U hGU hUo hUm using hU
  choose D hDU hDm using fun j ↦ exists_clopens_iUnion_eq μ (hUo j)
  refine ⟨fun i ↦ D i.unpair.1 i.unpair.2, ?_, fun x hx ↦ ?_⟩
  · have h1 : ∑' i : ℕ, μ (D i.unpair.1 i.unpair.2) =
        ∑' p : ℕ × ℕ, μ (D p.1 p.2) :=
      (Nat.pairEquiv.symm.tsum_eq fun p : ℕ × ℕ ↦ μ (D p.1 p.2))
    rw [h1, ENNReal.tsum_prod (f := fun j r ↦ μ (D j r))]
    simp_rw [hDm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hUm)
    rw [ENNReal.tsum_geometric]
    simp
  · have hr : ∀ j, ∃ r, x ∈ D j r := fun j ↦ by
      have : x ∈ ⋃ r, (D j r : Set (ℕ → Bool)) := by rw [hDU]; exact hGU j hx
      simpa using this
    choose r hr using hr
    rw [Nat.frequently_atTop_iff_infinite]
    refine infinite_of_injective_forall_mem (f := fun j ↦ Nat.pair j (r j)) (fun a b hab ↦ ?_)
      fun j ↦ ?_
    · exact (Nat.pair_eq_pair.1 hab).1
    · simpa using hr j
end AddUN
