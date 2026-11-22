-- Prove2me | solution 1 for Autoconvolutions.plateau_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:02.513666+00:00
-- url     : https://prove2.me/submissions/0f623184-4613-4dfe-bc88-b40ed664131c

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_auto_step_memLp
public import Theorems.Thm_Autoconvolutions_auto_step_L2_sq
public import Theorems.Thm_Autoconvolutions_auto_step_plateau


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (S : Finset ℤ)
    (H : ℤ → ℝ) (hl : ∀ k ∈ S, convCoeff d p k = H k)
    (hr : ∀ k ∈ S, convCoeff d p (k+1) = H k) :
    ∑ k ∈ S, (H k)^2 ≤ (eLpNorm (auto (step d p)) 2 volume).toReal ^ 2 := by
  classical
  rw [auto_step_L2_sq]
  let I (k : ℤ) := Ico ((k:ℝ)+1) ((k:ℝ)+2)
  have hi := (auto_step_memLp d p 2).integrable_sq
  have disj : Set.Pairwise (↑S) (fun i j => Disjoint (I i) (I j)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro x ⟨hx₁,hx₂⟩ ⟨hy₁,hy₂⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
      linarith
    · have : (j:ℝ)+1 ≤ i := by exact_mod_cast (show j+1 ≤ i by omega)
      linarith
  have unit (k : ℤ) (hk : k ∈ S) : (∫ x in I k, auto (step d p) x ^ 2) = (H k)^2 := by
    calc
      _ = ∫ _ in I k, (H k)^2 := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        change auto (step d p) x ^ 2 = (H k)^2
        rw [auto_step_plateau _ _ _ _ (hl k hk) (hr k hk) x ⟨hx.1,hx.2.le⟩]
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ico]
        have hh : (k:ℝ)+2-((k:ℝ)+1) = 1 := by ring
        simp [hh]
  calc
    _ = ∫ x in ⋃ k ∈ S, I k, auto (step d p) x ^ 2 := by
      rw [integral_biUnion_finset S (fun _ _ => measurableSet_Ico) disj
        (fun _ _ => hi.integrableOn)]
      exact Finset.sum_congr rfl fun k hk => (unit k hk).symm
    _ ≤ _ := setIntegral_le_integral hi (.of_forall fun x => sq_nonneg _)
end Autoconvolutions
