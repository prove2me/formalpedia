-- Prove2me | solution 1 for Auto.aux_overlapLower_le_overlapUpper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:31.700129+00:00
-- url     : https://prove2.me/submissions/355b6af7-595c-4814-8f3d-94fc75b9ebb4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_fin_univ_nonempty

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (u : aux_RVector n) (m : ℕ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ ε) (hεδ : ε ≤ δ) :
    aux_overlapLower hn ε u m ≤ aux_overlapUpper hn ε δ u m := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty := aux_fin_univ_nonempty hn
  change Finset.univ.sup' hne (fun i ↦ (m : ℝ) + ε - u i) ≤
    Finset.univ.inf' hne (fun i ↦ (m : ℝ) + ε + δ - u i)
  have hsup : Finset.univ.sup' hne (fun i ↦ (m : ℝ) + ε - u i) ≤
      (m : ℝ) + ε := by
    apply Finset.sup'_le hne
    intro i hi
    linarith [(hu i).1]
  have hinf : (m : ℝ) + δ ≤
      Finset.univ.inf' hne (fun i ↦ (m : ℝ) + ε + δ - u i) := by
    apply Finset.le_inf' hne
    intro i hi
    linarith [(hu i).2]
  linarith
end Auto
