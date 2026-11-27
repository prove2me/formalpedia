-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.iia_overlapping
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:57.111822+00:00
-- url     : https://prove2.me/submissions/eaaf9d31-18e9-44da-89ab-c19e31f853ea

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

open AssortSearch
open AssortSearch.MNLQC
open AssortSearch.MNLQC.Supplement

/-- IIA among product variants in the overlapping assortment model (p. 21):
`q_i^so(x) / q_j^so(x) = v_i / v_j` for product variants `i, j` of the assortment of depth `x`. -/
theorem solution {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hμ : 0 < μ) (hb : 0 < b) (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (x : ℕ) (i j : Fin n) (hi : i.val < x) (hj : j.val < x) :
    demandOv μ b v v0 x i / demandOv μ b v v0 x j = v i / v j := by
      unfold demandOv AssortSearch.FullAssort.demandSO
      have hS : 0 < ∑ k ∈ popularSet n x, v k + v0 := by
        have := Finset.sum_nonneg (fun k (_ : k ∈ popularSet n x) => (hv k).le)
        linarith
      have hvj := hv j
      have hH : AssortSearch.Cannibal.H μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
          (popularSet n x) < 1 := by
        unfold AssortSearch.Cannibal.H
        rw [← Real.exp_zero, Real.exp_lt_exp]
        have hl : 0 < AssortSearch.Cannibal.lam μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) := by
          unfold AssortSearch.Cannibal.lam; positivity
        have : 0 < v0 + ∑ k ∈ popularSet n x, v k := by linarith
        have := mul_pos hl this
        linarith
      have h1 : (1 - AssortSearch.Cannibal.H μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
          (popularSet n x)) ≠ 0 := by linarith
      unfold share
      split_ifs
      · field_simp
      · field_simp
