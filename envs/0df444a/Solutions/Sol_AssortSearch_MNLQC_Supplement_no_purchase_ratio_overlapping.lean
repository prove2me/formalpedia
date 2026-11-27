-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.no_purchase_ratio_overlapping
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:06.446919+00:00
-- url     : https://prove2.me/submissions/9c1124f2-6b18-43a1-a5d9-d74a463f4159

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

/-- The relative preference of the no-purchase variant in the overlapping assortment model
(pp. 21–22): for an assortment of depth `x < n` and a product variant `i` in it,
`q_0^so(x) / q_i^so(x) = (q_0^m(x) + ∑_{j ≤ x} q_j^m(x) H(Ū(x), x)) / (q_i^m(x) (1 − H(Ū(x), x)))`. -/
theorem solution {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hμ : 0 < μ) (hb : 0 < b) (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (x : ℕ) (hx : x < n) (i : Fin n) (hi : i.val < x) :
    demandNoPurchaseOv μ b v v0 x / demandOv μ b v v0 x i =
      (AssortSearch.HeurEq.shareNoPurchase v v0 x +
          ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j *
            AssortSearch.Cannibal.H μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
              (popularSet n x)) /
        (share v v0 (popularSet n x) i *
          (1 - AssortSearch.Cannibal.H μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
            (popularSet n x))) := by
              classical
              have hproper : popularSet n x ≠ Finset.univ := by
                intro heq
                have hmem : (⟨x, hx⟩ : Fin n) ∈ popularSet n x := by
                  rw [heq]
                  exact Finset.mem_univ _
                simpa [popularSet] using hmem
              have hden : (∑ j ∈ popularSet n x, v j) + v0 ≠ 0 := by
                have hsum : 0 ≤ ∑ j ∈ popularSet n x, v j :=
                  Finset.sum_nonneg (fun j _ => le_of_lt (hv j))
                exact ne_of_gt (add_pos_of_nonneg_of_pos hsum hv0)
              have hnorm : AssortSearch.HeurEq.shareNoPurchase v v0 x +
                  ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j = 1 := by
                simp only [AssortSearch.HeurEq.shareNoPurchase, share]
                rw [← Finset.sum_div, ← add_div]
                apply (div_eq_one_iff_eq hden).2
                ring
              have hdemand : ∀ j : Fin n, demandOv μ b v v0 x j =
                  share v v0 (popularSet n x) j *
                    (1 - AssortSearch.Cannibal.H μ
                      (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
                      (popularSet n x)) := by
                intro j
                simp [demandOv, AssortSearch.FullAssort.demandSO, hproper]
              have hno : demandNoPurchaseOv μ b v v0 x =
                  AssortSearch.HeurEq.shareNoPurchase v v0 x +
                    ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j *
                      AssortSearch.Cannibal.H μ
                        (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
                        (popularSet n x) := by
                simp only [demandNoPurchaseOv, hdemand]
                rw [← Finset.sum_mul, ← Finset.sum_mul]
                nlinarith [hnorm]
              rw [hno, hdemand]
