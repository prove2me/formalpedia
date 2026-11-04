-- Prove2me | solution 1 for AIMInventory.Known.cost_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:32:00.275987+00:00
-- url     : https://prove2.me/submissions/4832a841-d5b9-4b38-80c1-1f16fc4a7c31

import Definitions.Def_AIMInventory_Known_AIM
open MeasureTheory
open scoped NNReal
open AIMInventory.Known LostSalesOrderUpTo.Asymptotic

theorem solution (P : CappedBaseStock.DemandLaw) (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (yhat y : ℝ) (hyhat : 0 ≤ yhat) (hle : yhat ≤ y) :
    Q P h b y - Q P h b yhat ≤ h * (y - yhat) := by
  have hy : 0 ≤ y := hyhat.trans hle
  have holding_int (z : ℝ) : Integrable (fun d : ℝ≥0 => max (z - (d : ℝ)) 0) P.law :=
    ((integrable_const z).sub P.finiteMean).sup (integrable_const 0)
  have short_int (z : ℝ) : Integrable (fun d : ℝ≥0 => max ((d : ℝ) - z) 0) P.law :=
    (P.finiteMean.sub (integrable_const z)).sup (integrable_const 0)
  have hhold :
      (∫ d : ℝ≥0, max (y - (d : ℝ)) 0 ∂P.law) ≤
      (∫ d : ℝ≥0, max (yhat - (d : ℝ)) 0 ∂P.law) + (y - yhat) := by
    have hm := integral_mono (holding_int y)
      ((holding_int yhat).add (integrable_const (y - yhat)))
      (show ∀ d : ℝ≥0, max (y - (d : ℝ)) 0 ≤ max (yhat - (d : ℝ)) 0 + (y - yhat) from by
        intro d
        apply max_le
        · have := le_max_left (yhat - (d : ℝ)) 0
          linarith
        · have := le_max_right (yhat - (d : ℝ)) 0
          linarith)
    simp only [Pi.add_apply] at hm
    rw [integral_add (holding_int yhat) (integrable_const (y - yhat))] at hm
    simpa using hm
  have hshort :
      (∫ d : ℝ≥0, max ((d : ℝ) - y) 0 ∂P.law) ≤
      (∫ d : ℝ≥0, max ((d : ℝ) - yhat) 0 ∂P.law) :=
    integral_mono (short_int y) (short_int yhat)
      (fun d => max_le_max (by linarith) le_rfl)
  unfold Q backorderCost expectedHolding expectedShortfall
  rw [Real.coe_toNNReal y hy, Real.coe_toNNReal yhat hyhat]
  have := mul_le_mul_of_nonneg_left hhold hh.le
  have := mul_le_mul_of_nonneg_left hshort hb.le
  nlinarith

#print axioms solution
