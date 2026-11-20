-- Prove2me | solution 1 for Aggmetrics.DataStream.spec_joint_eq_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:13.712776+00:00
-- url     : https://prove2.me/submissions/0a9fc533-58d8-4e1b-ab52-575f274824bd

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m)
    (hπ : ∑ k, π k = 1) (hrow : ∀ k, ∑ l, c k l = 1) (hj : π j ≠ 1) :
    specJoint π c j = specFormula π c j := by
  have hden : ∑ k ∈ univ.erase j, π k = 1 - π j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hπ]
  have hnum : ∀ k, ∑ l ∈ univ.erase j, π k * c k l = π k * (1 - c k j) := fun k => by
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j), hrow k]
  unfold specJoint specFormula
  rw [hden, Finset.sum_congr rfl (fun k _ => hnum k), Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => by ring)
end Aggmetrics.DataStream
