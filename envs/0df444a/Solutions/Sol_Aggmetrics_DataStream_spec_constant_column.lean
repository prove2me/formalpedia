-- Prove2me | solution 1 for Aggmetrics.DataStream.spec_constant_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:55.527458+00:00
-- url     : https://prove2.me/submissions/cd253a04-498a-4fec-881d-83c56e5da303

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) (γ : ℝ)
    (hπ : ∑ k, π k = 1) (hj : π j ≠ 1) (hcol : ∀ k, k ≠ j → c k j = γ) :
    specFormula π c j = 1 - γ := by
  have hden : ∑ k ∈ univ.erase j, π k = 1 - π j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hπ]
  have h1j : (1 - π j) ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
  unfold specFormula
  rw [Finset.sum_congr rfl (fun k hk => by rw [hcol k (Finset.ne_of_mem_erase hk)]),
    ← Finset.sum_mul, ← Finset.sum_div, hden]
  field_simp
end Aggmetrics.DataStream
