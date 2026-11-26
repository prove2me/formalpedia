-- Prove2me | solution 1 for Auto.aux_discreteAverage_truncate_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:48.178627+00:00
-- url     : https://prove2.me/submissions/cab60ca8-bc25-4eff-954c-566daf29a885

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_mem_localInputSupport
public import Theorems.Thm_Auto_aux_truncate_eq_self_of_mem
public import Theorems.Thm_Auto_aux_discreteAverage_congr_on

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ}
    {B : Finset (Fin n → ℕ)} {L N : ℕ} (hNL : N ≤ L)
    (F : Fin n → (Fin n → ℕ) → ℝ) {k : Fin n → ℕ} (hk : k ∈ B) :
    aux_discreteAverage N
        (fun i ↦ aux_truncate (aux_localInputSupport B L) (F i)) k =
      aux_discreteAverage N F k := by
  apply aux_discreteAverage_congr_on
  intro i m hm
  apply aux_truncate_eq_self_of_mem
  exact aux_mem_localInputSupport hk i
    (lt_of_lt_of_le (Finset.mem_range.mp hm) hNL)
end Auto
