-- Prove2me | Definitions.Def_NewtonianLipschitz_CubicCandidate
-- name    : NewtonianLipschitz_CubicCandidate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:19:43.445187+00:00
-- url     : https://prove2.me/theorems/1af99c1b-2d4e-4a0b-b008-8e22f42516d6
-- title:
--   Cubic Candidate
-- statement:
--   Definitions and structural lemmas for Cubic Candidate, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
def stationaryCubic (y : ℝ) : ℝ :=
  2 * y ^ 3 - 8 * y ^ 2 - 4 * y + 1
noncomputable def candidateCoefficient (y : ℝ) : ℝ :=
  (2 + 6 * y - 2 * y ^ 2) / (Real.sqrt (1 + 2 * y ^ 2)) ^ 5
theorem stationaryCubic_pos_at_nine_fiftieths :
    0 < stationaryCubic (9 / 50 : ℝ) := by
  norm_num [stationaryCubic]
theorem stationaryCubic_neg_at_one_fifth :
    stationaryCubic (1 / 5 : ℝ) < 0 := by
  norm_num [stationaryCubic]
theorem stationaryCubic_exists_root_bracket :
    ∃ t : ℝ, (9 / 50 : ℝ) ≤ t ∧ t ≤ 1 / 5 ∧
      stationaryCubic t = 0 := by
  have hc : Continuous stationaryCubic := by
    unfold stationaryCubic
    fun_prop
  have hz :
      (0 : ℝ) ∈ Set.Icc
        (stationaryCubic (1 / 5 : ℝ))
        (stationaryCubic (9 / 50 : ℝ)) :=
    ⟨le_of_lt stationaryCubic_neg_at_one_fifth,
      le_of_lt stationaryCubic_pos_at_nine_fiftieths⟩
  obtain ⟨t, ht, hpt⟩ :=
    (intermediate_value_Icc'
      (by norm_num : (9 / 50 : ℝ) ≤ 1 / 5)
      hc.continuousOn) hz
  exact ⟨t, ht.1, ht.2, hpt⟩
noncomputable def candidateCriticalPoint : ℝ :=
  Classical.choose stationaryCubic_exists_root_bracket
end NewtonianLipschitz


