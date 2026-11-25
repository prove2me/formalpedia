-- Prove2me | Definitions.Def_SZ_Cells
-- name    : SZ_Cells
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:53:05.583743+00:00
-- url     : https://prove2.me/theorems/e933c493-7749-48ed-932d-bbf354cace67
-- title:
--   Cells
-- statement:
--   Definitions and structural lemmas for Cells, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_SZ_not_isSquare_of_bounded

set_option autoImplicit false
namespace SZ
theorem s5_lb : (2.236 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem s5_ub : Real.sqrt 5 < 2.2361 := by
  have h : Real.sqrt 5 < Real.sqrt (2.2361 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2361)] at h
theorem s6_lb : (2.449 : ℝ) < Real.sqrt 6 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem s6_ub : Real.sqrt 6 < 2.4495 := by
  have h : Real.sqrt 6 < Real.sqrt (2.4495 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.4495)] at h
theorem s7_lb : (2.645 : ℝ) < Real.sqrt 7 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem s7_ub : Real.sqrt 7 < 2.6458 := by
  have h : Real.sqrt 7 < Real.sqrt (2.6458 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.6458)] at h
theorem s8_lb : (2.828 : ℝ) < Real.sqrt 8 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem s8_ub : Real.sqrt 8 < 2.8285 := by
  have h : Real.sqrt 8 < Real.sqrt (2.8285 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.8285)] at h
noncomputable def slice5 : Slice where
  m := 5
  p := 2
  e := 4
  U := 1 + Real.sqrt 5
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s5_lb; push_cast; linarith
  gap := by have := s5_ub; push_cast; linarith
noncomputable def slice6 : Slice where
  m := 6
  p := 2
  e := 4
  U := 4 * (1 + Real.sqrt 6) / 5
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s6_lb; push_cast; linarith
  gap := by have := s6_ub; push_cast; linarith
noncomputable def slice7 : Slice where
  m := 7
  p := 2
  e := 6
  U := 1 + Real.sqrt 7
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s7_lb; push_cast; linarith
  gap := by have := s7_ub; push_cast; linarith
noncomputable def slice8 : Slice where
  m := 8
  p := 2
  e := 6
  U := 6 * (1 + Real.sqrt 8) / 7
  three_le := by norm_num
  not_square := not_isSquare_of_bounded (by norm_num) (by decide)
  two_le_p := by norm_num
  p_le_e := by norm_num
  p_dvd_e := by norm_num
  e_le := by norm_num
  U_def := by push_cast; ring
  p_le_U := by have := s8_lb; push_cast; linarith
  gap := by have := s8_ub; push_cast; linarith
end SZ


