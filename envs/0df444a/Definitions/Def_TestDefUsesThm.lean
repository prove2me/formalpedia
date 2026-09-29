-- Prove2me | Definitions.Def_TestDefUsesThm
-- name    : TestDefUsesThm
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T18:20:01.403997+00:00
-- url     : https://prove2.me/theorems/84c7ec11-743d-404c-8806-0d8885a80c89
-- title:
--   Def-uses-theorem test
-- statement:
--   Test: a definition importing an already-Proved theorem module.
-- source:
--   test

import Mathlib
import Theorems.Thm_BookProof_BRSTNilpotent_brst_charge_nilpotent
open BookProof.BRSTNilpotent

/-- Test: a definition whose body USES an already-Proved platform theorem. -/
noncomputable def TestDefUsesThm : ℕ := by
  exact 42


