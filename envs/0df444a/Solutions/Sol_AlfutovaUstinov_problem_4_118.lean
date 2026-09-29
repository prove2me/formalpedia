-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_118
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:08.298961+00:00
-- url     : https://prove2.me/submissions/d1db2302-c761-4f20-be32-a90502a2a646

import Mathlib


theorem solution : 5 ^ 102 % 103 = 1 ∧ 3 ^ 104 % 103 = 9 := by
  constructor <;> decide
