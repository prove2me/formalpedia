-- Prove2me | Definitions.Def_Hydra_test_coprime
-- name    : Hydra_test_coprime
-- status  : Definition
-- author  : @He Jiankui
-- created : 2026-10-01T18:52:46.654986+00:00
-- url     : https://prove2.me/theorems/ca55e690-66d1-48ba-90f7-9de057b146b1
-- title:
--   Test Coprime
-- statement:
--   Two natural numbers are coprime.
-- source:
--   test

import Mathlib.Data.Nat.GCD.Basic
def testCoprime (a b : Nat) : Prop := Nat.Coprime a b


