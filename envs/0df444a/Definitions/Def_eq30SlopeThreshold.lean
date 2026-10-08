-- Prove2me | Definitions.Def_eq30SlopeThreshold
-- name    : eq30SlopeThreshold
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T01:08:00.727351+00:00
-- url     : https://prove2.me/theorems/3e126a4e-913c-46a9-999f-133dd38fac22
-- title:
--   eq30SlopeThreshold
-- statement:
--   Automatically extracted helper definition eq30SlopeThreshold from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

def eq30SlopeThreshold (p x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => x 1
  | k + 2 => x (k + 2) + max (p (k + 1)) (eq30SlopeThreshold p x (k + 1))


