-- Prove2me | Definitions.Def_eq30NextPayoff
-- name    : eq30NextPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T01:08:12.074096+00:00
-- url     : https://prove2.me/theorems/9ce2ef24-6479-4bc5-87e2-3b4d1cd6bf98
-- title:
--   eq30NextPayoff
-- statement:
--   Automatically extracted helper definition eq30NextPayoff from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

/-! A one-step payoff model matching the recursive branches of `revenue`:
below protection it inherits the old payoff, between protection and the new
capacity it is affine with the new fare, and above capacity it inherits the
old payoff at the shifted seat count. -/
noncomputable def eq30NextPayoff (g : ℝ → ℝ) (p x fare s : ℝ) : ℝ :=
  if s < p then g s
  else if s < p + x then (s - p) * fare + g p
  else x * fare + g (s - x)


