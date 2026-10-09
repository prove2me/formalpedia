-- Prove2me | Definitions.Def_eq30RightSlope
-- name    : eq30RightSlope
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T15:39:43.71253+00:00
-- url     : https://prove2.me/theorems/c394dce1-1e8a-48f3-bf2a-feeef25610f0
-- title:
--   eq30RightSlope
-- statement:
--   Automatically extracted helper definition eq30RightSlope from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

/-!
Source-only reduction for `eq30_eventually_below_fare`.  `eq30RightSlope`
tracks the right slope of the pointwise recursive piecewise-affine payoff.
The source-only lemmas below establish pathwise threshold vanishing, a fare
majorant, and the delicate one-step boundary derivatives. Joint measurability
and the expected-revenue DCT assembly remain separate.
-/
noncomputable def eq30RightSlope (f p x : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => if s < x 1 then f 1 else 0
  | k + 2, s =>
      if s < p (k + 1) then eq30RightSlope f p x (k + 1) s
      else if s < p (k + 1) + x (k + 2) then f (k + 2)
      else eq30RightSlope f p x (k + 1) (s - x (k + 2))


