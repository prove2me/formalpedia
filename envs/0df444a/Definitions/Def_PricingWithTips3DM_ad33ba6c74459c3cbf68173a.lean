-- Prove2me | Definitions.Def_PricingWithTips3DM_ad33ba6c74459c3cbf68173a
-- name    : PricingWithTips3DM_ad33ba6c74459c3cbf68173a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:24:46.850691+00:00
-- url     : https://prove2.me/theorems/eb467221-2ef9-4041-a50b-b124fe3bfb09
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_43a72f26d14262efda381584
import Definitions.Def_PricingWithTips3DM_016f4b89ca40933af432d715
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# 34.3 NP-Completeness and Reducibility

CLRS §34.3: polynomial-time reducibility and the definitions of NP-hard and
NP-complete languages.

Main results:

- Definition `PolyTimeReducible`: `L₁ ≤_P L₂` — a polynomial-time computable
  reduction maps `L₁` into `L₂`.
- Definition `NPHard`: every polynomially verifiable language reduces to `L`.
- Definition `NPComplete`: `L ∈ NP` and `L` is NP-hard.
- Theorem `PolyTimeReducible.trans`: `≤_P` is transitive (via the composition
  of polynomial-time machines).
- Theorems `PolyTimeDecidable.of_reducible`, `NPHard.of_reducible`, and
  `NPComplete.of_reducible`: reductions transport decidability and hardness.
- Theorems `NPComplete.verifiable` and `NPComplete.hard`: direct projections
  from NP-completeness.
-/


