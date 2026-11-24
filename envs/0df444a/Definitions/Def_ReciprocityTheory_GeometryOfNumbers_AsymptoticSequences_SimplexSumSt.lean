-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
-- name    : ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:15.679988+00:00
-- url     : https://prove2.me/theorems/e5bfe038-a902-4923-96cc-94e5bfd91b2b
-- title:
--   Simplex Sum St
-- statement:
--   Definitions and structural lemmas for Simplex Sum St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open Filter Asymptotics Finset
namespace SimplexSum
def S (i j n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, (p.1 : ℝ) ^ i * (p.2 : ℝ) ^ j
end SimplexSum
end ReciprocityTheory.GeometryOfNumbersTheory


