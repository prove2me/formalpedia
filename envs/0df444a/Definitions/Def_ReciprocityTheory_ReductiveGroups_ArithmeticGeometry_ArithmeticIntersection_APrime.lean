-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:20.451636+00:00
-- url     : https://prove2.me/theorems/52053a88-4382-425d-b339-9c619464a9c7
-- title:
--   APrime
-- statement:
--   Definitions and structural lemmas for APrime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
def interp {VW : Type*} (k i : ℕ) (x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j = 0 then x₂ else if j < 1 + 2 * i then x₁ else if j < 1 + 2 * k then x₂ else a
def consWord {VW : Type*} (k i : ℕ) (x x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j < 2 then x else if j = 2 then x₂ else if j < 3 + 2 * i then x₁ else
    if j < 1 + 2 * k then x₂ else a
end ReciprocityTheory.ChartRestriction.G.AI


