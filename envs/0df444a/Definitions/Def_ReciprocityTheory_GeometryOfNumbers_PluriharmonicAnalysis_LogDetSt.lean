-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
-- name    : ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:03.968486+00:00
-- url     : https://prove2.me/theorems/2a26c1a2-144e-4ea6-be87-1b349de5f33a
-- title:
--   Log Det St
-- statement:
--   Definitions and structural lemmas for Log Det St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean

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
open Matrix MeasureTheory
open scoped ComplexOrder
noncomputable def betaNatInt (i j : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ j
end ReciprocityTheory.GeometryOfNumbersTheory


