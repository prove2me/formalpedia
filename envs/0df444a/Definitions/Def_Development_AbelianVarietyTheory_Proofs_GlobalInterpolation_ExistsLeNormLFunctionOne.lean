-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:23.09035+00:00
-- url     : https://prove2.me/theorems/f04300b3-19fe-4620-900a-3c37a25de06b
-- title:
--   Exists Le Norm LFunction One
-- statement:
--   Definitions and structural lemmas for Exists Le Norm LFunction One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
namespace GlobalTheory.LOneLower
noncomputable def wt (x : ℝ) : ℝ := x⁻¹ - (Real.exp x - 1)⁻¹
end GlobalTheory.LOneLower


