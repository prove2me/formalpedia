-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
-- name    : GroundTheory_LocalFields_LocalZetaChar
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:32.750683+00:00
-- url     : https://prove2.me/theorems/f5288605-7b41-534d-aa20-20a002aa49b9
-- title:
--   Local Zeta Char
-- statement:
--   Definitions and structural lemmas for Local Zeta Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Decomposition
end Decomposition
section QuasiCharacter
variable (χ : Kˣ →* ℂˣ)
def IsUnramifiedChar : Prop := unitFiltrationUnits K 0 ≤ χ.ker
def quasiCharConductor : ℕ := sInf {n : ℕ | unitFiltrationUnits K n ≤ χ.ker}
def quasiCharExponent : ℝ := -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖
variable {χ}
variable (hχ : Continuous χ)
include hχ
end QuasiCharacter
section ShellIntegral
variable [MeasurableSpace K] [BorelSpace K] {χ : Kˣ →* ℂˣ}
end ShellIntegral
end GroundTheory.LocalField


