-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:40.199736+00:00
-- url     : https://prove2.me/theorems/6861b01c-1678-4778-a789-4697ac67f2b2
-- title:
--   Twenty Five Mul Small Constant
-- statement:
--   Definitions and structural lemmas for Twenty Five Mul Small Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TwentyFiveMulSmallConstant.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
def rr (a : ℕ) : ℝ := 16 * Real.exp ((a : ℝ) + 1)
def eps (a : ℕ) : ℝ := 1 / rr a
def th (a : ℕ) : ℝ := 1 / (2 * Real.log (rr a))
def kap (a : ℕ) (D : ℝ) : ℝ := th a * eps a ^ 2 / (a * (D + 1))
def c0 (a : ℕ) : ℝ := 1 / (25 * rr a)
def E0 (a : ℕ) (D : ℝ) : ℝ := Real.exp (a * D / eps a ^ 2)
def j0 (a : ℕ) : ℝ := 1 + a / eps a ^ 2
def GG (a : ℕ) (CP cZ cS c₁ : ℝ) : ℝ :=
  (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * c₁ * Real.exp (j0 a * Real.log (rr a)) + 1 + rr a + rr a ^ 2
def K0 (a : ℕ) (D CP cZ cS c₁ : ℝ) : ℝ := E0 a D * GG a CP cZ cS c₁ / th a
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds


