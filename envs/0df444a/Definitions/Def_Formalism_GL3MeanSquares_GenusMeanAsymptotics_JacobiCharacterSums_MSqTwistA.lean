-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:45.884795+00:00
-- url     : https://prove2.me/theorems/f34fcc79-3c68-4519-831f-b5e163058f16
-- title:
--   MSq Twist A
-- statement:
--   Definitions and structural lemmas for MSq Twist A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
def clsB (m₀ s a₀ : ℕ) : Finset ℕ :=
  (range (m₀ * s)).filter (fun b => b % m₀ = a₀ % m₀ ∧ b.Coprime s)
def smallCnt (X : ℝ) (M b : ℕ) : ℕ :=
  (((Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).filter (fun p => p % M = b)).card
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds


