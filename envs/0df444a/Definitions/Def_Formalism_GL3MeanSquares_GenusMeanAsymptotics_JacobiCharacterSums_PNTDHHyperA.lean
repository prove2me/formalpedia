-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:11.48856+00:00
-- url     : https://prove2.me/theorems/f82aae6f-318c-451d-bd28-8c9e97e8be2d
-- title:
--   PNTDHHyper A
-- statement:
--   Definitions and structural lemmas for PNTDHHyper A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperA.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
def cS (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ)
def cT (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) * (Real.log b : ℂ) / (b : ℂ)
def cF (N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, (∑ d ∈ n.divisors, χ (d : ZMod q)) / (n : ℂ)
def hH (k : ℕ) : ℝ := ∑ a ∈ Ioc 0 k, ((a : ℝ))⁻¹
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp


