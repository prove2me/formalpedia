-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:05.222905+00:00
-- url     : https://prove2.me/theorems/1158c418-8183-4895-9681-20c5ec8111f7
-- title:
--   Chi Eight No Real Zero Hypothesis
-- statement:
--   Definitions and structural lemmas for Chi Eight No Real Zero Hypothesis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChiEightNoRealZeroHypothesis.lean

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
namespace Formalism.LFunctionChainParameters.LChain6.Chi8
open Formalism.ZF.ComplexPowerDifferenceIntegral
def chi : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
def g (s : ℂ) (n : ℕ) : ℂ :=
  ((8 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 3 : ℝ) : ℂ) ^ (-s)
    - (((8 * (n : ℝ) + 5 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 7 : ℝ) : ℂ) ^ (-s))
def G (s : ℂ) : ℂ := ∑' n, g s n
def tm (s : ℂ) (n : ℕ) : ℂ := LSeries.term (fun n : ℕ => chi (n : ZMod 8)) s n
def gr (σ : ℝ) (n : ℕ) : ℝ :=
  (8 * (n : ℝ) + 1) ^ (-σ) - (8 * (n : ℝ) + 3) ^ (-σ) - ((8 * (n : ℝ) + 5) ^ (-σ) - (8 * (n : ℝ) + 7) ^ (-σ))
end Formalism.LFunctionChainParameters.LChain6.Chi8
namespace Formalism.LFunctionChainParameters.LChain6
end Formalism.LFunctionChainParameters.LChain6


