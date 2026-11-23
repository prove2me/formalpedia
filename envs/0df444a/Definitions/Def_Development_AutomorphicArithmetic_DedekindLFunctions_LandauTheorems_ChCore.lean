-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
-- name    : Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:19.637581+00:00
-- url     : https://prove2.me/theorems/ed94f7c0-6e3b-4c18-b3b3-e49626b4c7d0
-- title:
--   Ch Core
-- statement:
--   Definitions and structural lemmas for Ch Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
namespace CharacterBalanceMoves
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def e1 (h : H) : E0 × H := (((1 : ZMod 2), (0 : ZMod 2)), h)
def Th (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (b y : ℝ) (u0 t : H) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ s ∈ T2, ∑ ψ : AddChar (E0 × H) ℂ,
    ψ (-(e1 (s + u0 - t))) * ((b : ℂ) * GPsi D ell ψ y)
open Classical in

def vv (Kp : Finset (AddChar (E0 × H) ℂ)) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (c x : ℝ)
    (ψ : AddChar (E0 × H) ℂ) : ℝ :=
  if ψ ∈ Kp then wtA c ψ * (GPsi D ell ψ x).re else -‖GPsi D ell ψ x‖
end CharacterBalanceMoves
end Deduction
end


