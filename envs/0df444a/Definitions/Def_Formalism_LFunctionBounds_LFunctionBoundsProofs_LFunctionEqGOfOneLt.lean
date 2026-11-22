-- Prove2me | Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
-- name    : Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:07.020077+00:00
-- url     : https://prove2.me/theorems/4ebbb4ed-fa05-4078-aa44-4b90dc776827
-- title:
--   LFunction Eq GOf One Lt
-- statement:
--   Definitions and structural lemmas for LFunction Eq GOf One Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
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
namespace Formalism.FX
namespace LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
def dterm (s : ℂ) (n : ℕ) : ℂ := Ap χ n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))
def G (s : ℂ) : ℂ := ∑' n, dterm χ s n
end LFunctionPartialSum
end Formalism.FX


