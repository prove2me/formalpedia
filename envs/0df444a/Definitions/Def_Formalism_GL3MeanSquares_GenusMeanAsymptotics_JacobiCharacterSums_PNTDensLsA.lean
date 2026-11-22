-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:26.518491+00:00
-- url     : https://prove2.me/theorems/d4e81a8d-e013-4aa2-af07-e65cb2180be0
-- title:
--   PNTDens Ls A
-- statement:
--   Definitions and structural lemmas for PNTDens Ls A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
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
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, f k
def dterm (s : ℂ) (n : ℕ) : ℂ := Ap f n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))
def G (s : ℂ) : ℂ := ∑' n, dterm f s n
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums


