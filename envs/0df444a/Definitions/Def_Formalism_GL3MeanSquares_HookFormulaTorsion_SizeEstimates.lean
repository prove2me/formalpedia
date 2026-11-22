-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SizeEstimates
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_SizeEstimates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:49.414266+00:00
-- url     : https://prove2.me/theorems/5b50fc83-5037-4d26-a1ef-a120a9d64e45
-- title:
--   Size Estimates
-- statement:
--   Definitions and structural lemmas for Size Estimates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SizeEstimates.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
namespace Formalism.HermitianLattices.P.JacobiSumIdentities
def jHom (q : ℕ) : ℤ →* ℤ where
  toFun a := jacobiSym a q
  map_one' := jacobiSym.one_left q
  map_mul' a b := jacobiSym.mul_left a b q
end Formalism.HermitianLattices.P.JacobiSumIdentities


