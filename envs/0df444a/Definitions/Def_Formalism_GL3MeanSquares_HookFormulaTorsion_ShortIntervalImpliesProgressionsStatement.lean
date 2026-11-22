-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ShortIntervalImpliesProgressionsStatement
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_ShortIntervalImpliesProgressionsStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:54.958571+00:00
-- url     : https://prove2.me/theorems/08b40110-66f7-44da-8c66-443d999898ba
-- title:
--   Short Interval Implies Progressions Statement
-- statement:
--   Definitions and structural lemmas for Short Interval Implies Progressions Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ShortIntervalImpliesProgressionsStatement.lean

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
open scoped ENNReal
namespace Formalism.HermitianLattices.GL2a2
open Formalism.HermitianLattices.GL2PrimeSums
end Formalism.HermitianLattices.GL2a2


