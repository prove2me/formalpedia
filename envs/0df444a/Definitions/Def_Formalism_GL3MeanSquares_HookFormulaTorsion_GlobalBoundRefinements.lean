-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:11.999801+00:00
-- url     : https://prove2.me/theorems/13771117-6f60-4cfa-8abd-72aa1d694241
-- title:
--   Global Bound Refinements
-- statement:
--   Definitions and structural lemmas for Global Bound Refinements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/GlobalBoundRefinements.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
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
namespace Formalism.HermitianLattices.GlobalBoundRefinements
section ShortIntervalLowerBound
open Formalism.HermitianLattices.GL2PrimeSums
end ShortIntervalLowerBound
section T2
open NumberField
open Formalism.LogVandermondeBounds.StandardLattice
end T2
end Formalism.HermitianLattices.GlobalBoundRefinements


