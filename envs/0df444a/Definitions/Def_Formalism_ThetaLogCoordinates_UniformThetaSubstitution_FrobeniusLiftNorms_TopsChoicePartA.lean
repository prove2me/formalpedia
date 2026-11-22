-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:52.964924+00:00
-- url     : https://prove2.me/theorems/739ce850-0c36-40ea-a9e0-7b68df26fc23
-- title:
--   Tops Choice Part A
-- statement:
--   Definitions and structural lemmas for Tops Choice Part A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def AA (K : Type) [Field K] (p : ℕ) (x y : Fin 2) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n x + 1), ∑ j ∈ range (n y + 1),
    if i ≤ j ∧ n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0
end Formalism.InvariantFactorPaths.G7


