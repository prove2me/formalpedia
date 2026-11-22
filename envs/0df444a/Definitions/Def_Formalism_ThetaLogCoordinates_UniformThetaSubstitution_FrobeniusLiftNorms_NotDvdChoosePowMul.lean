-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:20.159382+00:00
-- url     : https://prove2.me/theorems/44bf895b-6266-436d-9068-9aaacec63a45
-- title:
--   Not Dvd Choose Pow Mul
-- statement:
--   Definitions and structural lemmas for Not Dvd Choose Pow Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
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
namespace LemOne
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section Top
variable {K : Type} [Field K]
end Top
section Main
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Main
section Limit
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def rem (p : ℕ) (f : PowerSeries K) (a b : K) : PowerSeries K :=
  f - PowerSeries.C a * g0F K p - PowerSeries.C b * lgF K p
def Good (p : ℕ) (f : PowerSeries K) (j : ℕ) (a b : K) : Prop :=
  ‖a‖ ≤ 1 ∧ ∀ d < p ^ (2 * j + 1), ‖PowerSeries.coeff d (rem p f a b)‖ ≤ 1
end Limit
end LemOne
end Formalism.InvariantFactorPaths.G7


