-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:03.906833+00:00
-- url     : https://prove2.me/theorems/d987026e-3059-4d55-929b-37bcf872393b
-- title:
--   Single Apply
-- statement:
--   Definitions and structural lemmas for Single Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/SingleApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
namespace PI.LPI
open Formalism.UG
def single {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F := by
  classical
  exact adOf (Pi.single v a) (fun w => by
    by_cases h : w = v
    · subst h; simpa using ha
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
end PI.LPI


