-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:25.902958+00:00
-- url     : https://prove2.me/theorems/9c5e0abd-aef6-4372-96f5-c1c3d68d4f2a
-- title:
--   Pr VSum Tmul
-- statement:
--   Definitions and structural lemmas for Pr VSum Tmul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/PrVSumTmul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
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
def adOf {F : Type} [Field F] [NumberField F] (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  (⟨a, Filter.Eventually.of_forall ha⟩ :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
end PI.LPI


