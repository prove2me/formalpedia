-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:46.523203+00:00
-- url     : https://prove2.me/theorems/9e00a0b5-20a2-40be-8ffd-91e25bd8c862
-- title:
--   Hecke Char Uniformiser Value Is Algebraic
-- statement:
--   Definitions and structural lemmas for Hecke Char Uniformiser Value Is Algebraic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraic.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section
namespace GlobalTheory
open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
end GlobalTheory


