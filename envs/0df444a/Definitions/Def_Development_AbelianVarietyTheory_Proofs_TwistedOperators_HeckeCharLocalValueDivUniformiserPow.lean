-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharLocalValueDivUniformiserPow
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharLocalValueDivUniformiserPow
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:32.702122+00:00
-- url     : https://prove2.me/theorems/1597ae4a-2e81-423e-ab64-2e893124d2e5
-- title:
--   Hecke Char Local Value Div Uniformiser Pow
-- statement:
--   Definitions and structural lemmas for Hecke Char Local Value Div Uniformiser Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharLocalValueDivUniformiserPow.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
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
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace GlobalTheory.HeckeLocDec
end GlobalTheory.HeckeLocDec


