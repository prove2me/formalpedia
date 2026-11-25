-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_CoeffTwoPSeries
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_CoeffTwoPSeries
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:32:06.760744+00:00
-- url     : https://prove2.me/theorems/d475eb76-9963-434f-9a6c-b8fe63ada220
-- title:
--   Coeff Two PSeries
-- statement:
--   Definitions and structural lemmas for Coeff Two PSeries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/CoeffTwoPSeries.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_GoodModelLattice
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
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
namespace Formalism.L2.Th1.B.KSum
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
end Formalism.L2.Th1.B.KSum


