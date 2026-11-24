-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:20.507635+00:00
-- url     : https://prove2.me/theorems/790c07cd-bce8-43e8-a6b1-76ef91785c1b
-- title:
--   Weierstrass Numerator Denominator
-- statement:
--   Definitions and structural lemmas for Weierstrass Numerator Denominator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
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
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries
namespace Formalism.L2.Th1.F.POf
variable {K : Type} [Field K]
section CharZero
variable [CharZero K]
end CharZero
section CharZero2
variable [CharZero K]
def defect (g2 g3 : K) (P : PowerSeries K) : PowerSeries K :=
  (-2 + X ^ 3 * derivative K P) ^ 2 - 4 * (1 + X ^ 2 * P) ^ 3
    + C g2 * X ^ 4 * (1 + X ^ 2 * P) + C g3 * X ^ 6
end CharZero2
end Formalism.L2.Th1.F.POf
namespace Formalism.L2.Th1.F
open POf
end Formalism.L2.Th1.F


