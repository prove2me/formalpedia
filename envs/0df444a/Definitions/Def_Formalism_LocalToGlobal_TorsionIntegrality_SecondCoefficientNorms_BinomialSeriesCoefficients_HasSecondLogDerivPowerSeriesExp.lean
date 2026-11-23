-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:35.943654+00:00
-- url     : https://prove2.me/theorems/0e82706c-ec57-4680-8ecf-95e70e9bd4c9
-- title:
--   Has Second Log Deriv Power Series Exp
-- statement:
--   Definitions and structural lemmas for Has Second Log Deriv Power Series Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
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
open PowerSeries
namespace Formalism.L2.Th1.C
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [CharZero K]
def pExp (f : PowerSeries K) : PowerSeries K := mvExp f
end SlopeTestRemainingChoices
section Calc
variable {K : Type} [Field K] [CharZero K]
end Calc
section Main
end Main
end Formalism.L2.Th1.C


