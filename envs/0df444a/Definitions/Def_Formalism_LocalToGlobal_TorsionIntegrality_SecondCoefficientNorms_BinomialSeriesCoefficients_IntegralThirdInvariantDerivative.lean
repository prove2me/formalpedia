-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:25.51499+00:00
-- url     : https://prove2.me/theorems/f7bbd536-bf29-4d22-a774-2429336407e4
-- title:
--   Integral Third Invariant Derivative
-- statement:
--   Definitions and structural lemmas for Integral Third Invariant Derivative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
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
namespace Formalism.L2.Th1.C
namespace FormalGroupJetIntegrality
open JetSubstitutionLemmas
section Field
variable {K : Type} [Field K]
end Field
section CharZero
variable {K : Type} [Field K] [CharZero K] {R : Subring K}
end CharZero
end FormalGroupJetIntegrality
end Formalism.L2.Th1.C


