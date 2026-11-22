-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:50.336822+00:00
-- url     : https://prove2.me/theorems/43aef5ef-a7a6-482a-9852-204c8e1fdcc8
-- title:
--   Kappa Normalise
-- statement:
--   Definitions and structural lemmas for Kappa Normalise, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [NumberField K]
end SlopeTestRemainingChoices
end Formalism.DivisionValues


