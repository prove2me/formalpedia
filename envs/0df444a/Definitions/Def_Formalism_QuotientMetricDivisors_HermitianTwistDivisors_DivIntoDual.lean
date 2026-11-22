-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:43.225723+00:00
-- url     : https://prove2.me/theorems/eb4c8280-6ff3-4423-bc8f-8cf9342a2d31
-- title:
--   Div Into Dual
-- statement:
--   Definitions and structural lemmas for Div Into Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivIntoDual.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
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
namespace DualLatticeDivisor
variable {K : Type} [Field K] [NumberField K]
end DualLatticeDivisor
end Formalism.DivisionValues


