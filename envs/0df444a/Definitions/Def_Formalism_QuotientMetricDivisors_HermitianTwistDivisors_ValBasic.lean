-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:17.010586+00:00
-- url     : https://prove2.me/theorems/25fe4f8d-96d9-403d-aaf5-12059a914cd4
-- title:
--   Val Basic
-- statement:
--   Definitions and structural lemmas for Val Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
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
namespace ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end ValuationRepresentative
open ValuationRepresentative
end Formalism.DivisionValues


