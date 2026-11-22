-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:51.982298+00:00
-- url     : https://prove2.me/theorems/e2bc1602-276f-4995-ad0a-631030b3242a
-- title:
--   Reduction Third Step Mean
-- statement:
--   Definitions and structural lemmas for Reduction Third Step Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionThirdStepMean.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace Formalism.DivisionValues
namespace NormSquareReduction
variable {Q E : Type} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end NormSquareReduction
end Formalism.DivisionValues


