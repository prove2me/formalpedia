-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:49.863183+00:00
-- url     : https://prove2.me/theorems/e75e83e5-aff3-4a5c-8309-2cd449461599
-- title:
--   Jw Conj
-- statement:
--   Definitions and structural lemmas for Jw Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/JwConj.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
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
namespace ConjugateWeightLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end ConjugateWeightLattice
open ConjugateWeightLattice
end Formalism.DivisionValues


