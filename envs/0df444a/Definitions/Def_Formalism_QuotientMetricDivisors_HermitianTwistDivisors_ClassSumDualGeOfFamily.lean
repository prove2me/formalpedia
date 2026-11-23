-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:18.618849+00:00
-- url     : https://prove2.me/theorems/dcf70413-ce22-4519-9440-b00471bb7b7f
-- title:
--   Class Sum Dual Ge Of Family
-- statement:
--   Definitions and structural lemmas for Class Sum Dual Ge Of Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace ValuationLatticeField
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end ValuationLatticeField
open exponent_index_lattice ValuationLatticeField
namespace ValuationLatticeField
end ValuationLatticeField
open ValuationLatticeField
end Formalism.DivisionValues


