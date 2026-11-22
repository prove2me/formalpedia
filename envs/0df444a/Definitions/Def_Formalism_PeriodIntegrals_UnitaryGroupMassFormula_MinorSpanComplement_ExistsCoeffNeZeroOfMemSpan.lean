-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:54.353937+00:00
-- url     : https://prove2.me/theorems/03dafcf5-3688-42af-95ae-160fe6b8341e
-- title:
--   Exists Coeff Ne Zero Of Mem Span
-- statement:
--   Definitions and structural lemmas for Exists Coeff Ne Zero Of Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.MSC
open scoped MonomialOrder
variable {σ R : Type*} [CommRing R]
end PI.MSC


