-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:19.6077+00:00
-- url     : https://prove2.me/theorems/4e8380e0-0640-41c7-94a3-92622903808a
-- title:
--   Ram Basic
-- statement:
--   Definitions and structural lemmas for Ram Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end SlopeTestRemainingChoices
end Formalism.EigenvalueLevelCeiling


