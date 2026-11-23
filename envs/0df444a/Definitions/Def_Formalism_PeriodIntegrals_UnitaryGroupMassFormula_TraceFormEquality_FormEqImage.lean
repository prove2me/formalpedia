-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:53.285967+00:00
-- url     : https://prove2.me/theorems/663ed767-9583-49e9-be9c-d0d8d9f01a03
-- title:
--   Form Eq Image
-- statement:
--   Definitions and structural lemmas for Form Eq Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.HermitianFormEquivalence
open PI.Dv
section Forms
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
end Forms
end PI.Dv.HermitianFormEquivalence


