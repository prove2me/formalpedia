-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:57.917218+00:00
-- url     : https://prove2.me/theorems/b68f6b27-886a-455e-a1af-50fabec44733
-- title:
--   Measure Preserving Of Card
-- statement:
--   Definitions and structural lemmas for Measure Preserving Of Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerShearHaar/MeasurePreservingOfCard.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace PI.LowSplitHaarW
def extNe {ι : Type} [DecidableEq ι] (a : ι) (y : {i // i ≠ a} → ℂ) : ι → ℂ :=
  fun j => if h : j ≠ a then y ⟨j, h⟩ else 0
end PI.LowSplitHaarW


