-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_UniHaar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_UniHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:13.864847+00:00
-- url     : https://prove2.me/theorems/85971d16-6a1d-4c0a-a18f-61bdaca6735b
-- title:
--   Uni Haar
-- statement:
--   Definitions and structural lemmas for Uni Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open MeasureTheory
def IsLowUni {A : Type} [CommRing A] {k : ℕ} (U : Matrix (Fin k) (Fin k) A) : Prop :=
  (∀ i, U i i = 1) ∧ ∀ i j : Fin k, i < j → U i j = 0
end PI.VolSemiDirect.W.Cj


