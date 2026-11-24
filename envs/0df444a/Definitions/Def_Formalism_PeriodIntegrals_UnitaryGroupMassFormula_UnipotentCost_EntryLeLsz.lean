-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:10.730923+00:00
-- url     : https://prove2.me/theorems/ad0aa396-cd72-4b5a-8b1d-14bec56a8cf9
-- title:
--   Entry Le Lsz
-- statement:
--   Definitions and structural lemmas for Entry Le Lsz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/EntryLeLsz.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
def sc {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (((lsz X)⁻¹ : ℝ) : ℂ) • X
def scx {k r : ℕ} (x : Bool × B.Mat k r) : Bool × B.Mat k r := (x.1, sc x.2)
end PI.UnitaryGroupMassFormula.UsCost


