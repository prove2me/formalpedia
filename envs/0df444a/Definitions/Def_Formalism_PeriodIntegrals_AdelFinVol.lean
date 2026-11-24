-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_AdelFinVol
-- name    : Formalism_PeriodIntegrals_AdelFinVol
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:40.808215+00:00
-- url     : https://prove2.me/theorems/c78cf306-045c-45e6-aadc-169dcd2c4689
-- title:
--   Adel Fin Vol
-- statement:
--   Definitions and structural lemmas for Adel Fin Vol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/AdelFinVol.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AdelFinVol
open MeasureTheory
def AdelFinVol : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf], μf.IsHaarMeasure →
    ∀ fund : Set I.GA, I.IsFundDom (I.muA μf) fund → I.muA μf fund ≠ ⊤
end PI.AdelFinVol


