-- Prove2me | solution 1 for AAInvW.operators_commute_translations_of_left_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:19.996901+00:00
-- url     : https://prove2.me/submissions/78d74175-cd93-45af-9a3f-29fb0e265504

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorsCommuteTranslationsOfLeftRight
import Theorems.Thm_AAInvW_inUH_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
namespace AAInvW
theorem _root_.solution (hL : LeftAA) (hR : RightAA) (hS : SsetUH) : OperatorsCommuteTranslations := by
  unfold OperatorsCommuteTranslations
  intro E _ _ k r z z' m hm u ell f _ _ hf s hs s' hs' g hg
  have hsg : inUH (Hpk k r) (s * g) := inUH_mul (hS k r z s hs) hg
  obtain ⟨hL1, hL2⟩ := hL E k r z m hm u ell (fun x => f (x * s')) s g hs hg
  obtain ⟨hR1, hR2⟩ := hR E k r z' m hm u ell f s' (s * g) hf hs' hsg
  exact ⟨hL1.trans hR1, hL2.trans hR2⟩
end AAInvW
