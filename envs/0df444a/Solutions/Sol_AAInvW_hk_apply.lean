-- Prove2me | solution 1 for AAInvW.hk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:35:03.931813+00:00
-- url     : https://prove2.me/submissions/3401ed6d-eaae-4bac-a6aa-22a191b3d739

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
namespace AAInvW
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hkSig k r i then hkEps k r i else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Hpk, hkSig, hkEps, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end AAInvW
