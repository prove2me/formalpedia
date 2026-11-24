-- Prove2me | solution 1 for AAInvW.hk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:51.368163+00:00
-- url     : https://prove2.me/submissions/d7c4e79d-37e9-4b32-8c7f-d337c17b5d06

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Theorems.Thm_AAInvW_hk_apply
import Theorems.Thm_AAInvW_hk_sig_sig
import Theorems.Thm_AAInvW_hk_eps_sig
import Theorems.Thm_AAInvW_hk_star_eps

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
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hk_apply, hk_apply]
  by_cases h : j = hkSig k r i
  · subst h
    simp [hk_sig_sig, hk_eps_sig, hk_star_eps]
  · have h' : i ≠ hkSig k r j := fun e => h (by rw [e, hk_sig_sig])
    simp [h, h']
end AAInvW
