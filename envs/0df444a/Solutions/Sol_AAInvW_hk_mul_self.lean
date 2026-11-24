-- Prove2me | solution 1 for AAInvW.hk_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:21.245498+00:00
-- url     : https://prove2.me/submissions/1e008b63-a973-45a4-9cb0-acba134cae14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Theorems.Thm_AAInvW_hk_apply
import Theorems.Thm_AAInvW_hk_sig_sig
import Theorems.Thm_AAInvW_hk_eps_sig
import Theorems.Thm_AAInvW_hk_eps_mul_self

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
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [mul_apply]
  simp_rw [hk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hk_sig_sig, hk_eps_sig]
  by_cases h : j = i
  · subst h; simp [hk_eps_mul_self]
  · simp [h, one_apply_ne' h]
end AAInvW
