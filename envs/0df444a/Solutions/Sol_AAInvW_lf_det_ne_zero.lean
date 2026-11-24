-- Prove2me | solution 1 for AAInvW.lf_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:03.361004+00:00
-- url     : https://prove2.me/submissions/a017d3fe-7225-495d-b9c9-63cf92f9ba32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_Hmul
import Theorems.Thm_AAInvW_hk_apply
import Theorems.Thm_AAInvW_hk_eps_sig
import Theorems.Thm_AAInvW_hk_sig_sig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext t p
  rw [lf_Hmul, hk_apply, hk_sig_sig, hk_eps_sig, Matrix.one_apply]
  by_cases htp : p = t
  · subst htp
    rw [if_pos rfl, if_pos rfl]
    unfold hkEps
    split_ifs <;> norm_num
  · rw [if_neg htp, if_neg (Ne.symm htp), mul_zero]
end AAInvW
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
namespace AAInvW
theorem _root_.solution (k r : ℕ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : inUH (Hpk k r) g) : g.det ≠ 0 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hdH : (Hpk k r).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (hpk_sq_lemma k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  intro h0
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, h0, mul_zero] at h1
  exact hdH h1.symm
end AAInvW
