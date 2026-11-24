-- Prove2me | solution 1 for AAInvW.lx_herm_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:54:03.187603+00:00
-- url     : https://prove2.me/submissions/9eca2304-a2eb-4eb1-9984-3f0d1a599117

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Theorems.Thm_AAInvW_lx_mulVec_apply
import Theorems.Thm_AAInvW_lf_H_eI
import Theorems.Thm_AAInvW_lf_bvec_apply


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
theorem _root_.solution (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [dotProduct, Finset.sum_eq_single (eI k r a)]
  · rw [Pi.star_apply, lf_bvec_apply, if_pos rfl, star_one, one_mul, lx_mulVec_apply,
      Finset.sum_eq_single (esI k r a)]
    · rw [lf_H_eI, if_pos rfl, one_mul]
    · intro q _ hq
      rw [lf_H_eI, if_neg hq, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · intro t _ ht
    rw [Pi.star_apply, lf_bvec_apply, if_neg ht, star_zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end AAInvW
