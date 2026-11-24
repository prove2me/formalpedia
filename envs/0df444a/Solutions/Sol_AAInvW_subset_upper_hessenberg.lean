-- Prove2me | solution 1 for AAInvW.subset_upper_hessenberg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:08.647797+00:00
-- url     : https://prove2.me/submissions/f41721e1-6c2d-4d79-8cdf-f4a6e4df3407

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_inUH_mul

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
theorem _root_.solution : SsetUH := by
  unfold SsetUH
  intro k r z s hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact lf_inUH_mul hh.1 hm.1
end AAInvW
