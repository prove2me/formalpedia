-- Prove2me | solution 1 for AAInvW.eab_h_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:51.649696+00:00
-- url     : https://prove2.me/submissions/bbb27ce2-d1f0-43ef-9f01-d6198c5c6090

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_ana_rdLin
import Theorems.Thm_AAInvW_ana_hpartMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace AAInvW
theorem _root_.solution : EabHLin := by
  unfold EabHLin
  intro n H E _ _ f f' c a b g hH hf hf' hg
  unfold EabH
  rw [ana_rdLin hH c hf hf' (ana_hpartMem hH _).1 hg, ana_rdLin hH c hf hf' (ana_hpartMem hH _).2.1 hg]
  rw [smul_add, smul_add, smul_comm Complex.I c]
  abel
end AAInvW
