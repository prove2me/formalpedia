-- Prove2me | solution 1 for AAInvW.ana_Ec_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:41:48.800985+00:00
-- url     : https://prove2.me/submissions/6d98705f-2e96-4032-a7f8-3d721e9622b7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_hpart1_sub
import Theorems.Thm_AAInvW_ana_hpart2_sub
import Theorems.Thm_AAInvW_ana_hpartMem
import Theorems.Thm_AAInvW_ana_rdSub


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
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hg : inUH H g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcH H (Z - W) f g = EcH H Z f g - EcH H W f g := by
  unfold EcH
  rw [ana_hpart1_sub hH, ana_hpart2_sub hH,
    ana_rdSub hH hf (ana_hpartMem hH Z).1 (ana_hpartMem hH W).1 hg,
    ana_rdSub hH hf (ana_hpartMem hH Z).2.1 (ana_hpartMem hH W).2.1 hg, smul_sub]
  abel
end AAInvW
