-- Prove2me | solution 1 for AAInvW.ana_rdLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:00:39.275257+00:00
-- url     : https://prove2.me/submissions/22a49ff4-7af5-4396-aece-be1c98c210b7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_ana_expt
import Theorems.Thm_AAInvW_ana_mul


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
theorem _root_.solution (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X g : Matrix (Fin n) (Fin n) ℂ}
    (hff : ∀ x, inUH H x → f x = f' x) (hX : inLH H X) (hg : inUH H g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact hff _ (ana_mul hg (ana_expt hH hX t))
end AAInvW
