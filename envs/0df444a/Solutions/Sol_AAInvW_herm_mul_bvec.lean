-- Prove2me | solution 1 for AAInvW.herm_mul_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:21.70536+00:00
-- url     : https://prove2.me/submissions/04a00895-c480-467e-9c1c-c7162929d86f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine

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
theorem _root_.solution {N : ℕ} (H g s : Matrix (Fin N) (Fin N) ℂ) (c : Fin N) (w : Fin N → ℂ) :
    herm H ((g * s) *ᵥ bvec c) w = ∑ d, s d c * herm H (g *ᵥ bvec d) w := by
  unfold herm
  have hcol : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (e : Fin N), M *ᵥ bvec e = fun i => M i e := by
    intro M e
    funext i
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hcol]
  simp only [Matrix.mulVec_mulVec]
  simp only [hcol, dotProduct, Matrix.mul_apply (M := H * g), Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring
end AAInvW
