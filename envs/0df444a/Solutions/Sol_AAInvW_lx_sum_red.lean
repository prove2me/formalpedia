-- Prove2me | solution 1 for AAInvW.lx_sum_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:19.275733+00:00
-- url     : https://prove2.me/submissions/cf6f3d19-41d2-4975-8834-9a3189afb907

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector

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
theorem _root_.solution {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) (F : Fin n → ℂ)
    (hF : ∀ j, j ∉ Set.range e → F j = 0) : ∑ j, F j = ∑ b, F (e b) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (by intro x _ y _ h; exact he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hF
  rintro ⟨b, rfl⟩
  exact hj (Finset.mem_image_of_mem e (Finset.mem_univ b))
end AAInvW
