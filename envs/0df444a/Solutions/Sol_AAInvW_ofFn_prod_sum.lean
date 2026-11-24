-- Prove2me | solution 1 for AAInvW.ofFn_prod_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:59:57.745551+00:00
-- url     : https://prove2.me/submissions/01db5799-7f4e-4327-9aaa-d247782e113c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul

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
open Formalism.REAL
namespace AAInvW
theorem _root_.solution {A : Type*} [Ring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (F : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, F k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => F k (c k)).prod := by
  intro t
  induction t with
  | zero => intro F; simp
  | succ t ih =>
    intro F
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => F k.succ), Finset.sum_mul_sum]
    first
    | (rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
       simp [List.ofFn_succ, Fin.consEquiv])
    | (rw [← (Equiv.piFinSucc t ι).symm.sum_comp, Fintype.sum_prod_type]
       simp [List.ofFn_succ, Equiv.piFinSucc])
end AAInvW
