-- Prove2me | solution 1 for AAInvW.ofFn_prod_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:59:56.937243+00:00
-- url     : https://prove2.me/submissions/d17d6755-b41e-485a-8368-ee6db35113c1

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (w : Fin t → ℂ) (X : Fin t → A),
      (List.ofFn fun k => w k • X k).prod = (∏ k, w k) • (List.ofFn X).prod := by
  intro t
  induction t with
  | zero => intro w X; simp
  | succ t ih =>
    intro w X
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => w k.succ) (fun k => X k.succ), Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
end AAInvW
