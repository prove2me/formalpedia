-- Prove2me | solution 1 for AAInvW.tm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:59:59.534808+00:00
-- url     : https://prove2.me/submissions/49cd7c83-9a15-42c0-940e-09d643ab037d

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ) (i j : Fin n) :
    Tm (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) x i j =
      ∑ p : Fin n × Fin n, (P p.1 i * Q j p.2) • Tm E x p.1 p.2 := by
  simp only [Tm]
  simp only [smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul]
  have hsum : ∑ c, P c i * Q j c = (Q * P) j i := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [hsum, hQP, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
end AAInvW
