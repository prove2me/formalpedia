-- Prove2me | solution 1 for AAInvW.det_mul_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:19.366523+00:00
-- url     : https://prove2.me/submissions/74c706b4-91f0-41e8-b91c-4f6637225b67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet

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
namespace AAInvW
theorem _root_.solution {m N : ℕ} (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ d : Fin m → Fin N, (∏ l, Y (d l) l) • (Matrix.of fun a l => X a (d l)).det := by
  rw [← Matrix.det_transpose]
  have hT : (X * Y)ᵀ = fun l => ∑ k, Y k l • (fun a => X a k) := by
    ext l a
    simp [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [hT]
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_sum
    (fun l k => Y k l • (fun a => X a k))).trans ?_
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_smul_univ
    (fun l => Y (d l) l) (fun l a => X a (d l))).trans ?_
  congr 1
  rw [← Matrix.det_transpose]
  rfl
end AAInvW
