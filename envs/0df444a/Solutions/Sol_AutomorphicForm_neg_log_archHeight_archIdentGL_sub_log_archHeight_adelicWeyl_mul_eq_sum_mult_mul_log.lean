-- Prove2me | solution 1 for AutomorphicForm.neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e985512c-8020-59b7-8b21-68abf63f0814

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace ArchWeightToken

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

theorem val_archComponent_adelicWeyl (L : Type) [Field L] [NumberField L] (w : NumberField.InfinitePlace L) :
    ((NumberField.AdelicLevel.archComponent L w
        (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L)) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) = !![0, 1; 1, 0] := by
  ext i j : 1
  rw [NumberField.AdelicLevel.archComponent_apply, NumberField.AdelicLevel.glArch_apply]
  change (algebraMap L (AdeleRing (𝓞 L) L)
      (((AutomorphicForm.gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j)).1 w = !![0, 1; 1, 0] i j
  have hval : ((AutomorphicForm.gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] := rfl
  rw [hval]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem topNormSq_pos {F : Type*} [NormedField F] (g : GL (Fin 2) F) :
    0 < topNormSq (g : Matrix (Fin 2) (Fin 2) F) := by
  unfold topNormSq
  rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) F) 0 0) 0 with h0 | h0
  · rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) F) 0 1) 0 with h1 | h1
    · exact absurd (by rw [Matrix.det_fin_two, h0, h1]; ring) (Matrix.GeneralLinearGroup.det_ne_zero g)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.2 h1) 2)
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 h0) 2) (sq_nonneg _)

theorem rowNormSq_swap_mul {F : Type*} [NormedField F] (M : Matrix (Fin 2) (Fin 2) F) :
    rowNormSq (!![(0 : F), 1; 1, 0] * M) = topNormSq M := by
  simp [rowNormSq, topNormSq, Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_det_swap_mul {F : Type*} [NormedField F] (M : Matrix (Fin 2) (Fin 2) F) :
    ‖(!![(0 : F), 1; 1, 0] * M).det‖ = ‖M.det‖ := by
  rw [Matrix.det_mul, norm_mul]
  simp [Matrix.det_fin_two]

theorem log_aux (d r t : ℝ) (hd : 0 < d) (hr : 0 < r) (ht : 0 < t) :
    -Real.log (d / r) - Real.log (d / t) = Real.log (t * r / d ^ 2) := by
  rw [Real.log_div hd.ne' hr.ne', Real.log_div hd.ne' ht.ne', Real.log_div (mul_pos ht hr).ne' (pow_pos hd 2).ne',
    Real.log_mul ht.ne' hr.ne', Real.log_pow]
  push_cast
  ring

end ArchWeightToken

open ArchWeightToken AutomorphicForm.WindowedSiegel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
            (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) * AutomorphicForm.archIdentGL K L y)) =
      ∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
        Real.log
          (AutomorphicForm.WindowedSiegel.topNormSq
              ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L y) : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion) *
            AutomorphicForm.WindowedSiegel.rowNormSq
              ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L y) : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion) /
            ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L y) : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2) := by

  generalize AutomorphicForm.archIdentGL K L y = g
  set W := AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) with hWdef
  have hW : ∀ w : NumberField.InfinitePlace L,
      ((NumberField.AdelicLevel.archComponent L w W : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
        !![0, 1; 1, 0] := fun w => by rw [hWdef]; exact val_archComponent_adelicWeyl L w

  have hrow : ∀ w : NumberField.InfinitePlace L,
      rowNormSq ((NumberField.AdelicLevel.archComponent L w (W * g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) =
      topNormSq ((NumberField.AdelicLevel.archComponent L w g : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := fun w => by
    rw [map_mul, Units.val_mul, hW, rowNormSq_swap_mul]
  have hdet : ∀ w : NumberField.InfinitePlace L,
      ‖((NumberField.AdelicLevel.archComponent L w (W * g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ =
      ‖((NumberField.AdelicLevel.archComponent L w g : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ := fun w => by
    rw [map_mul, Units.val_mul, hW, norm_det_swap_mul]

  unfold AutomorphicForm.WindowedSiegel.archHeight
  rw [Real.log_prod (fun w _ => (pow_pos (localHeight_pos _) _).ne'),
    Real.log_prod (fun w _ => (pow_pos (localHeight_pos _) _).ne')]
  simp only [Real.log_pow]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold AutomorphicForm.WindowedSiegel.localHeight
  rw [hrow w, hdet w]
  have hd : 0 < ‖((NumberField.AdelicLevel.archComponent L w g : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).det‖ :=
    norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero _)
  rw [← log_aux _ _ _ hd (rowNormSq_pos _) (topNormSq_pos _)]
  ring

end S_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log
end P2MW
export P2MW.S_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log (solution)
