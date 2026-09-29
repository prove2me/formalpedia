-- Prove2me | solution 1 for AutomorphicForm.archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/458610ba-3e03-516e-8f56-0782871c9383

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace ArchWeightRegK

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

theorem val_archComponent_adelicWeyl (L : Type) [Field L] [NumberField L] (w : NumberField.InfinitePlace L) :
    ((NumberField.AdelicLevel.archComponent L w
        (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L)) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) = !![0, 1; 1, 0] := by
  ext i j
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

theorem det_swap {F : Type*} [NormedField F] : (!![(0 : F), 1; 1, 0]).det = -1 := by
  simp [Matrix.det_fin_two]

theorem continuous_localHeight' {F : Type*} [NormedField F] :
    Continuous fun g : GL (Fin 2) F => localHeight g := by
  have h1 : Continuous fun g : GL (Fin 2) F => ‖(g : Matrix (Fin 2) (Fin 2) F).det‖ :=
    (Units.continuous_val.matrix_det).norm
  have h2 : Continuous fun g : GL (Fin 2) F => rowNormSq (g : Matrix (Fin 2) (Fin 2) F) := by
    unfold rowNormSq
    exact (((Units.continuous_val.matrix_elem 1 0).norm).pow 2).add
      (((Units.continuous_val.matrix_elem 1 1).norm).pow 2)
  exact h1.div h2 fun g => (rowNormSq_pos g).ne'

theorem localHeight_diag_mul_mul_localHeight_swap_mul {F : Type*} [NormedField F]
    (S T X : GL (Fin 2) F) (hS : (S : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0])
    (hT01 : (T : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    localHeight (T * X) * localHeight (S * (T * X)) = localHeight X * localHeight (S * X) := by
  have hdetT : (T : Matrix (Fin 2) (Fin 2) F).det =
      (T : Matrix (Fin 2) (Fin 2) F) 0 0 * (T : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, hT01, hT10]; ring
  have ha : (T : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h; exact Matrix.GeneralLinearGroup.det_ne_zero T (by rw [hdetT, h, zero_mul])
  have hb : (T : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h; exact Matrix.GeneralLinearGroup.det_ne_zero T (by rw [hdetT, h, mul_zero])
  have hrowTX : rowNormSq ((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ‖(T : Matrix (Fin 2) (Fin 2) F) 1 1‖ ^ 2 * rowNormSq (X : Matrix (Fin 2) (Fin 2) F) :=
    rowNormSq_scalar_entries_mul hT10 rfl X
  have htopTX : topNormSq ((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ‖(T : Matrix (Fin 2) (Fin 2) F) 0 0‖ ^ 2 * topNormSq (X : Matrix (Fin 2) (Fin 2) F) :=
    topNormSq_scalar_entries_mul rfl hT01 X
  have hrowSTX : rowNormSq ((S * (T * X) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      topNormSq ((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, hS, rowNormSq_swap_mul]
  have hrowSX : rowNormSq ((S * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      topNormSq (X : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, hS, rowNormSq_swap_mul]
  have hdTX : ‖((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ =
      ‖(T : Matrix (Fin 2) (Fin 2) F) 0 0‖ * ‖(T : Matrix (Fin 2) (Fin 2) F) 1 1‖ *
        ‖(X : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hdetT, norm_mul, norm_mul]
  have hdSTX : ‖((S * (T * X) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ =
      ‖((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hS, det_swap, norm_mul, norm_neg, norm_one, one_mul]
  have hdSX : ‖((S * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ =
      ‖(X : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hS, det_swap, norm_mul, norm_neg, norm_one, one_mul]
  have hr := rowNormSq_pos X
  have ht := topNormSq_pos X
  have hna : 0 < ‖(T : Matrix (Fin 2) (Fin 2) F) 0 0‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖(T : Matrix (Fin 2) (Fin 2) F) 1 1‖ := norm_pos_iff.2 hb
  unfold localHeight
  rw [hdSTX, hdTX, hrowSTX, hrowTX, htopTX, hdSX, hrowSX]
  field_simp

end ArchWeightRegK

open ArchWeightRegK AutomorphicForm.WindowedSiegel in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hγ10 : (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (hγ01 : (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ : AutomorphicForm.IsRegularSemisimple (AdelicLevel.glArch (𝓞 K) K γ))
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K))) :
    (∀ t : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))),
      ∀ x : GL (Fin 2) (InfiniteAdeleRing K),
        (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x) =
        (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) x) ∧
    Continuous (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) ∧
    AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)]
      (fun x => ((fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) x : ℂ)) ν := by
  set W := AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) with hWdef
  have hW : ∀ v : NumberField.InfinitePlace K,
      ((NumberField.AdelicLevel.archComponent K v W : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) =
        !![0, 1; 1, 0] := fun v => by rw [hWdef]; exact val_archComponent_adelicWeyl K v

  have hHc : Continuous (AutomorphicForm.WindowedSiegel.archHeight K) := by
    unfold AutomorphicForm.WindowedSiegel.archHeight
    exact continuous_finsetProd _ fun v _ =>
      (continuous_localHeight'.comp (NumberField.AdelicLevel.continuous_archComponent K v)).pow _
  have hcont : Continuous (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
      -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight K (W * y))) :=
    ((hHc.log fun y => (archHeight_pos K y).ne').neg).sub
      ((hHc.comp (continuous_const.mul continuous_id)).log fun y => (archHeight_pos K _).ne')
  refine ⟨?_, hcont, ?_⟩
  ·
    intro t x

    have hcomm : ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
        (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
      rw [← Units.val_mul, ← Units.val_mul, Subgroup.mem_centralizer_singleton_iff.mp t.2]
    have hu : IsUnit ((AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
        (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) := by
      have h := hγ
      unfold AutomorphicForm.IsRegularSemisimple at h
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, hγ10, hγ01] at h
      have : ((AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 +
          (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) ^ 2 -
          4 * ((AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 *
            (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 - 0 * 0) =
          ((AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
            (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) ^ 2 := by ring
      rw [this] at h
      exact (isUnit_pow_iff two_ne_zero).mp h
    have ht01 : ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 := by
      have h := congrFun (congrFun hcomm 0) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hγ10, hγ01, mul_zero, zero_mul, add_zero, zero_add] at h

      refine (hu.mul_right_eq_zero).mp ?_
      rw [sub_mul, sub_eq_zero, ← h, mul_comm]
    have ht10 : ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := by
      have h := congrFun (congrFun hcomm 1) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hγ10, hγ01, mul_zero, zero_mul, add_zero, zero_add] at h

      refine (hu.mul_right_eq_zero).mp ?_
      rw [sub_mul, sub_eq_zero, mul_comm, h, mul_comm]

    have key : ∀ y : GL (Fin 2) (InfiniteAdeleRing K),
        AutomorphicForm.WindowedSiegel.archHeight K ((t : GL (Fin 2) (InfiniteAdeleRing K)) * y) *
          AutomorphicForm.WindowedSiegel.archHeight K (W * ((t : GL (Fin 2) (InfiniteAdeleRing K)) * y)) =
        AutomorphicForm.WindowedSiegel.archHeight K y *
          AutomorphicForm.WindowedSiegel.archHeight K (W * y) := by
      intro y
      unfold AutomorphicForm.WindowedSiegel.archHeight
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← mul_pow, ← mul_pow]
      congr 1
      rw [map_mul, map_mul, map_mul, map_mul]
      exact localHeight_diag_mul_mul_localHeight_swap_mul _ _ _ (hW v)
        (by rw [NumberField.AdelicLevel.archComponent_apply, ht01]; rfl)
        (by rw [NumberField.AdelicLevel.archComponent_apply, ht10]; rfl)
    have hlog : ∀ y : GL (Fin 2) (InfiniteAdeleRing K),
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K (W * y)) =
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y *
          AutomorphicForm.WindowedSiegel.archHeight K (W * y)) := fun y => by
      rw [Real.log_mul (archHeight_pos K _).ne' (archHeight_pos K _).ne']
      ring
    show -Real.log _ - Real.log _ = -Real.log _ - Real.log _
    rw [hlog, hlog, key]
  ·
    letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
    haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _
    exact (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable

end S_AutomorphicForm_archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal (solution)
