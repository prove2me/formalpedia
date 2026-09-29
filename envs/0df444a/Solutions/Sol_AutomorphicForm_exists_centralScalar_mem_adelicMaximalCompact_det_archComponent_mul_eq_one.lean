-- Prove2me | solution 1 for AutomorphicForm.exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1e85501f-6d5b-5ff6-81e0-04edd59bb2d5

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_AdelicLsXi

import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

noncomputable section

open AutomorphicForm.WindowedSiegel NumberField.AdelicVolume

namespace ComplexSplitProof

variable {F : Type} [Field F] [NumberField F]

theorem exists_sq_eq (w : InfinitePlace F) (hw : w.IsComplex) (d : w.Completion) :
    ∃ u : w.Completion, u ^ 2 = d := by
  let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e d) (by norm_num : 0 < 2)
  refine ⟨e.symm s, ?_⟩
  apply e.injective
  rw [map_pow, RingEquiv.apply_symm_apply, hs]

theorem isRowIsometry_of_diag {K : Type*} [NormedField K] (M : GL (Fin 2) K) (u : K) (hu : ‖u‖ = 1)
    (h00 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = u) (h01 : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = u) :
    IsRowIsometry M := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [Matrix.det_fin_two, h00, h01, h10, h11, mul_zero, sub_zero, norm_mul, hu, mul_one]
  · rw [h00, h01, h10, h11]
    simp only [mul_zero, add_zero, zero_add, norm_mul, hu, mul_one]

end ComplexSplitProof

open ComplexSplitProof AutomorphicForm.WindowedSiegel NumberField.AdelicVolume in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (hreal : ∀ w : InfinitePlace F, w.IsReal →
      ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ,
      centralScalar (𝓞 F) F z ∈ adelicMaximalCompact F ∧
      (∀ w : InfinitePlace F, w.IsReal →
        ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) ∧
      (∀ w : InfinitePlace F,
        ((archComponent F w (glArch (𝓞 F) F (k * centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) := by
  classical

  set d : ∀ w : InfinitePlace F, w.Completion := fun w =>
    ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det with hd
  have hdn : ∀ w, ‖d w‖ = 1 := fun w => (isRowIsometry_archComponent hk w).1
  have hd0 : ∀ w, d w ≠ 0 := fun w h => by have := hdn w; rw [h, norm_zero] at this; exact zero_ne_one this

  have hc : ∀ w : InfinitePlace F, ∃ u : w.Completion, ‖u‖ = 1 ∧ d w * u ^ 2 = 1 := by
    intro w
    by_cases hw : w.IsReal
    · exact ⟨1, norm_one, by rw [one_pow, mul_one]; exact hreal w hw⟩
    · have hwc : w.IsComplex := (NumberField.InfinitePlace.isReal_or_isComplex w).resolve_left hw
      obtain ⟨u, hu⟩ := exists_sq_eq w hwc (d w)⁻¹
      refine ⟨u, ?_, by rw [hu, mul_inv_cancel₀ (hd0 w)]⟩
      have h2 : ‖u‖ ^ 2 = 1 := by rw [← norm_pow, hu, norm_inv, hdn, inv_one]
      have h3 : (‖u‖ - 1) * (‖u‖ + 1) = 0 := by ring_nf; linarith [h2]
      rcases mul_eq_zero.mp h3 with h | h
      · linarith
      · linarith [norm_nonneg u]
  choose c hcn hcd using hc
  have hc0 : ∀ w, c w ≠ 0 := fun w h => by have := hcn w; rw [h, norm_zero] at this; exact zero_ne_one this

  let zA : InfiniteAdeleRing F := fun w => c w
  let zAi : InfiniteAdeleRing F := fun w => (c w)⁻¹
  let z : (AdeleRing (𝓞 F) F)ˣ :=
    { val := (zA, 1)
      inv := (zAi, 1)
      val_inv := Prod.ext (funext fun w => mul_inv_cancel₀ (hc0 w)) (one_mul 1)
      inv_val := Prod.ext (funext fun w => inv_mul_cancel₀ (hc0 w)) (one_mul 1) }

  have hentry : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = if i = j then c w else 0 := by
    intro w i j
    simp only [archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  have hdetz : ∀ w : InfinitePlace F,
      ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = c w ^ 2 := by
    intro w
    rw [Matrix.det_fin_two, hentry, hentry, hentry, hentry]
    simp
    ring
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [mem_adelicMaximalCompact_iff]
    refine ⟨?_, fun w => ?_⟩
    · have : glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 := by
        refine Matrix.GeneralLinearGroup.ext fun i j => ?_
        rw [glFin_apply, Units.val_one]
        by_cases h : i = j
        · subst h
          rw [centralScalar_apply_eq, Matrix.one_apply_eq]
        · rw [centralScalar_apply_ne _ h, Matrix.one_apply_ne h]
          rfl
      rw [this]
      exact (finiteIntegralGL2 (𝓞 F) F).one_mem
    · exact isRowIsometry_of_diag _ (c w) (hcn w) (by rw [hentry]; simp) (by rw [hentry]; simp)
        (by rw [hentry]; simp) (by rw [hentry]; simp)
  · intro w hw
    rw [hdetz]
    have h1 := hcd w
    rwa [show d w = 1 from hreal w hw, one_mul] at h1
  · intro w
    rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, hdetz]
    exact hcd w

end
end S_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one (solution)
