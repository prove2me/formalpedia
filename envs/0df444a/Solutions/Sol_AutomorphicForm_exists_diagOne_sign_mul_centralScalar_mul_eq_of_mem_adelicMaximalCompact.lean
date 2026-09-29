-- Prove2me | solution 1 for AutomorphicForm.exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/52cf36bd-cdc7-5337-a822-33d6dcb2d9aa

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ AutomorphicForm.adelicMaximalCompact F) :
    ∃ (a z : (AdeleRing (𝓞 F) F)ˣ) (k₁ : AdelicGL2 (𝓞 F) F),
      ((a : AdeleRing (𝓞 F) F).2 = 1 ∧
        ∀ w : InfinitePlace F, (a : AdeleRing (𝓞 F) F).1 w = 1 ∨ (a : AdeleRing (𝓞 F) F).1 w = -1) ∧
      AutomorphicForm.centralScalar (𝓞 F) F z ∈ AutomorphicForm.adelicMaximalCompact F ∧
      k₁ ∈ AutomorphicForm.adelicMaximalCompact F ∧
      (∀ w : InfinitePlace F,
        ((archComponent F w (glArch (𝓞 F) F k₁) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) ∧
      k = NumberField.AdelicLevel.diagOne a * AutomorphicForm.centralScalar (𝓞 F) F z * k₁ := by
  classical
  obtain ⟨hkf, hkinf⟩ := AutomorphicForm.mem_adelicMaximalCompact_iff.mp hk

  set d : ∀ w : InfinitePlace F, w.Completion := fun w =>
    ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det
    with hd
  have hd1 : ∀ w, ‖d w‖ = 1 := fun w => (hkinf w).1
  have hd0 : ∀ w, d w ≠ 0 := fun w h => by have := hd1 w; rw [h, norm_zero] at this; exact zero_ne_one this

  have hchoice : ∀ w : InfinitePlace F, ∃ p : w.Completion × w.Completion,
      (p.1 = 1 ∨ p.1 = -1) ∧ ‖p.2‖ = 1 ∧ p.1 * p.2 ^ 2 = d w := by
    intro w
    rcases isReal_or_isComplex w with hw | hw
    · refine ⟨(d w, 1), ?_, norm_one, by ring⟩
      have hn : ‖extensionEmbeddingOfIsReal hw (d w)‖ = 1 := by
        rw [(isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]; exact hd1 w
      rw [Real.norm_eq_abs, abs_eq (zero_le_one' ℝ)] at hn
      rcases hn with h | h
      · left
        apply (extensionEmbeddingOfIsReal hw).injective
        rw [h, map_one]
      · right
        apply (extensionEmbeddingOfIsReal hw).injective
        rw [h, map_neg, map_one]
    · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (ringEquivComplexOfIsComplex hw (d w)) (by norm_num : 0 < 2)
      have h2 : ((ringEquivComplexOfIsComplex hw).symm s) ^ 2 = d w := by
        apply (ringEquivComplexOfIsComplex hw).injective
        rw [map_pow, RingEquiv.apply_symm_apply, hs]
      refine ⟨(1, (ringEquivComplexOfIsComplex hw).symm s), Or.inl rfl, ?_, by rw [one_mul, h2]⟩
      have : ‖(ringEquivComplexOfIsComplex hw).symm s‖ ^ 2 = 1 := by rw [← norm_pow, h2, hd1]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  choose p hp using hchoice
  have ha2 : ∀ w, (p w).1 * (p w).1 = 1 := fun w => by
    rcases (hp w).1 with h | h <;> rw [h] <;> norm_num
  have hz0 : ∀ w, (p w).2 ≠ 0 := fun w h => by
    have := (hp w).2.1; rw [h, norm_zero] at this; exact zero_ne_one this

  let aA : InfiniteAdeleRing F := fun w => (p w).1
  let zA : InfiniteAdeleRing F := fun w => (p w).2
  let zAi : InfiniteAdeleRing F := fun w => ((p w).2)⁻¹
  have haA : aA * aA = 1 := funext fun w => ha2 w
  have hzA : zA * zAi = 1 := funext fun w => mul_inv_cancel₀ (hz0 w)
  have hzA' : zAi * zA = 1 := funext fun w => inv_mul_cancel₀ (hz0 w)
  let a : (AdeleRing (𝓞 F) F)ˣ :=
    ⟨(aA, 1), (aA, 1), Prod.ext haA (mul_one 1), Prod.ext haA (mul_one 1)⟩
  let z : (AdeleRing (𝓞 F) F)ˣ :=
    ⟨(zA, 1), (zAi, 1), Prod.ext hzA (mul_one 1), Prod.ext hzA' (mul_one 1)⟩

  have eA : ∀ (w : InfinitePlace F) (i j : Fin 2),
      (archComponent F w (glArch (𝓞 F) F (diagOne a)) : Matrix (Fin 2) (Fin 2) w.Completion) i j =
        Matrix.diagonal ![(p w).1, 1] i j := by
    intro w i j
    rw [archComponent_apply, glArch_apply]
    change (Matrix.diagonal ![((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] i j).1 w = _
    fin_cases i <;> fin_cases j <;> rfl
  have eZ : ∀ (w : InfinitePlace F) (i j : Fin 2),
      (archComponent F w (glArch (𝓞 F) F (AutomorphicForm.centralScalar (𝓞 F) F z)) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = Matrix.diagonal ![(p w).2, (p w).2] i j := by
    intro w i j
    rw [archComponent_apply, glArch_apply]
    change ((Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) i j).1 w = _
    fin_cases i <;> fin_cases j <;> rfl

  have ha_mem : diagOne a ∈ AutomorphicForm.adelicMaximalCompact F := by
    refine AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨?_, fun w => ?_⟩
    · have h1' : glFin (𝓞 F) F (diagOne a) = 1 := by
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [glFin_apply, Units.val_one]
        change (Matrix.diagonal ![((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] i j).2 =
          (1 : Matrix (Fin 2) (Fin 2) _) i j
        fin_cases i <;> fin_cases j <;> rfl
      rw [h1']
      exact one_mem _
    · have hn : ‖(p w).1‖ = 1 := by
        rcases (hp w).1 with h | h
        · rw [h, norm_one]
        · rw [h, norm_neg, norm_one]
      refine ⟨?_, fun x y => ?_⟩
      · rw [Matrix.det_fin_two, eA, eA, eA, eA]
        simp [hn]
      · rw [eA, eA, eA, eA]
        simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
          Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1), Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_zero, add_zero, zero_add, mul_one, norm_mul, hn]
  have hz_mem : AutomorphicForm.centralScalar (𝓞 F) F z ∈ AutomorphicForm.adelicMaximalCompact F := by
    refine AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨?_, fun w => ?_⟩
    · have h1' : glFin (𝓞 F) F (AutomorphicForm.centralScalar (𝓞 F) F z) = 1 := by
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [glFin_apply, Units.val_one]
        change ((Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2) _) i j
        fin_cases i <;> fin_cases j <;> rfl
      rw [h1']
      exact one_mem _
    · have hn : ‖(p w).2‖ = 1 := (hp w).2.1
      refine ⟨?_, fun x y => ?_⟩
      · rw [Matrix.det_fin_two, eZ, eZ, eZ, eZ]
        simp [hn]
      · rw [eZ, eZ, eZ, eZ]
        simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
          Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1), Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_zero, add_zero, zero_add, norm_mul, hn, mul_one]

  have hdetA : ∀ w, ((Matrix.GeneralLinearGroup.det (archComponent F w (glArch (𝓞 F) F (diagOne a))) :
      (w.Completion)ˣ) : w.Completion) = (p w).1 := by
    intro w
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, eA, eA, eA, eA]
    simp
  have hdetZ : ∀ w, ((Matrix.GeneralLinearGroup.det (archComponent F w (glArch (𝓞 F) F
      (AutomorphicForm.centralScalar (𝓞 F) F z))) : (w.Completion)ˣ) : w.Completion) = (p w).2 ^ 2 := by
    intro w
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, eZ, eZ, eZ, eZ]
    simp [sq]
  have hdetK : ∀ w, ((Matrix.GeneralLinearGroup.det (archComponent F w (glArch (𝓞 F) F k)) :
      (w.Completion)ˣ) : w.Completion) = d w := fun w => by
    rw [Matrix.GeneralLinearGroup.val_det_apply]

  refine ⟨a, z, (diagOne a * AutomorphicForm.centralScalar (𝓞 F) F z)⁻¹ * k, ⟨rfl, fun w => (hp w).1⟩, hz_mem,
    ?_, fun w => ?_, ?_⟩
  · exact (AutomorphicForm.adelicMaximalCompact F).mul_mem
      ((AutomorphicForm.adelicMaximalCompact F).inv_mem ((AutomorphicForm.adelicMaximalCompact F).mul_mem ha_mem hz_mem)) hk
  · rw [← Matrix.GeneralLinearGroup.val_det_apply]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hdetA, hdetZ, hdetK]
    rw [(hp w).2.2]
    exact inv_mul_cancel₀ (hd0 w)
  · rw [mul_inv_cancel_left]

end S_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact (solution)
