-- Prove2me | solution 1 for AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ecc444fa-0970-5d53-ab9c-fb45ba8c8b3d

import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F))
    (_hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (_hg' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F) :
    ∃ (β : GL (Fin 2) (v.adicCompletion F)) (x : v.adicCompletion F),
      (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
      (∀ i j, (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        ∈ v.adicCompletionIntegers F) ∧
      x ∈ v.adicCompletionIntegers F ∧
      (g = β * gl2Weyl * unipotentGL2 x ∨ g = β * gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹) := by

  set a := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 with hd
  set p := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 with hp
  set q := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 with hq
  set r := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 with hr
  set t := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 with ht
  have hgm : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a, b; c, d] := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> rfl
  have hgim : ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![p, q; r, t] := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> rfl
  have hai : a ∈ v.adicCompletionIntegers F := _hg 0 0
  have hbi : b ∈ v.adicCompletionIntegers F := _hg 0 1
  have hci : c ∈ v.adicCompletionIntegers F := _hg 1 0
  have hdi : d ∈ v.adicCompletionIntegers F := _hg 1 1
  have hpi : p ∈ v.adicCompletionIntegers F := _hg' 0 0
  have hqi : q ∈ v.adicCompletionIntegers F := _hg' 0 1
  have hri : r ∈ v.adicCompletionIntegers F := _hg' 1 0
  have hti : t ∈ v.adicCompletionIntegers F := _hg' 1 1

  have hrow : c * q + d * t = 1 := by
    have h1 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => m 1 1)
      (show ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        * ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1) from by
          rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one])
    simp only [hgm, hgim, Matrix.mul_fin_two] at h1
    simpa using h1

  have mem_iff : ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F ↔ Valued.v y ≤ 1 :=
    fun y => Iff.rfl
  by_cases hcu : Valued.v c = 1
  ·
    have hc0 : c ≠ 0 := by intro h; rw [h, map_zero] at hcu; exact zero_ne_one hcu
    set x : v.adicCompletion F := d / c with hx
    have hxi : x ∈ v.adicCompletionIntegers F := by
      rw [mem_iff, hx, map_div₀, hcu, div_one]; exact (mem_iff d).mp hdi
    set β : GL (Fin 2) (v.adicCompletion F) := g * (unipotentGL2 x)⁻¹ * gl2Weyl⁻¹ with hβ
    have hβm : (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![b - a * x, a; d - c * x, c] := by
      rw [hβ, gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hgm, gl2Weyl_val]
      have : (((unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
          = !![1, -x; 0, 1] := rfl
      rw [this]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp <;> ring
    have hβim : ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![r, t; p + x * r, q + x * t] := by
      rw [hβ, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_mul, hgim, gl2Weyl_val, unipotentGL2_coe]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hdcx : d - c * x = 0 := by rw [hx, mul_div_cancel₀ _ hc0, sub_self]
    refine ⟨β, x, ?_, ?_, ?_, hxi, Or.inl ?_⟩
    · rw [hβm]; simp [hdcx]
    · intro i j
      rw [hβm]
      fin_cases i <;> fin_cases j
      · exact sub_mem hbi (mul_mem hai hxi)
      · exact hai
      · simp only [hdcx]; exact zero_mem _
      · exact hci
    · intro i j
      rw [hβim]
      fin_cases i <;> fin_cases j
      · exact hri
      · exact hti
      · exact add_mem hpi (mul_mem hxi hri)
      · exact add_mem hqi (mul_mem hxi hti)
    · rw [hβ]; simp only [mul_assoc, inv_mul_cancel, mul_one]
  ·
    have hclt : Valued.v c < 1 := lt_of_le_of_ne ((mem_iff c).mp hci) hcu
    have hdu : Valued.v d = 1 := by
      have hcq : Valued.v (c * q) < 1 := by
        rw [map_mul]
        calc Valued.v c * Valued.v q ≤ Valued.v c * 1 := mul_le_mul_right ((mem_iff q).mp hqi) _
          _ = Valued.v c := mul_one _
          _ < 1 := hclt
      have hdt : Valued.v (d * t) = 1 := by
        have h := hrow
        rw [add_comm] at h
        have : d * t = 1 - c * q := by rw [← h]; ring
        rw [this, Valuation.map_one_sub_of_lt _ hcq]
      rw [map_mul] at hdt
      have hd1 : Valued.v d ≤ 1 := (mem_iff d).mp hdi
      have ht1 : Valued.v t ≤ 1 := (mem_iff t).mp hti
      by_contra hne
      have hdlt : Valued.v d < 1 := lt_of_le_of_ne hd1 hne
      have : Valued.v d * Valued.v t < 1 := by
        calc Valued.v d * Valued.v t ≤ Valued.v d * 1 := mul_le_mul_right ht1 _
          _ = Valued.v d := mul_one _
          _ < 1 := hdlt
      rw [hdt] at this
      exact lt_irrefl _ this
    have hd0 : d ≠ 0 := by intro h; rw [h, map_zero] at hdu; exact zero_ne_one hdu
    set x : v.adicCompletion F := c / d with hx
    have hxi : x ∈ v.adicCompletionIntegers F := by
      rw [mem_iff, hx, map_div₀, hdu, div_one]; exact (mem_iff c).mp hci
    set β : GL (Fin 2) (v.adicCompletion F) := g * (gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹)⁻¹ with hβ
    have hnm : ((gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![1, 0; x, 1] := by
      rw [gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val, unipotentGL2_coe]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hnim : (((gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![1, 0; -x, 1] := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, gl2Weyl_inv, ← mul_assoc, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val]
      have : (((unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
          = !![1, -x; 0, 1] := rfl
      rw [this]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hβm : (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a - b * x, b; c - d * x, d] := by
      rw [hβ, Matrix.GeneralLinearGroup.coe_mul, hgm, hnim]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp <;> ring
    have hβim : ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![p, q; x * p + r, x * q + t] := by
      rw [hβ, mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.coe_mul, hnm, hgim]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hcdx : c - d * x = 0 := by rw [hx, mul_div_cancel₀ _ hd0, sub_self]
    refine ⟨β, x, ?_, ?_, ?_, hxi, Or.inr ?_⟩
    · rw [hβm]; simp [hcdx]
    · intro i j
      rw [hβm]
      fin_cases i <;> fin_cases j
      · exact sub_mem hai (mul_mem hbi hxi)
      · exact hbi
      · simp only [hcdx]; exact zero_mem _
      · exact hdi
    · intro i j
      rw [hβim]
      fin_cases i <;> fin_cases j
      · exact hpi
      · exact hqi
      · exact add_mem (mul_mem hxi hpi) hri
      · exact add_mem (mul_mem hxi hqi) hti
    · rw [hβ]; simp only [mul_assoc, inv_mul_cancel, mul_one]

end S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
end P2MW
export P2MW.S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral (solution)
