-- Prove2me | solution 1 for AsymptoticOperator.symbol_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:50:53.120973+00:00
-- url     : https://prove2.me/submissions/fe7ea7a8-8cff-42d0-b4d7-5bd95bd1a5ae

import Definitions.Def_AsymptoticOperator_Setting

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao9_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao9_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The eigenvalue equation of the symbol `-2πim J₀` in components. -/
lemma ao9_comp {n : ℕ} (μ : ℝ) (m : ℤ) (c : Fin n ⊕ Fin n → ℂ)
    (h : (μ : ℂ) • c = -((2 * Real.pi * m : ℝ) * Complex.I) •
      ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ c)) (a : Fin n) :
    (μ : ℂ) * c (Sum.inl a) = ((2 * Real.pi * m : ℝ) : ℂ) * Complex.I * c (Sum.inr a) ∧
      (μ : ℂ) * c (Sum.inr a) = -(((2 * Real.pi * m : ℝ) : ℂ) * Complex.I * c (Sum.inl a)) := by
  have hl := congrFun h (Sum.inl a)
  have hr := congrFun h (Sum.inr a)
  simp only [Pi.smul_apply, smul_eq_mul, ao9_J_inl, ao9_J_inr] at hl hr
  constructor
  · rw [hl]; ring
  · rw [hr]; ring

theorem solution {n : ℕ} (μ : ℝ) (m : ℤ) (c : Fin n ⊕ Fin n → ℂ)
    (h : (μ : ℂ) • c = -((2 * Real.pi * m : ℝ) * Complex.I) •
      ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ c)) (i : Fin n ⊕ Fin n) :
    ((μ : ℂ) - ((2 * Real.pi * m : ℝ) : ℂ)) * ((μ : ℂ) + ((2 * Real.pi * m : ℝ) : ℂ)) * c i = 0 := by
  set a : ℂ := ((2 * Real.pi * m : ℝ) : ℂ)
  rcases i with b | b
  · obtain ⟨hl, hr⟩ := ao9_comp μ m c h b
    linear_combination (μ : ℂ) * hl + a * Complex.I * hr + (-a ^ 2 * c (Sum.inl b)) * Complex.I_sq
  · obtain ⟨hl, hr⟩ := ao9_comp μ m c h b
    linear_combination (μ : ℂ) * hr - a * Complex.I * hl + (-a ^ 2 * c (Sum.inr b)) * Complex.I_sq
