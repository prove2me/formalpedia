-- Prove2me | solution 1 for ArithmeticE.polynomial_derivative_frame_minimal_equation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T17:34:13.042674+00:00
-- url     : https://prove2.me/submissions/5b455f9f-eb9b-44b1-9fe2-5c1d787a2891

import Definitions.Def_polynomialDerivativeFrame

noncomputable section
open scoped BigOperators
open ArithmeticE Polynomial Matrix
namespace CyclicFrame

private lemma combine_rows {n : ℕ} (g : Fin n → PowerSeries ℂ)
    (A : Matrix (Fin n) (Fin n) (Polynomial ℂ)) (c : Fin n → Polynomial ℂ) :
    (∑ i, (c i : PowerSeries ℂ) * ∑ j, (A i j : PowerSeries ℂ) * g j) =
      ∑ j, ((c ᵥ* A) j : PowerSeries ℂ) * g j := by
  simp only [Matrix.vecMul, dotProduct, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

private lemma vecMul_injective {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Polynomial ℂ)) (hA : A.det ≠ 0)
    (c : Fin n → Polynomial ℂ) (hc : c ᵥ* A = 0) : c = 0 := by
  have h := congrArg (fun v => v ᵥ* A.adjugate) hc
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
    Matrix.vecMul_one, Matrix.zero_vecMul] at h
  funext i
  have hi := congrFun h i
  change A.det * c i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left hA

lemma frame_equation {F : PowerSeries ℂ} {ξ : ℂ} {n : ℕ}
    (hf : PolynomialDerivativeFrame F ξ n) :
    ∃ p : ℕ → Polynomial ℂ, MinimalEquation p n F ∧ (p n).eval ξ ≠ 0 := by
  classical
  obtain ⟨d,g,A,b,hd,hg,hlo,hhi,hA⟩ := hf
  have hd0 : (d : PowerSeries ℂ) ≠ 0 := by
    intro h
    have : d = 0 := Polynomial.coe_injective ℂ (by simpa using h)
    exact hd (by simp [this])
  have hA0 : A.det ≠ 0 := by intro h; exact hA (by simp [h])
  let c : Fin n → Polynomial ℂ := b ᵥ* A.adjugate
  have hc : c ᵥ* A = A.det • b := by
    dsimp [c]
    rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul,
      Matrix.vecMul_one]
  let p : ℕ → Polynomial ℂ := fun k =>
    if h : k < n then -c ⟨k,h⟩ else if k = n then A.det else 0
  have hpn : p n = A.det := by simp [p]
  have hop : operatorValue p n F =
      (A.det : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[n] F -
        ∑ i : Fin n, (c i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] F := by
    rw [operatorValue, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
    simp only [p, Fin.is_lt, dite_true, Polynomial.coe_neg, neg_mul,
      Finset.sum_neg_distrib, lt_self_iff_false, dite_false, ↓reduceIte]
    ring
  have heq : operatorValue p n F = 0 := by
    apply (mul_eq_zero.mp (show (d : PowerSeries ℂ) * operatorValue p n F = 0 from ?_)).resolve_left hd0
    rw [hop, mul_sub, Finset.mul_sum]
    have hlo' : ∀ i : Fin n,
        (d : PowerSeries ℂ) * ((c i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] F) =
          (c i : PowerSeries ℂ) * ∑ j, (A i j : PowerSeries ℂ) * g j := by
      intro i
      rw [← mul_assoc, mul_comm (d : PowerSeries ℂ), mul_assoc, hlo i]
    simp_rw [hlo']
    rw [← mul_assoc, mul_comm (d : PowerSeries ℂ), mul_assoc, hhi,
      combine_rows, hc]
    simp [Finset.mul_sum, mul_assoc]
  refine ⟨p, ⟨by simpa [hpn] using hA0, heq, ?_⟩, by simpa [hpn] using hA⟩
  intro k hk q hq he
  let v : Fin n → Polynomial ℂ := fun i => if i.val ≤ k then q i.val else 0
  have hvsum : (∑ i : Fin n, (v i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] F) =
      operatorValue q k F := by
    dsimp [v, operatorValue]
    simp only [apply_ite (fun p : Polynomial ℂ => (p : PowerSeries ℂ)),
      Polynomial.coe_zero, ite_mul, zero_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      if i ≤ k then (q i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i] F else 0) n]
    calc
      _ = ∑ i ∈ Finset.range (k + 1),
          if i ≤ k then (q i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i] F else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ n))
        intro i hi hnot
        simp only [Finset.mem_range, not_lt] at hnot
        simp [show ¬ i ≤ k by omega]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [show i ≤ k from Nat.le_of_lt_succ (Finset.mem_range.mp hi)]
  have hrel : ∑ j, ((v ᵥ* A) j : PowerSeries ℂ) * g j = 0 := by
    rw [← combine_rows]
    simp_rw [← hlo]
    have he' := congrArg (fun x : PowerSeries ℂ => (d : PowerSeries ℂ) * x) (hvsum.trans he)
    simpa [Finset.mul_sum, mul_left_comm] using he'
  have hvA : v ᵥ* A = 0 := funext (hg _ hrel)
  have hv := congrFun (vecMul_injective A hA0 v hvA) ⟨k,hk⟩
  exact hq (by simpa [v] using hv)

end CyclicFrame

theorem solution (F : PowerSeries ℂ) (ξ : ℂ) (n : ℕ)
    (hf : PolynomialDerivativeFrame F ξ n) :
    ∃ p : ℕ → Polynomial ℂ, MinimalEquation p n F ∧ (p n).eval ξ ≠ 0 := by
  exact CyclicFrame.frame_equation hf

#print axioms solution
