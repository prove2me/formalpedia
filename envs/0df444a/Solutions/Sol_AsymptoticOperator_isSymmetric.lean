-- Prove2me | solution 1 for AsymptoticOperator.isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T16:41:53.676199+00:00
-- url     : https://prove2.me/submissions/8d52262e-d16e-4535-9126-8b286d5bc93d

import Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
import Theorems.Thm_AsymptoticOperator_inner_mul_symm
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq_coeffMul

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao3_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao3_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The first-order symbol `D = -(c i) J₀` (`c` real) is Hermitian on `ℂ²ⁿ`. -/
lemma ao3_symbol_symm {n : ℕ} (c : ℝ) (a b : Fin n ⊕ Fin n → ℂ) :
    ∑ i, conj ((-((c : ℂ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ a)) i) * b i =
      ∑ i, conj (a i) * (-((c : ℂ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ b)) i := by
  simp only [Fintype.sum_sum_type, Pi.smul_apply, smul_eq_mul, ao3_J_inl, ao3_J_inr, map_mul,
    map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma ao3_main {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) (f u g v : L2 n)
    (hu : IsAsymptoticAction S f u) (hv : IsAsymptoticAction S g v) :
    inner ℝ u g = inner ℝ f v := by
  obtain ⟨m, hm⟩ := exists_coeff_eq_coeffMul S f
  obtain ⟨m', hm'⟩ := exists_coeff_eq_coeffMul S g
  have hP := (hasSum_inner_coeff u g).add (hasSum_inner_coeff m g)
  have hQ := (hasSum_inner_coeff f v).add (hasSum_inner_coeff f m')
  have e : (fun k : ℤ => (∑ i, conj (coeff u k i) * coeff g k i).re +
        (∑ i, conj (coeff m k i) * coeff g k i).re) =
      fun k : ℤ => (∑ i, conj (coeff f k i) * coeff v k i).re +
        (∑ i, conj (coeff f k i) * coeff m' k i).re := by
    funext k
    rw [← Complex.add_re, ← Complex.add_re, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have h1 : ∀ i, conj (coeff u k i) * coeff g k i + conj (coeff m k i) * coeff g k i =
        conj ((-(((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) •
          ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff f k)) i) * coeff g k i := by
      intro i
      rw [hu.2 k, hm k, Pi.sub_apply, map_sub]
      ring
    have h2 : ∀ i, conj (coeff f k i) * coeff v k i + conj (coeff f k i) * coeff m' k i =
        conj (coeff f k i) * (-(((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) •
          ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff g k)) i := by
      intro i
      rw [hv.2 k, hm' k, Pi.sub_apply]
      ring
    simp only [h1, h2]
    rw [ao3_symbol_symm]
  rw [e] at hP
  have hsum := hP.unique hQ
  have hmul := inner_mul_symm S hS f g m m' hm hm'
  linarith

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    (asymptoticOperator S).IsFormalAdjoint (asymptoticOperator S) := by
  by_cases hex : ∃ A : L2 n →ₗ.[ℝ] L2 n, (A.graph : Set (L2 n × L2 n)) = graphSet S
  · have hA : asymptoticOperator S = hex.choose := by
      unfold asymptoticOperator; rw [dif_pos hex]
    have hgraph := hex.choose_spec
    rw [hA]
    intro x y
    have hx : IsAsymptoticAction S x (hex.choose x) := by
      have h := hex.choose.mem_graph x
      rw [← SetLike.mem_coe, hgraph] at h
      exact h
    have hy : IsAsymptoticAction S y (hex.choose y) := by
      have h := hex.choose.mem_graph y
      rw [← SetLike.mem_coe, hgraph] at h
      exact h
    exact ao3_main S hS x _ y _ hx hy
  · have hA : asymptoticOperator S = 0 := by
      unfold asymptoticOperator; rw [dif_neg hex]
    rw [hA]
    intro x y
    simp [LinearPMap.zero_apply]
