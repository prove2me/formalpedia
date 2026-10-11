-- Prove2me | solution 1 for AsymptoticOperator.inW12_of_forall_inner
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:09:19.574428+00:00
-- url     : https://prove2.me/submissions/e9061537-80d4-41c7-b127-cdffb2927eb1

import Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao4_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

/-- Fourier coefficients of a real function are conjugate-symmetric. -/
lemma ao4_coeff_neg {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f (-k) i = conj (coeff f k i) := by
  rw [ao4_coeff_apply, ao4_coeff_apply]
  simp only [fourierCoeff]
  rw [← integral_conj]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal, neg_neg, fourier_neg,
    Complex.conj_conj]

lemma ao4_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao4_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The symbol `v ↦ -2πik J₀ v` of `-J₀ ∂ₜ` at frequency `k`. -/
noncomputable def ao4T {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) : Fin n ⊕ Fin n → ℂ :=
  -(((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v)

lemma ao4T_neg {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) (i : Fin n ⊕ Fin n) :
    ao4T (-k) (fun j => conj (v j)) i = conj (ao4T k v i) := by
  rcases i with a | a <;>
  · simp only [ao4T, Pi.smul_apply, smul_eq_mul, ao4_J_inl, ao4_J_inr, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring

lemma ao4T_symm {n : ℕ} (k : ℤ) (a b : Fin n ⊕ Fin n → ℂ) :
    ∑ i, conj (ao4T k a i) * b i = ∑ i, conj (a i) * ao4T k b i := by
  simp only [ao4T, Fintype.sum_sum_type, Pi.smul_apply, smul_eq_mul, ao4_J_inl, ao4_J_inr,
    map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma ao4T_norm {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ∑ i, ‖ao4T k v i‖ ^ 2 = (2 * Real.pi * k) ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  simp only [ao4T, Fintype.sum_sum_type, Pi.smul_apply, smul_eq_mul, ao4_J_inl, ao4_J_inr,
    norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one, mul_pow,
    sq_abs, Finset.mul_sum, mul_add]
  rw [add_comm]

lemma ao4_re_self {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) :
    (∑ i, conj (v i) * v i).re = ∑ i, ‖v i‖ ^ 2 := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  norm_cast

theorem solution {n : ℕ} (g u : L2 n)
    (h : ∀ f p : L2 n, InW12 f →
      (∀ k : ℤ, coeff p k =
        -((2 * Real.pi * k : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff f k)) →
      inner ℝ p g = inner ℝ f u) :
    InW12 g ∧ ∀ k : ℤ, coeff u k =
      -((2 * Real.pi * k : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff g k) := by
  have hcoef : ∀ k0 : ℤ, coeff u k0 = ao4T k0 (coeff g k0) := by
    intro k0
    let w : ℤ → Fin n ⊕ Fin n → ℂ := fun k => ao4T k (coeff g k) - coeff u k
    have hwneg : ∀ k i, w (-k) i = conj (w k i) := by
      intro k i
      have hg : coeff g (-k) = fun j => conj (coeff g k j) := funext fun j => ao4_coeff_neg g k j
      simp only [w, Pi.sub_apply, map_sub, hg, ao4T_neg, ao4_coeff_neg u]
    let c : ℤ → Fin n ⊕ Fin n → ℂ := fun k => if k = k0 ∨ k = -k0 then w k else 0
    have hcsupp : ∀ k ∉ ({k0, -k0} : Finset ℤ), c k = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp [c, hk]
    have hcconj : ∀ k i, c (-k) i = conj (c k i) := by
      intro k i
      by_cases hk : k = k0 ∨ k = -k0
      · have hk' : -k = k0 ∨ -k = -k0 := by omega
        simp only [c, if_pos hk, if_pos hk', hwneg]
      · have hk' : ¬(-k = k0 ∨ -k = -k0) := by omega
        simp [c, if_neg hk, if_neg hk']
    obtain ⟨f, hf⟩ := exists_coeff_eq c
      (summable_of_ne_finset_zero (s := {k0, -k0}) fun k hk => by simp [hcsupp k hk]) hcconj
    let d : ℤ → Fin n ⊕ Fin n → ℂ := fun k => ao4T k (c k)
    have hdsupp : ∀ k ∉ ({k0, -k0} : Finset ℤ), d k = 0 := by
      intro k hk
      simp [d, hcsupp k hk, ao4T]
    have hdconj : ∀ k i, d (-k) i = conj (d k i) := by
      intro k i
      have hc : c (-k) = fun j => conj (c k j) := funext fun j => hcconj k j
      simp only [d, hc, ao4T_neg]
    obtain ⟨p, hp⟩ := exists_coeff_eq d
      (summable_of_ne_finset_zero (s := {k0, -k0}) fun k hk => by simp [hdsupp k hk]) hdconj
    have hfW : InW12 f :=
      summable_of_ne_finset_zero (s := {k0, -k0}) fun k hk => by simp [hf k, hcsupp k hk]
    have hin := h f p hfW fun k => by rw [hp k, hf k]; rfl
    have hP := (hasSum_inner_coeff p g).sub (hasSum_inner_coeff f u)
    rw [hin, sub_self] at hP
    have hterm : ∀ k, (∑ i, conj (coeff p k i) * coeff g k i).re -
        (∑ i, conj (coeff f k i) * coeff u k i).re = (∑ i, conj (c k i) * w k i).re := by
      intro k
      rw [hp k, hf k, ← Complex.sub_re]
      simp only [d]
      rw [ao4T_symm, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, Pi.sub_apply]
      ring
    simp only [hterm] at hP
    have hnn : ∀ k, 0 ≤ (∑ i, conj (c k i) * w k i).re := by
      intro k
      by_cases hk : k = k0 ∨ k = -k0
      · simp only [c, if_pos hk, ao4_re_self]
        positivity
      · simp [c, if_neg hk]
    have h0 := congrFun ((hasSum_zero_iff_of_nonneg hnn).1 hP) k0
    simp only [c, if_pos (Or.inl rfl : k0 = k0 ∨ k0 = -k0), ao4_re_self, Pi.zero_apply] at h0
    have hw0 : ∀ i, w k0 i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h0 i
        (Finset.mem_univ i)
      simpa using this
    funext i
    have := hw0 i
    simp only [w, Pi.sub_apply, sub_eq_zero] at this
    exact this.symm
  refine ⟨?_, fun k => hcoef k⟩
  have hg := (hasSum_inner_coeff g g).summable
  have hu := (hasSum_inner_coeff u u).summable
  simp only [ao4_re_self, hcoef, ao4T_norm] at hg hu
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  have e : (fun k : ℤ => (1 + (k : ℝ) ^ 2) * ∑ i, ‖coeff g k i‖ ^ 2) =
      fun k : ℤ => ∑ i, ‖coeff g k i‖ ^ 2 +
        ((2 * Real.pi) ^ 2)⁻¹ * ((2 * Real.pi * k) ^ 2 * ∑ i, ‖coeff g k i‖ ^ 2) := by
    funext k
    field_simp
  unfold InW12
  rw [e]
  exact hg.add (hu.mul_left _)
