-- Prove2me | solution 1 for AsymptoticOperator.compact_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:39:52.260928+00:00
-- url     : https://prove2.me/submissions/3ba603c0-add4-4180-91b8-690c8f4b92fa

import Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
import Theorems.Thm_AsymptoticOperator_graph_existsUnique
import Theorems.Thm_AsymptoticOperator_exists_isCompactOperator_fourierMultiplier
import Theorems.Thm_AsymptoticOperator_exists_clm_coeffMul
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate Filter Topology

/-! Coefficient algebra on `L²` and the symbol of `(-J₀∂ₜ - π)⁻¹`. -/

lemma ao7_cx_int {n : ℕ} (f : L2 n) :
    Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i) :
    Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp ((Lp.memLp f).integrable one_le_two)

lemma ao7_coeff_add {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f + g : L2 n) : UnitAddCircle → Vec n) k = coeff f k + coeff g k := by
  have h : (fun t => complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => complexify (f t)) + (fun t => complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    rw [ht]; funext i; simp [complexify]
  simp only [coeff]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (ao7_cx_int f) (ao7_cx_int g)]
  rfl

lemma ao7_coeff_smul {n : ℕ} (c : ℝ) (f : L2 n) (k : ℤ) :
    coeff ((c • f : L2 n) : UnitAddCircle → Vec n) k = (c : ℂ) • coeff f k := by
  have h : (fun t => complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    rw [ht]; funext i; simp [complexify]
  simp only [coeff]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma ao7_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, ao7_coeff_add, ao7_coeff_smul]
  simp [sub_eq_add_neg]

lemma ao7_ext {n : ℕ} (f g : L2 n) (h : ∀ k, coeff f k = coeff g k) : f = g :=
  sub_eq_zero.1 (eq_zero_of_coeff_eq_zero _ fun k => by rw [ao7_coeff_sub, h k, sub_self])

lemma ao7_re_self {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) :
    (∑ i, conj (v i) * v i).re = ∑ i, ‖v i‖ ^ 2 := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  norm_cast

lemma ao7_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao7_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The symbol `v ↦ -2πik J₀ v` of `-J₀ ∂ₜ` at frequency `k`. -/
noncomputable def ao7T {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) : Fin n ⊕ Fin n → ℂ :=
  -(((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v)

lemma ao7T_norm {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ∑ i, ‖ao7T k v i‖ ^ 2 = (2 * Real.pi * k) ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  simp only [ao7T, Fintype.sum_sum_type, Pi.smul_apply, smul_eq_mul, ao7_J_inl, ao7_J_inr,
    norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one, mul_pow,
    sq_abs, Finset.mul_sum, mul_add]
  rw [add_comm]

/-- `T² = (2πk)²`. -/
lemma ao7T_T {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ao7T k (ao7T k v) = (((2 * Real.pi * k) ^ 2 : ℝ) : ℂ) • v := by
  funext i
  rcases i with a | a
  · simp only [ao7T, Pi.smul_apply, smul_eq_mul, mulVec_smul, ao7_J_inl, ao7_J_inr]
    push_cast
    linear_combination (-(4 * Real.pi ^ 2 * (k : ℂ) ^ 2) * v (Sum.inl a)) * Complex.I_sq
  · simp only [ao7T, Pi.smul_apply, smul_eq_mul, mulVec_smul, ao7_J_inl, ao7_J_inr]
    push_cast
    linear_combination (-(4 * Real.pi ^ 2 * (k : ℂ) ^ 2) * v (Sum.inr a)) * Complex.I_sq

lemma ao7T_add {n : ℕ} (k : ℤ) (v w : Fin n ⊕ Fin n → ℂ) :
    ao7T k (v + w) = ao7T k v + ao7T k w := by
  simp only [ao7T, mulVec_add, smul_add]

lemma ao7T_smul {n : ℕ} (k : ℤ) (a : ℂ) (v : Fin n ⊕ Fin n → ℂ) :
    ao7T k (a • v) = a • ao7T k v := by
  simp only [ao7T, mulVec_smul, smul_comm a]

lemma ao7T_sub {n : ℕ} (k : ℤ) (v w : Fin n ⊕ Fin n → ℂ) :
    ao7T k (v - w) = ao7T k v - ao7T k w := by
  simp only [ao7T, mulVec_sub, smul_sub]

lemma ao7_den_ne {k : ℤ} : Real.pi ^ 2 * (4 * (k : ℝ) ^ 2 - 1) ≠ 0 := by
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  refine mul_ne_zero hpi ?_
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [sq_abs (k : ℝ)]
    linarith

/-- The symbol of `(-J₀∂ₜ - π)⁻¹` at frequency `k`: `(T + π)/(π²(4k² - 1))`. -/
noncomputable def ao7m (n : ℕ) (k : ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (((Real.pi ^ 2 * (4 * (k : ℝ) ^ 2 - 1) : ℝ) : ℂ))⁻¹ •
    (-(((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) • (J₀ n).map (fun x : ℝ => (x : ℂ)) +
      (Real.pi : ℂ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))

lemma ao7m_mulVec {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ao7m n k *ᵥ v = (((Real.pi ^ 2 * (4 * (k : ℝ) ^ 2 - 1) : ℝ) : ℂ))⁻¹ •
      (ao7T k v + (Real.pi : ℂ) • v) := by
  simp only [ao7m, smul_mulVec, add_mulVec, one_mulVec, ao7T]

lemma ao7m_conj {n : ℕ} (k : ℤ) : ao7m n (-k) = (ao7m n k).map (starRingEnd ℂ) := by
  ext i j
  simp only [ao7m, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Matrix.one_apply, map_mul, map_add, map_inv₀, Complex.conj_ofReal, map_neg, Complex.conj_I]
  push_cast
  split_ifs <;> simp <;> ring

/-- `(T - π) m v = v`. -/
lemma ao7_I1 {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ao7T k (ao7m n k *ᵥ v) - (Real.pi : ℂ) • (ao7m n k *ᵥ v) = v := by
  have hd : ((Real.pi ^ 2 * (4 * (k : ℝ) ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ao7_den_ne
  rw [ao7m_mulVec, ao7T_smul, ao7T_add, ao7T_smul, ao7T_T]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  push_cast
  ring

/-- `m (T - π) v = v`. -/
lemma ao7_I2 {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ao7m n k *ᵥ (ao7T k v - (Real.pi : ℂ) • v) = v := by
  have hd : ((Real.pi ^ 2 * (4 * (k : ℝ) ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ao7_den_ne
  rw [ao7m_mulVec, ao7T_sub, ao7T_smul, ao7T_T]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  push_cast
  ring

lemma ao7m_bound {n : ℕ} (k : ℤ) (v : Fin n ⊕ Fin n → ℂ) :
    ∑ i, ‖(ao7m n k *ᵥ v) i‖ ^ 2 ≤
      10 / (Real.pi ^ 2 * (1 + (k : ℝ) ^ 2)) * ∑ i, ‖v i‖ ^ 2 := by
  rw [ao7m_mulVec]
  set d : ℝ := Real.pi ^ 2 * (4 * (k : ℝ) ^ 2 - 1) with hd
  have hd0 : d ≠ 0 := ao7_den_ne
  have hd2 : 0 < d ^ 2 := lt_of_le_of_ne (sq_nonneg d) (Ne.symm (pow_ne_zero 2 hd0))
  have h1 : ∀ i, ‖((((d : ℂ))⁻¹ • (ao7T k v + (Real.pi : ℂ) • v)) i)‖ ^ 2 ≤
      (d ^ 2)⁻¹ * (2 * ‖ao7T k v i‖ ^ 2 + 2 * Real.pi ^ 2 * ‖v i‖ ^ 2) := by
    intro i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    gcongr
    have h := norm_add_le (ao7T k v i) ((Real.pi : ℂ) * v i)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
    have h0 := norm_nonneg (ao7T k v i + (Real.pi : ℂ) * v i)
    nlinarith [sq_nonneg (‖ao7T k v i‖ - Real.pi * ‖v i‖), mul_le_mul h h h0 (by positivity)]
  have hx : (k : ℝ) = 0 ∨ 1 ≤ (k : ℝ) ^ 2 := by
    rcases eq_or_ne k 0 with hk | hk
    · left; simp [hk]
    · right
      have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
      nlinarith [sq_abs (k : ℝ)]
  have key : 2 * (4 * (k : ℝ) ^ 2 + 1) * (1 + (k : ℝ) ^ 2) ≤ 10 * (4 * (k : ℝ) ^ 2 - 1) ^ 2 := by
    rcases hx with hx | hx
    · rw [hx]; norm_num
    · nlinarith
  have hpi4 : 0 < Real.pi ^ 4 := by positivity
  calc ∑ i, ‖((((d : ℂ))⁻¹ • (ao7T k v + (Real.pi : ℂ) • v)) i)‖ ^ 2
      ≤ ∑ i, (d ^ 2)⁻¹ * (2 * ‖ao7T k v i‖ ^ 2 + 2 * Real.pi ^ 2 * ‖v i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = (d ^ 2)⁻¹ * (2 * (2 * Real.pi * k) ^ 2 + 2 * Real.pi ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ao7T_norm]
        ring
    _ ≤ 10 / (Real.pi ^ 2 * (1 + (k : ℝ) ^ 2)) * ∑ i, ‖v i‖ ^ 2 := by
        gcongr ?_ * _
        rw [inv_mul_eq_div, div_le_div_iff₀ hd2 (by positivity), hd]
        nlinarith [mul_le_mul_of_nonneg_left key hpi4.le]

lemma ao7_tendsto :
    Tendsto (fun k : ℤ => 10 / (Real.pi ^ 2 * (1 + (k : ℝ) ^ 2))) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨N, hN⟩ := exists_nat_gt (10 / (Real.pi ^ 2 * ε))
  refine (Set.finite_Icc (-(N : ℤ)) N).subset fun k hk => ?_
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hk
  rw [Set.mem_Icc]
  by_contra hk'
  have hkZ : (N : ℤ) < |k| := by
    rcases le_or_gt 0 k with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  have hkR : (N : ℝ) < |(k : ℝ)| := by exact_mod_cast hkZ
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (1 : ℤ) ≤ |k| := by omega
    exact_mod_cast h1
  have hsq : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by nlinarith [sq_abs (k : ℝ)]
  have hpos : 0 < Real.pi ^ 2 * (1 + (k : ℝ) ^ 2) := by positivity
  rw [abs_of_pos (by positivity), le_div_iff₀ hpos] at hk
  have h3 : 10 / (Real.pi ^ 2 * ε) < (k : ℝ) ^ 2 := by linarith
  rw [div_lt_iff₀ (by positivity)] at h3
  nlinarith [Real.pi_pos]

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate Filter Topology

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) (μ : ℝ)
    (hμ : eigenspace (asymptoticOperator S) μ = ⊥) :
    ∃ R : L2 n →L[ℝ] L2 n, IsCompactOperator R ∧
      (∀ g : L2 n, ∃ h : R g ∈ (asymptoticOperator S).domain,
        (asymptoticOperator S) ⟨R g, h⟩ - μ • R g = g) ∧
      ∀ f : (asymptoticOperator S).domain,
        R ((asymptoticOperator S) f - μ • (f : L2 n)) = f := by
  -- the graph of `A_S` is `graphSet S`
  have hex : ∃ A' : L2 n →ₗ.[ℝ] L2 n, (A'.graph : Set (L2 n × L2 n)) = graphSet S :=
    (graph_existsUnique S).exists
  have hgraph : ((asymptoticOperator S).graph : Set (L2 n × L2 n)) = graphSet S := by
    rw [asymptoticOperator, dif_pos hex]
    exact hex.choose_spec
  have hact : ∀ x : (asymptoticOperator S).domain,
      IsAsymptoticAction S x (asymptoticOperator S x) := by
    intro x
    have : ((x : L2 n), asymptoticOperator S x) ∈
        ((asymptoticOperator S).graph : Set (L2 n × L2 n)) := (asymptoticOperator S).mem_graph x
    rw [hgraph] at this
    exact this
  have hdom : ∀ f g : L2 n, IsAsymptoticAction S f g →
      ∃ h : f ∈ (asymptoticOperator S).domain, asymptoticOperator S ⟨f, h⟩ = g := by
    intro f g hfg
    have : (f, g) ∈ ((asymptoticOperator S).graph : Set (L2 n × L2 n)) := by
      rw [hgraph]; exact hfg
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 this
    have hy1' : (y : L2 n) = f := hy1
    refine ⟨hy1' ▸ y.2, ?_⟩
    have hy2' : asymptoticOperator S y = g := hy2
    rw [← hy2']
    congr 1
    exact Subtype.ext hy1'.symm
  -- the free resolvent `R₀ = (-J₀∂ₜ - π)⁻¹` and the bounded part `B = S + (μ - π)`
  obtain ⟨B0, hB0⟩ := exists_clm_coeffMul S
  obtain ⟨R0, hR0c, hR0⟩ := exists_isCompactOperator_fourierMultiplier (ao7m n) ao7m_conj
    (fun k : ℤ => 10 / (Real.pi ^ 2 * (1 + (k : ℝ) ^ 2))) ao7_tendsto ao7m_bound
  let B : L2 n →L[ℝ] L2 n := B0 + (μ - Real.pi) • ContinuousLinearMap.id ℝ (L2 n)
  have hB : ∀ (f : L2 n) (k : ℤ),
      coeff (B f) k = coeffMul S f k + ((μ - Real.pi : ℝ) : ℂ) • coeff f k := by
    intro f k
    simp only [B, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [ao7_coeff_add, ao7_coeff_smul, hB0]
  have hpar : ∀ g : L2 n, Summable fun k : ℤ => ∑ i, ‖coeff g k i‖ ^ 2 := fun g => by
    have h := (hasSum_inner_coeff g g).summable
    simpa only [ao7_re_self] using h
  have hF1W : ∀ g : L2 n, InW12 (R0 g) := by
    intro g
    unfold InW12
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hpar g).mul_left (10 / Real.pi ^ 2))
    rw [hR0]
    have hpos : 0 < 1 + (k : ℝ) ^ 2 := by positivity
    calc (1 + (k : ℝ) ^ 2) * ∑ i, ‖(ao7m n k *ᵥ coeff g k) i‖ ^ 2
        ≤ (1 + (k : ℝ) ^ 2) *
            (10 / (Real.pi ^ 2 * (1 + (k : ℝ) ^ 2)) * ∑ i, ‖coeff g k i‖ ^ 2) := by
          gcongr; exact ao7m_bound k _
      _ = 10 / Real.pi ^ 2 * ∑ i, ‖coeff g k i‖ ^ 2 := by field_simp
  have hF1 : ∀ (g : L2 n) (k : ℤ),
      coeff g k = ao7T k (coeff (R0 g) k) - (Real.pi : ℂ) • coeff (R0 g) k := by
    intro g k
    rw [hR0]
    exact (ao7_I1 k _).symm
  have hF2 : ∀ f h : L2 n,
      (∀ k, coeff h k = ao7T k (coeff f k) - (Real.pi : ℂ) • coeff f k) → R0 h = f := by
    intro f h hh
    apply ao7_ext
    intro k
    rw [hR0, hh]
    exact ao7_I2 k _
  -- the compact perturbation `K = B R₀` and the Fredholm alternative
  let K : L2 n →L[ℝ] L2 n := B.comp R0
  have hKc : IsCompactOperator K := hR0c.clm_comp B
  have hnot : ¬ Module.End.HasEigenvalue (K : Module.End ℝ (L2 n)) 1 := by
    intro hev
    obtain ⟨h, hh⟩ := hev.exists_hasEigenvector
    have hKh : B (R0 h) = h := by
      have := Module.End.mem_eigenspace_iff.1 hh.1
      simpa [K] using this
    have hcoef : ∀ k : ℤ, coeff ((μ • R0 h : L2 n)) k =
        -((2 * Real.pi * k : ℝ) * Complex.I) •
          ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff (R0 h) k) - coeffMul S (R0 h) k := by
      intro k
      have e1 := hF1 h k
      have e2 := hB (R0 h) k
      rw [hKh] at e2
      rw [ao7_coeff_smul]
      funext i
      have e1' := congrFun e1 i
      have e2' := congrFun e2 i
      simp only [ao7T, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1' e2' ⊢
      push_cast at e1' e2' ⊢
      linear_combination e1' - e2'
    obtain ⟨hfd, hAf⟩ := hdom (R0 h) (μ • R0 h) ⟨hF1W h, hcoef⟩
    have hmem : (⟨R0 h, hfd⟩ : (asymptoticOperator S).domain) ∈
        eigenspace (asymptoticOperator S) μ := by
      simp only [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Submodule.subtype_apply]
      change asymptoticOperator S ⟨R0 h, hfd⟩ - μ • R0 h = 0
      rw [hAf, sub_self]
    rw [hμ, Submodule.mem_bot] at hmem
    have hf0 : R0 h = 0 := congrArg Subtype.val hmem
    apply hh.2
    rw [← hKh, hf0, map_zero]
  have hres := (hKc.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left hnot
  rw [spectrum.mem_resolventSet_iff, map_one] at hres
  let Q : L2 n →L[ℝ] L2 n := ↑hres.unit⁻¹
  have hQ1 : ∀ g, Q g - B (R0 (Q g)) = g := by
    intro g
    have := congrArg (fun T : L2 n →L[ℝ] L2 n => T g) hres.mul_val_inv
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at this
    exact this
  have hQ2 : ∀ h, Q (h - B (R0 h)) = h := by
    intro h
    have := congrArg (fun T : L2 n →L[ℝ] L2 n => T h) hres.val_inv_mul
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at this
    exact this
  refine ⟨R0.comp Q, hR0c.comp_clm Q, fun g => ?_, fun f => ?_⟩
  · have hc : ∀ k : ℤ, coeff ((g + μ • R0 (Q g) : L2 n)) k =
        -((2 * Real.pi * k : ℝ) * Complex.I) •
          ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff (R0 (Q g)) k) -
            coeffMul S (R0 (Q g)) k := by
      intro k
      have e1 := hF1 (Q g) k
      have e2 := hB (R0 (Q g)) k
      have e3 : coeff g k = coeff (Q g) k - coeff (B (R0 (Q g))) k := by
        conv_lhs => rw [← hQ1 g]
        exact ao7_coeff_sub _ _ k
      rw [ao7_coeff_add, ao7_coeff_smul, e3, e2, e1]
      funext i
      simp only [ao7T, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    obtain ⟨hd, hAf⟩ := hdom _ _ ⟨hF1W (Q g), hc⟩
    refine ⟨hd, ?_⟩
    change asymptoticOperator S ⟨R0 (Q g), hd⟩ - μ • R0 (Q g) = g
    rw [hAf, add_sub_cancel_right]
  · have hRh : R0 (asymptoticOperator S f - μ • (f : L2 n) + B f) = f := by
      apply hF2
      intro k
      obtain ⟨-, hk⟩ := hact f
      rw [ao7_coeff_add, ao7_coeff_sub, ao7_coeff_smul, hB, hk k]
      funext i
      simp only [ao7T, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hKh : (asymptoticOperator S f - μ • (f : L2 n) + B f) -
        B (R0 (asymptoticOperator S f - μ • (f : L2 n) + B f)) =
          asymptoticOperator S f - μ • (f : L2 n) := by
      rw [hRh, add_sub_cancel_right]
    change R0 (Q (asymptoticOperator S f - μ • (f : L2 n))) = f
    rw [← hKh, hQ2, hRh]
