-- Prove2me | solution 1 for AsymptoticOperator.spectrum_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:19:53.65424+00:00
-- url     : https://prove2.me/submissions/126526a8-26d1-45f6-b1a3-17d46ef7b0b5

import Theorems.Thm_AsymptoticOperator_hasSum_inner_self_of_hilbertBasis_eigenvectors
import Theorems.Thm_AsymptoticOperator_hasDiscreteEigenbasis
import Theorems.Thm_AsymptoticOperator_isSymmetric
import Theorems.Thm_AsymptoticOperator_graph_existsUnique
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate Filter Topology

/-! Coefficient algebra on `L²`. -/

lemma ao8_cx_int {n : ℕ} (f : L2 n) :
    Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i) :
    Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp ((Lp.memLp f).integrable one_le_two)

lemma ao8_coeff_add {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f + g : L2 n) : UnitAddCircle → Vec n) k = coeff f k + coeff g k := by
  have h : (fun t => complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => complexify (f t)) + (fun t => complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    rw [ht]; funext i; simp [complexify]
  simp only [coeff]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (ao8_cx_int f) (ao8_cx_int g)]
  rfl

lemma ao8_coeff_smul {n : ℕ} (c : ℝ) (f : L2 n) (k : ℤ) :
    coeff ((c • f : L2 n) : UnitAddCircle → Vec n) k = (c : ℂ) • coeff f k := by
  have h : (fun t => complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    rw [ht]; funext i; simp [complexify]
  simp only [coeff]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma ao8_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, ao8_coeff_add, ao8_coeff_smul]
  simp [sub_eq_add_neg]

lemma ao8_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k :=
  eval_integral (integrable_pi_iff.1 ((ao8_cx_int f).fourier_smul (-k))) i

lemma ao8_integrable_fourier (m : ℤ) :
    Integrable (fourier m : UnitAddCircle → ℂ) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  ((Lp.memLp (fourierLp 2 m)).integrable one_le_two).congr (coeFn_fourierLp 2 m)

/-- The real test function `t ↦ Re(z e^{2πikt}) eⱼ`. -/
noncomputable def ao8ψ {n : ℕ} (k : ℤ) (j : Fin n ⊕ Fin n) (z : ℂ) : C(UnitAddCircle, Vec n) :=
  ⟨fun t => (z * fourier k t).re • EuclideanSpace.single j (1 : ℝ),
    (Complex.continuous_re.comp (continuous_const.mul (fourier k).continuous)).smul
      continuous_const⟩

lemma ao8_re_eq (z : ℂ) (k : ℤ) (t : UnitAddCircle) :
    (((z * fourier k t).re : ℝ) : ℂ) = z / 2 * fourier k t + conj z / 2 * fourier (-k) t := by
  rw [Complex.re_eq_add_conj, map_mul, ← fourier_neg]
  ring

lemma ao8_coeff_ψ {n : ℕ} (k m : ℤ) (j i : Fin n ⊕ Fin n) (z : ℂ) :
    coeff (ContinuousMap.toLp (E := Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ
        (ao8ψ k j z)) m i =
      (if i = j then (1 : ℂ) else 0) *
        (z / 2 * (Pi.single k (1 : ℂ) : ℤ → ℂ) m + conj z / 2 * (Pi.single (-k) (1 : ℂ) : ℤ → ℂ) m) := by
  rw [ao8_coeff_apply]
  have hae : (fun t => (((ContinuousMap.toLp (E := Vec n) 2
        (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ (ao8ψ k j z)) t i : ℝ) : ℂ))
      =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (if i = j then (1 : ℂ) else 0) •
        ((z / 2) • (fourier k : UnitAddCircle → ℂ) + (conj z / 2) • (fourier (-k) : UnitAddCircle → ℂ)) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := Vec n) (p := 2)
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (𝕜 := ℝ) (ao8ψ k j z)] with t ht
    rw [ht]
    simp only [ao8ψ, ContinuousMap.coe_mk, PiLp.smul_apply, PiLp.single_apply,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    split_ifs <;> simp only [mul_one, one_mul, mul_zero, zero_mul, Complex.ofReal_zero, ao8_re_eq,
      smul_eq_mul]
  rw [fourierCoeff_congr_ae hae, fourierCoeff.const_smul,
    fourierCoeff.add ((ao8_integrable_fourier k).smul _) ((ao8_integrable_fourier (-k)).smul _),
    Pi.add_apply, fourierCoeff.const_smul, fourierCoeff.const_smul, fourierCoeff_fourier, fourierCoeff_fourier]
  simp only [smul_eq_mul]

/-- An explicit `L²` representative of `t ↦ S(t) f(t)` with its pointwise description. -/
lemma ao8_exists_mul {n : ℕ} (S : C(UnitAddCircle, Mat n)) (f : L2 n) :
    ∃ m : L2 n, (∀ k : ℤ, coeff m k = coeffMul S f k) ∧
      ∃ M : ℝ, ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), ‖m t‖ ≤ M * ‖f t‖ := by
  let E := toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)
  have hE : Continuous fun A : Mat n => E A :=
    LinearMap.continuous_of_finiteDimensional E.toAlgEquiv.toLinearMap
  let T : C(UnitAddCircle, Vec n →L[ℝ] Vec n) := ⟨fun t => E (S t), hE.comp S.continuous⟩
  have hmeas : AEStronglyMeasurable (fun t => T t (f t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    have hc : Continuous fun p : (Vec n →L[ℝ] Vec n) × Vec n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hc.comp_aestronglyMeasurable
      (T.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f))
  have hle : ∀ t, ‖T t (f t)‖ ≤ ‖T‖ * ‖f t‖ := fun t =>
    ((T t).le_opNorm (f t)).trans
      (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm t) (norm_nonneg _))
  have hmem : MemLp (fun t => T t (f t)) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (Lp.memLp f).of_le_mul hmeas (ae_of_all _ hle)
  refine ⟨hmem.toLp _, fun k => ?_, ‖T‖, ?_⟩
  · simp only [coeff, coeffMul]
    refine congrFun (fourierCoeff_congr_ae ?_) k
    filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht]
    funext i
    simp only [T, E, ContinuousMap.coe_mk, complexify]
    change ((((S t) *ᵥ ((f t : Vec n) : Fin n ⊕ Fin n → ℝ)) i : ℝ) : ℂ) = _
    simp [mulVec, dotProduct, complexify]
  · filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht]; exact hle t

lemma ao8_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao8_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The test function `cos(2πkt) e_{inl j} + sin(2πkt) e_{inr j}` in `L²`. -/
noncomputable def ao8f {n : ℕ} (k : ℤ) (j : Fin n) : L2 n :=
  ContinuousMap.toLp (E := Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ
      (ao8ψ k (Sum.inl j) 1) +
    ContinuousMap.toLp (E := Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ
      (ao8ψ k (Sum.inr j) (-Complex.I))

lemma ao8f_coeff {n : ℕ} (k m : ℤ) (j : Fin n) (i : Fin n ⊕ Fin n) :
    coeff (ao8f k j) m i =
      (if i = Sum.inl j then (1 : ℂ) else 0) *
          (1 / 2 * (Pi.single k (1 : ℂ) : ℤ → ℂ) m + 1 / 2 * (Pi.single (-k) (1 : ℂ) : ℤ → ℂ) m) +
        (if i = Sum.inr j then (1 : ℂ) else 0) *
          (-Complex.I / 2 * (Pi.single k (1 : ℂ) : ℤ → ℂ) m +
            Complex.I / 2 * (Pi.single (-k) (1 : ℂ) : ℤ → ℂ) m) := by
  rw [ao8f, ao8_coeff_add, Pi.add_apply, ao8_coeff_ψ, ao8_coeff_ψ]
  simp [Complex.conj_I]

/-- For `k ≠ 0` the test function is an eigenfunction of `-J₀∂ₜ` with eigenvalue `2πk`. -/
lemma ao8f_symbol {n : ℕ} (k m : ℤ) (hk : k ≠ 0) (j : Fin n) :
    -((2 * Real.pi * m : ℝ) * Complex.I) •
        ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff (ao8f k j) m) =
      ((2 * Real.pi * k : ℝ) : ℂ) • coeff (ao8f k j) m := by
  have hkk : k ≠ -k := by omega
  funext i
  rcases i with a | a
  · rw [Pi.smul_apply, ao8_J_inl, Pi.smul_apply, ao8f_coeff, ao8f_coeff]
    by_cases ha : a = j
    · subst ha
      by_cases h1 : m = k
      · subst h1; simp [Pi.single_apply, hkk]; push_cast; ring_nf; try simp [Complex.I_sq]; try ring
      by_cases h2 : m = -k
      · subst h2; simp [Pi.single_apply, hkk, Ne.symm hkk]; push_cast; ring_nf
        try simp [Complex.I_sq]; try ring
      simp [Pi.single_apply, h1, h2]
    · simp [ha]
  · rw [Pi.smul_apply, ao8_J_inr, Pi.smul_apply, ao8f_coeff, ao8f_coeff]
    by_cases ha : a = j
    · subst ha
      by_cases h1 : m = k
      · subst h1; simp [Pi.single_apply, hkk]; push_cast; ring_nf
      by_cases h2 : m = -k
      · subst h2; simp [Pi.single_apply, hkk, Ne.symm hkk]; push_cast; ring_nf
      simp [Pi.single_apply, h1, h2]
    · simp [ha]

lemma ao8f_ne_zero {n : ℕ} (k : ℤ) (hk : k ≠ 0) (j : Fin n) : ao8f k j ≠ 0 := by
  intro h
  have hkk : k ≠ -k := by omega
  have h0 : coeff (ao8f k j) k (Sum.inl j) = 0 := by
    rw [h]
    have := ao8_coeff_sub (0 : L2 n) 0 k
    rw [sub_zero, sub_self] at this
    rw [this]; rfl
  rw [ao8f_coeff] at h0
  simp [Pi.single_apply, hkk] at h0

lemma ao8f_inW12 {n : ℕ} (k : ℤ) (j : Fin n) : InW12 (ao8f k j) := by
  unfold InW12
  apply summable_of_ne_finset_zero (s := {k, -k})
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  simp [ao8f_coeff, Pi.single_apply, hm.1, hm.2]

/-- The quadratic form of `A_S` on the test function is within `M‖f‖²` of `2πk‖f‖²`. -/
lemma ao8_key {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hn : 0 < n) :
    ∃ M : ℝ, ∀ k : ℤ, k ≠ 0 → ∃ x : (asymptoticOperator S).domain, (x : L2 n) ≠ 0 ∧
      |inner ℝ (asymptoticOperator S x) (x : L2 n) - 2 * Real.pi * k * ‖(x : L2 n)‖ ^ 2| ≤
        M * ‖(x : L2 n)‖ ^ 2 := by
  have hex : ∃ A' : L2 n →ₗ.[ℝ] L2 n, (A'.graph : Set (L2 n × L2 n)) = graphSet S :=
    (graph_existsUnique S).exists
  have hgraph : ((asymptoticOperator S).graph : Set (L2 n × L2 n)) = graphSet S := by
    rw [asymptoticOperator, dif_pos hex]
    exact hex.choose_spec
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
  -- a uniform bound for multiplication by `S` (it does not depend on `f`)
  let E := toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)
  have hE : Continuous fun A : Mat n => E A :=
    LinearMap.continuous_of_finiteDimensional E.toAlgEquiv.toLinearMap
  let T : C(UnitAddCircle, Vec n →L[ℝ] Vec n) := ⟨fun t => E (S t), hE.comp S.continuous⟩
  refine ⟨‖T‖, fun k hk => ?_⟩
  set j : Fin n := ⟨0, hn⟩
  set f := ao8f k j
  -- the product `S f` in `L²`
  have hmeas : AEStronglyMeasurable (fun t => T t (f t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    have hc : Continuous fun p : (Vec n →L[ℝ] Vec n) × Vec n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hc.comp_aestronglyMeasurable
      (T.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f))
  have hle : ∀ t, ‖T t (f t)‖ ≤ ‖T‖ * ‖f t‖ := fun t =>
    ((T t).le_opNorm (f t)).trans
      (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm t) (norm_nonneg _))
  have hmem : MemLp (fun t => T t (f t)) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (Lp.memLp f).of_le_mul hmeas (ae_of_all _ hle)
  set m : L2 n := hmem.toLp _
  have hm : ∀ k : ℤ, coeff m k = coeffMul S f k := by
    intro k
    simp only [coeff, coeffMul]
    refine congrFun (fourierCoeff_congr_ae ?_) k
    filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht]
    funext i
    simp only [T, E, ContinuousMap.coe_mk, complexify]
    change ((((S t) *ᵥ ((f t : Vec n) : Fin n ⊕ Fin n → ℝ)) i : ℝ) : ℂ) = _
    simp [mulVec, dotProduct, complexify]
  have hmn : ‖m‖ ≤ ‖T‖ * ‖f‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht]; exact hle t
  -- the action `A_S f = 2πk f - S f`
  set g : L2 n := (2 * Real.pi * k : ℝ) • f - m
  have hact : IsAsymptoticAction S f g := by
    refine ⟨ao8f_inW12 k j, fun l => ?_⟩
    rw [ao8_coeff_sub, ao8_coeff_smul, hm, ao8f_symbol k l hk j]
  obtain ⟨hf, hAf⟩ := hdom f g hact
  refine ⟨⟨f, hf⟩, ao8f_ne_zero k hk j, ?_⟩
  change |inner ℝ (asymptoticOperator S ⟨f, hf⟩) f - _| ≤ _
  rw [hAf, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h1 : |inner ℝ m f| ≤ ‖T‖ * ‖f‖ ^ 2 := by
    calc |inner ℝ m f| ≤ ‖m‖ * ‖f‖ := abs_real_inner_le_norm m f
      _ ≤ ‖T‖ * ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right hmn (norm_nonneg _)
      _ = ‖T‖ * ‖f‖ ^ 2 := by ring
  calc |2 * Real.pi * k * ‖f‖ ^ 2 - inner ℝ m f - 2 * Real.pi * k * ‖f‖ ^ 2|
      = |inner ℝ m f| := by rw [sub_sub_cancel_left, abs_neg]
    _ ≤ _ := h1

theorem solution {n : ℕ} (hn : 0 < n) (S : C(UnitAddCircle, Mat n))
    (hS : IsSymLoop S) (c : ℝ) :
    (∃ μ : ℝ, c < μ ∧ eigenspace (asymptoticOperator S) μ ≠ ⊥) ∧
      ∃ μ : ℝ, μ < -c ∧ eigenspace (asymptoticOperator S) μ ≠ ⊥ := by
  obtain ⟨ι, b, ev, hb, -⟩ := hasDiscreteEigenbasis S hS
  have hsym := isSymmetric S hS
  obtain ⟨M, hM⟩ := ao8_key S hn
  -- each `evᵢ` is an eigenvalue
  have heig : ∀ i, eigenspace (asymptoticOperator S) (ev i) ≠ ⊥ := by
    intro i
    obtain ⟨h, hi⟩ := hb i
    rw [Submodule.ne_bot_iff]
    refine ⟨⟨b i, h⟩, ?_, ?_⟩
    · change (asymptoticOperator S) ⟨b i, h⟩ - ev i • (b i) = 0
      rw [hi, sub_self]
    · intro h0
      have : (b i : L2 n) = 0 := congrArg Subtype.val h0
      exact b.orthonormal.ne_zero i this
  -- quadratic form and norm in the eigenbasis
  have hq := hasSum_inner_self_of_hilbertBasis_eigenvectors (asymptoticOperator S) hsym b ev hb
  have hnorm : ∀ x : L2 n, HasSum (fun i => inner ℝ x (b i) ^ 2) (‖x‖ ^ 2) := by
    intro x
    have := b.hasSum_inner_mul_inner x x
    rw [real_inner_self_eq_norm_sq] at this
    have hf : (fun i => inner ℝ x (b i) * inner ℝ (b i) x) = fun i => inner ℝ x (b i) ^ 2 := by
      funext i; rw [real_inner_comm (b i) x, sq]
    rwa [hf] at this
  -- choose a large frequency
  obtain ⟨k, hk⟩ : ∃ k : ℕ, M + |c| < 2 * Real.pi * k := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((M + |c|) / (2 * Real.pi))
    exact ⟨k, by rwa [div_lt_iff₀ (by positivity), mul_comm] at hk⟩
  have hk0 : (k : ℤ) ≠ 0 := by
    rintro h
    have : (k : ℝ) = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hk
    have := abs_nonneg c
    obtain ⟨x, hx, hb⟩ := hM 1 one_ne_zero
    have := (abs_nonneg _).trans hb
    have hpos : 0 < ‖(x : L2 n)‖ ^ 2 := by positivity
    nlinarith [abs_nonneg c]
  constructor
  · by_contra hcon
    push_neg at hcon
    have hle : ∀ i, ev i ≤ c := fun i => by
      by_contra h; push_neg at h; exact heig i (hcon _ h)
    obtain ⟨x, hx, hbd⟩ := hM k hk0
    have hpos : 0 < ‖(x : L2 n)‖ ^ 2 := by positivity
    have h1 : inner ℝ (asymptoticOperator S x) (x : L2 n) ≤ c * ‖(x : L2 n)‖ ^ 2 := by
      have := hasSum_le (fun i => mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))
        (hq x) ((hnorm x).mul_left c)
      exact this
    have h2 := (abs_le.1 hbd).1
    push_cast at h2
    nlinarith [le_abs_self c]
  · by_contra hcon
    push_neg at hcon
    have hle : ∀ i, -c ≤ ev i := fun i => by
      by_contra h; push_neg at h; exact heig i (hcon _ h)
    obtain ⟨x, hx, hbd⟩ := hM (-(k : ℤ)) (neg_ne_zero.2 hk0)
    have hpos : 0 < ‖(x : L2 n)‖ ^ 2 := by positivity
    have h1 : -c * ‖(x : L2 n)‖ ^ 2 ≤ inner ℝ (asymptoticOperator S x) (x : L2 n) := by
      exact hasSum_le (fun i => mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))
        ((hnorm x).mul_left (-c)) (hq x)
    have h2 := (abs_le.1 hbd).2
    push_cast at h2
    have h3 : -c * ‖(x : L2 n)‖ ^ 2 ≤ (M - 2 * Real.pi * k) * ‖(x : L2 n)‖ ^ 2 := by nlinarith
    have h4 := le_of_mul_le_mul_right h3 hpos
    linarith [le_abs_self c]
