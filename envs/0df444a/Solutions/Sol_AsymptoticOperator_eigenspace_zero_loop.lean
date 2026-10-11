-- Prove2me | solution 1 for AsymptoticOperator.eigenspace_zero_loop
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:54:01.200986+00:00
-- url     : https://prove2.me/submissions/f1544ab8-cbc0-4ab5-89bc-809221919dc3

import Theorems.Thm_AsymptoticOperator_graph_existsUnique
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq
import Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
import Theorems.Thm_AsymptoticOperator_coeff_neg
import Theorems.Thm_AsymptoticOperator_symbol_eigen
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

/-! Coefficient algebra on `L²`. -/

lemma ao9_cx_int {n : ℕ} (f : L2 n) :
    Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i) :
    Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp ((Lp.memLp f).integrable one_le_two)

lemma ao9_coeff_add {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f + g : L2 n) : UnitAddCircle → Vec n) k = coeff f k + coeff g k := by
  have h : (fun t => complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => complexify (f t)) + (fun t => complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    rw [ht]; funext i; simp [complexify]
  simp only [coeff]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (ao9_cx_int f) (ao9_cx_int g)]
  rfl

lemma ao9_coeff_smul {n : ℕ} (c : ℝ) (f : L2 n) (k : ℤ) :
    coeff ((c • f : L2 n) : UnitAddCircle → Vec n) k = (c : ℂ) • coeff f k := by
  have h : (fun t => complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    rw [ht]; funext i; simp [complexify]
  simp only [coeff]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma ao9_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k :=
  eval_integral (integrable_pi_iff.1 ((ao9_cx_int f).fourier_smul (-k))) i

lemma ao9_coeffMul_zero {n : ℕ} (f : L2 n) (k : ℤ) :
    coeffMul (0 : C(UnitAddCircle, Mat n)) f k = 0 := by
  have h : (fun t => ((0 : C(UnitAddCircle, Mat n)) t).map (fun x : ℝ => (x : ℂ)) *ᵥ
      complexify (f t)) = fun _ => 0 := by
    funext t
    simp [Matrix.map_zero]
  simp only [coeffMul]
  rw [h]
  simp [fourierCoeff]

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

theorem solution (n : ℕ) (μ : ℝ) :
    ((∃ k : ℤ, μ = 2 * Real.pi * k) →
        Nonempty (eigenspace (asymptoticOperator (0 : C(UnitAddCircle, Mat n))) μ ≃ₗ[ℝ]
          (Fin n ⊕ Fin n → ℝ))) ∧
      ((∀ k : ℤ, μ ≠ 2 * Real.pi * k) →
        eigenspace (asymptoticOperator (0 : C(UnitAddCircle, Mat n))) μ = ⊥) := by
  set S : C(UnitAddCircle, Mat n) := 0 with hS0
  set A := asymptoticOperator S
  -- the graph of `A` is `graphSet S`
  have hex : ∃ A' : L2 n →ₗ.[ℝ] L2 n, (A'.graph : Set (L2 n × L2 n)) = graphSet S :=
    (graph_existsUnique S).exists
  have hgraph : (A.graph : Set (L2 n × L2 n)) = graphSet S := by
    simp only [A]
    rw [asymptoticOperator, dif_pos hex]
    exact hex.choose_spec
  have hact : ∀ x : A.domain, IsAsymptoticAction S x (A x) := by
    intro x
    have : ((x : L2 n), A x) ∈ (A.graph : Set (L2 n × L2 n)) := A.mem_graph x
    rw [hgraph] at this
    exact this
  have hdom : ∀ f g : L2 n, IsAsymptoticAction S f g →
      ∃ h : f ∈ A.domain, A ⟨f, h⟩ = g := by
    intro f g hfg
    have : (f, g) ∈ (A.graph : Set (L2 n × L2 n)) := by
      rw [hgraph]; exact hfg
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 this
    have hy1' : (y : L2 n) = f := hy1
    refine ⟨hy1' ▸ y.2, ?_⟩
    have hy2' : A y = g := hy2
    rw [← hy2']
    congr 1
    exact Subtype.ext hy1'.symm
  have hmem : ∀ x : A.domain, x ∈ eigenspace A μ ↔ A x = μ • (x : L2 n) := by
    intro x
    simp only [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply]
    change A x - μ • (x : L2 n) = 0 ↔ _
    exact sub_eq_zero
  -- coefficients of eigenvectors satisfy the symbol equation
  have heq : ∀ x : eigenspace A μ, ∀ m : ℤ,
      (μ : ℂ) • coeff (((x : A.domain) : L2 n)) m = -((2 * Real.pi * m : ℝ) * Complex.I) •
        ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff (((x : A.domain) : L2 n)) m) := by
    intro x m
    obtain ⟨-, hk⟩ := hact x
    have hx := (hmem x).1 x.2
    rw [← ao9_coeff_smul, ← hx, hk m, ao9_coeffMul_zero, sub_zero]
  have hzero : ∀ x : eigenspace A μ,
      (∀ m : ℤ, coeff (((x : A.domain) : L2 n)) m = 0) → x = 0 := by
    intro x h
    have := eq_zero_of_coeff_eq_zero _ h
    exact Subtype.ext (Subtype.ext this)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨k, rfl⟩
    -- coefficients vanish away from `±k`
    have hvan : ∀ x : eigenspace A (2 * Real.pi * k), ∀ m : ℤ, m ≠ k → m ≠ -k →
        coeff (((x : A.domain) : L2 n)) m = 0 := by
      intro x m h1 h2
      funext i
      have hs := symbol_eigen _ m _ (heq x m) i
      have hf1 : ((2 * Real.pi * k : ℝ) : ℂ) - ((2 * Real.pi * m : ℝ) : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
        intro h0
        have : (2 * Real.pi) * ((k : ℝ) - m) = 0 := by linear_combination h0
        rcases mul_eq_zero.1 this with h | h
        · exact hpi h
        · exact h1 (by exact_mod_cast (sub_eq_zero.1 h).symm)
      have hf2 : ((2 * Real.pi * k : ℝ) : ℂ) + ((2 * Real.pi * m : ℝ) : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
        intro h0
        have : (2 * Real.pi) * ((k : ℝ) + m) = 0 := by linear_combination h0
        rcases mul_eq_zero.1 this with h | h
        · exact hpi h
        · exact h2 (by have : (m : ℝ) = -k := by linarith
                       exact_mod_cast this)
      rcases mul_eq_zero.1 hs with h | h
      · exact absurd h (mul_ne_zero hf1 hf2)
      · exact h
    -- the readout `x ↦ Re x̂ₖ`
    let Φ : eigenspace A (2 * Real.pi * k) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
      { toFun := fun x i => (coeff (((x : A.domain) : L2 n)) k i).re
        map_add' := by
          intro x y
          funext i
          simp only [Submodule.coe_add, ao9_coeff_add, Pi.add_apply, Complex.add_re]
        map_smul' := by
          intro c x
          funext i
          simp only [Submodule.coe_smul, ao9_coeff_smul, Pi.smul_apply, smul_eq_mul,
            Complex.re_ofReal_mul, RingHom.id_apply] }
    refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩⟩
    · -- injectivity
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have hre : ∀ i, (coeff (((x : A.domain) : L2 n)) k i).re = 0 := fun i => congrFun hx i
      obtain ⟨c, hc⟩ : ∃ c, coeff (((x : A.domain) : L2 n)) k = c := ⟨_, rfl⟩
      have hek := heq x k
      rw [hc] at hek
      simp only [hc] at hre
      have hck : c = 0 := by
        funext i
        by_cases hk : k = 0
        · have hconj := coeff_neg ((x : A.domain) : L2 n) k i
          have hkk : -k = k := by omega
          rw [hkk, hc] at hconj
          apply Complex.ext
          · simpa using hre i
          · have := congrArg Complex.im hconj
            simp only [Complex.conj_im] at this
            simp only [Pi.zero_apply, Complex.zero_im]; linarith
        · have hkc : ((2 * Real.pi * k : ℝ) : ℂ) ≠ 0 := by
            rw [Complex.ofReal_ne_zero]
            exact mul_ne_zero hpi (by exact_mod_cast hk)
          have hrel : ∀ a, c (Sum.inl a) = Complex.I * c (Sum.inr a) := by
            intro a
            have := (ao9_comp _ k c hek a).1
            apply mul_left_cancel₀ hkc
            linear_combination this
          have hr0 : ∀ a, c (Sum.inr a) = 0 := by
            intro a
            have h1 := hre (Sum.inl a)
            have h2 := hre (Sum.inr a)
            rw [hrel a] at h1
            simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
              zero_sub, neg_eq_zero] at h1
            exact Complex.ext h2 h1
          rcases i with a | a
          · simp only [Pi.zero_apply]; rw [hrel a, hr0 a, mul_zero]
          · simp only [Pi.zero_apply]; exact hr0 a
      apply hzero
      intro m
      by_cases h1 : m = k
      · rw [h1, hc]; exact hck
      by_cases h2 : m = -k
      · funext i
        rw [h2, coeff_neg, hc, hck]
        simp
      exact hvan x m h1 h2
    · -- surjectivity
      intro v
      let w : Fin n ⊕ Fin n → ℂ := if k = 0 then fun i => ((v i : ℝ) : ℂ) else
        Sum.elim (fun a => (v (Sum.inl a) : ℂ) + Complex.I * v (Sum.inr a))
          (fun a => (v (Sum.inr a) : ℂ) - Complex.I * v (Sum.inl a))
      let c : ℤ → Fin n ⊕ Fin n → ℂ := fun m =>
        if m = k then w else if m = -k then fun i => conj (w i) else 0
      have hwre : ∀ i, (w i).re = v i := by
        intro i
        by_cases hk : k = 0
        · simp [w, hk]
        · rcases i with a | a <;> simp [w, hk]
      have hw0 : k = 0 → ∀ i, conj (w i) = w i := by
        intro hk i
        simp [w, hk]
      have hwl : k ≠ 0 → ∀ a,
          w (Sum.inl a) = (v (Sum.inl a) : ℂ) + Complex.I * v (Sum.inr a) := fun hk a => by
        simp [w, hk]
      have hwr : k ≠ 0 → ∀ a,
          w (Sum.inr a) = (v (Sum.inr a) : ℂ) - Complex.I * v (Sum.inl a) := fun hk a => by
        simp [w, hk]
      have hcsupp : ∀ m ∉ ({k, -k} : Finset ℤ), c m = 0 := by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
        simp [c, hm.1, hm.2]
      have hcconj : ∀ m i, c (-m) i = conj (c m i) := by
        intro m i
        by_cases h1 : m = k
        · rw [h1]
          by_cases hk : k = 0
          · simp [c, hk, hw0 hk]
          · have : -k ≠ k := by omega
            simp [c, this]
        by_cases h2 : m = -k
        · rw [h2]
          have : -k ≠ k := by omega
          simp [c, this]
        · have h3 : -m ≠ k := by omega
          have h4 : -m ≠ -k := by omega
          simp [c, h1, h2, h3, h4]
      obtain ⟨f, hf⟩ := exists_coeff_eq c
        (summable_of_ne_finset_zero (s := {k, -k}) fun m hm => by simp [hcsupp m hm]) hcconj
      have hsym : ∀ m : ℤ, ((2 * Real.pi * k : ℝ) : ℂ) • c m =
          -((2 * Real.pi * m : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ c m) := by
        intro m
        by_cases hk : k = 0
        · subst hk
          by_cases h1 : m = 0
          · subst h1; simp
          · simp [c, h1]
        by_cases h1 : m = k
        · subst h1
          funext i
          rcases i with a | a <;>
            simp only [c, if_pos rfl, Pi.smul_apply, smul_eq_mul, ao9_J_inl, ao9_J_inr,
              hwl hk, hwr hk] <;>
            push_cast <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)
        by_cases h2 : m = -k
        · subst h2
          funext i
          rcases i with a | a <;>
            simp only [c, if_neg h1, if_pos rfl, ↓reduceIte, Pi.smul_apply, smul_eq_mul, ao9_J_inl, ao9_J_inr,
              hwl hk, hwr hk, map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I] <;>

            push_cast <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)
        · simp [c, h1, h2]
      have hW : InW12 f := by
        unfold InW12
        apply summable_of_ne_finset_zero (s := {k, -k})
        intro m hm
        simp [hf, hcsupp m hm]
      have hacts : IsAsymptoticAction S f ((2 * Real.pi * k : ℝ) • f) := by
        refine ⟨hW, fun m => ?_⟩
        rw [ao9_coeff_smul, hf, ao9_coeffMul_zero, sub_zero]
        exact hsym m
      obtain ⟨hd, hAf⟩ := hdom f _ hacts
      refine ⟨⟨⟨f, hd⟩, (hmem _).2 hAf⟩, ?_⟩
      funext i
      change (coeff f k i).re = v i
      rw [hf]
      simp only [c, if_pos rfl]
      exact hwre i
  · intro hμ
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 := hzero ⟨x, hx⟩ ?_
    · exact congrArg Subtype.val hx0
    intro m
    funext i
    have hs := symbol_eigen μ m _ (heq ⟨x, hx⟩ m) i
    have hf1 : (μ : ℂ) - ((2 * Real.pi * m : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero, sub_ne_zero]
      exact hμ m
    have hf2 : (μ : ℂ) + ((2 * Real.pi * m : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
      intro h0
      apply hμ (-m)
      push_cast
      linarith
    rcases mul_eq_zero.1 hs with h | h
    · exact absurd h (mul_ne_zero hf1 hf2)
    · exact h
