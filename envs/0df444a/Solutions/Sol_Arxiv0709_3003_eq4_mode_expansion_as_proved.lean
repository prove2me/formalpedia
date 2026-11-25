-- Prove2me | solution 1 for Arxiv0709_3003.eq4_mode_expansion_as_proved
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T18:34:16.599178+00:00
-- url     : https://prove2.me/submissions/721d60b1-f29e-43f0-8837-48081162ad9a

import Definitions.Def_Arxiv0709_3003_Basic

open MeasureTheory ProbabilityTheory Filter Topology Arxiv0709_3003
open scoped RealInnerProductSpace NNReal

private lemma modeCov_posSemidef (s ρ : ℝ) (hs : 0 < s) (hρ : |ρ| ≤ s) :
    (modeCov s ρ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [modeCov]
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, modeCov]
    have h1 : -s ≤ ρ := (abs_le.mp hρ).1
    have h2 : ρ ≤ s := (abs_le.mp hρ).2
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1), sq_nonneg (x 2)]

private noncomputable def modeLinMap (s ρ : ℝ) (z : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.sqrt s * z 0,
    (ρ / Real.sqrt s) * z 0 + Real.sqrt (s - ρ ^ 2 / s) * z 1,
    Real.sqrt s * z 2]

private lemma measurable_modeLinMap (s ρ : ℝ) : Measurable (modeLinMap s ρ) := by
  unfold modeLinMap
  refine (WithLp.measurable_toLp 2 _).comp ?_
  rw [measurable_pi_iff]
  intro i
  fin_cases i <;> simp <;> fun_prop

private lemma modeLaw_eq_map_pi (s ρ : ℝ) (hs : 0 < s) (hρ : |ρ| ≤ s) :
    modeLaw s ρ = (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map (modeLinMap s ρ) := by
  set a : ℝ := Real.sqrt s
  set b : ℝ := ρ / Real.sqrt s
  set c : ℝ := Real.sqrt (s - ρ ^ 2 / s)
  have ha2 : a ^ 2 = s := Real.sq_sqrt hs.le
  have hab : a * b = ρ := mul_div_cancel₀ ρ (Real.sqrt_ne_zero'.mpr hs)
  have hρ2 : ρ ^ 2 ≤ s ^ 2 := by
    have h1 := abs_le.mp hρ
    nlinarith
  have hsc : 0 ≤ s - ρ ^ 2 / s := by
    rw [sub_nonneg, div_le_iff₀ hs]
    linarith
  have hbc : b ^ 2 + c ^ 2 = s := by
    dsimp [b, c]
    rw [div_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hsc]
    ring
  unfold modeLaw
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_multivariateGaussian (modeCov_posSemidef s ρ hs hρ)]
  rw [charFun_apply, integral_map (measurable_modeLinMap s ρ).aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]
  let g : Fin 3 → ℝ → ℂ :=
    ![fun x => Complex.exp (↑((a * t 0 + b * t 1) * x) * Complex.I),
      fun x => Complex.exp (↑((c * t 1) * x) * Complex.I),
      fun x => Complex.exp (↑((a * t 2) * x) * Complex.I)]
  have hfun : (fun z : Fin 3 → ℝ => Complex.exp (↑⟪modeLinMap s ρ z, t⟫ * Complex.I)) =
      fun z => ∏ i : Fin 3, g i (z i) := by
    ext z
    simp only [Fin.prod_univ_three, g, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp [PiLp.inner_apply, Fin.sum_univ_three, modeLinMap, a, b, c]
    push_cast
    ring
  rw [hfun, integral_fintype_prod_eq_prod]
  have hcf : ∀ α : ℝ,
      ∫ x : ℝ, Complex.exp (↑(α * x) * Complex.I) ∂gaussianReal 0 1 =
        Complex.exp (-↑(α ^ 2) / 2) := by
    intro α
    simp_rw [Complex.ofReal_mul]
    rw [← charFun_apply_real, charFun_gaussianReal]
    simp [neg_div]
  simp only [Fin.prod_univ_three, g, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hcf]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, modeCov]
  have halg : (a * t 0 + b * t 1) ^ 2 + (c * t 1) ^ 2 + (a * t 2) ^ 2 =
      t 0 * (s * t 0 + ρ * t 1) + t 1 * (ρ * t 0 + s * t 1) + t 2 * (s * t 2) := by
    calc (a * t 0 + b * t 1) ^ 2 + (c * t 1) ^ 2 + (a * t 2) ^ 2
        = a ^ 2 * t 0 ^ 2 + 2 * (a * b) * t 0 * t 1 + (b ^ 2 + c ^ 2) * t 1 ^ 2 +
            a ^ 2 * t 2 ^ 2 := by ring
      _ = s * t 0 ^ 2 + 2 * ρ * t 0 * t 1 + s * t 1 ^ 2 + s * t 2 ^ 2 := by
          rw [ha2, hab, hbc]
      _ = t 0 * (s * t 0 + ρ * t 1) + t 1 * (ρ * t 0 + s * t 1) + t 2 * (s * t 2) := by ring
  have halgC : ((a * t 0 + b * t 1) ^ 2 + (c * t 1) ^ 2 + (a * t 2) ^ 2 : ℂ) =
      (t 0 * (s * t 0 + ρ * t 1) + t 1 * (ρ * t 0 + s * t 1) + t 2 * (s * t 2) : ℂ) := by
    exact_mod_cast halg
  push_cast at halgC ⊢
  linear_combination halgC / 2

private lemma integrable_pow_std (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  induction k with
  | zero => simp
  | succ m _ =>
    have hlp : MemLp (id : ℝ → ℝ) ((m + 1 : ℕ) : ℝ≥0) (gaussianReal 0 1) :=
      memLp_id_gaussianReal (m + 1 : ℕ)
    have hnorm : Integrable (fun x : ℝ => ‖x‖ ^ (m + 1)) (gaussianReal 0 1) :=
      hlp.integrable_norm_pow (Nat.succ_ne_zero m)
    refine hnorm.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_pow]

private lemma integral_pow_one_std : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 :=
  integral_id_gaussianReal

private lemma integral_pow_two_std : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa using hv

private lemma integral_pow_three_std : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  have h1 : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = ∫ x : ℝ, (-x) ^ 3 ∂gaussianReal 0 1 := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∫ x : ℝ, (-x) ^ 3 ∂gaussianReal 0 1 = -(∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) := by
    have : (fun x : ℝ => (-x) ^ 3) = fun x : ℝ => -(x ^ 3) := by ext x; ring
    rw [this, integral_neg]
  linarith

private lemma integral_pow_four_std : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have h0 : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 =
      iteratedDeriv 4 (mgf (fun x => x) (gaussianReal 0 1)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  rw [h0, mgf_fun_id_gaussianReal]
  have hmgf : (fun t : ℝ => Real.exp (0 * t + ↑(1 : NNReal) * t ^ 2 / 2)) =
      fun t : ℝ => Real.exp (t ^ 2 / 2) := by
    ext t; simp
  rw [hmgf]
  have hexp : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    intro t
    have h := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert h using 1
    ring
  have hd1 : deriv (fun u : ℝ => Real.exp (u ^ 2 / 2)) =
      fun u : ℝ => u * Real.exp (u ^ 2 / 2) := by
    ext u; exact (hexp u).deriv
  have hd2 : deriv (fun u : ℝ => u * Real.exp (u ^ 2 / 2)) =
      fun u : ℝ => (1 + u ^ 2) * Real.exp (u ^ 2 / 2) := by
    ext u
    have h : HasDerivAt (fun u : ℝ => u * Real.exp (u ^ 2 / 2))
        (1 * Real.exp (u ^ 2 / 2) + u * (u * Real.exp (u ^ 2 / 2))) u :=
      (hasDerivAt_id u).mul (hexp u)
    rw [h.deriv]
    ring
  have hd3 : deriv (fun u : ℝ => (1 + u ^ 2) * Real.exp (u ^ 2 / 2)) =
      fun u : ℝ => (3 * u + u ^ 3) * Real.exp (u ^ 2 / 2) := by
    ext u
    have h : HasDerivAt (fun u : ℝ => (1 + u ^ 2) * Real.exp (u ^ 2 / 2))
        ((0 + (2 : ℝ) * u ^ (2 - 1)) * Real.exp (u ^ 2 / 2) +
          (1 + u ^ 2) * (u * Real.exp (u ^ 2 / 2))) u :=
      ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_pow 2 u)).mul (hexp u)
    rw [h.deriv]
    ring
  have hd4 : deriv (fun u : ℝ => (3 * u + u ^ 3) * Real.exp (u ^ 2 / 2)) =
      fun u : ℝ => (3 + 6 * u ^ 2 + u ^ 4) * Real.exp (u ^ 2 / 2) := by
    ext u
    have h : HasDerivAt (fun u : ℝ => (3 * u + u ^ 3) * Real.exp (u ^ 2 / 2))
        ((3 * 1 + (3 : ℝ) * u ^ (3 - 1)) * Real.exp (u ^ 2 / 2) +
          (3 * u + u ^ 3) * (u * Real.exp (u ^ 2 / 2))) u :=
      (((hasDerivAt_id u).const_mul 3).add (hasDerivAt_pow 3 u)).mul (hexp u)
    rw [h.deriv]
    ring
  rw [iteratedDeriv_succ', hd1, iteratedDeriv_succ', hd2,
    iteratedDeriv_succ', hd3, iteratedDeriv_one, hd4]
  norm_num

private lemma integrable_triple_prod (k0 k1 k2 : ℕ) :
    Integrable (fun z : Fin 3 → ℝ => z 0 ^ k0 * z 1 ^ k1 * z 2 ^ k2)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) := by
  let f : Fin 3 → ℝ → ℝ := ![fun x => x ^ k0, fun x => x ^ k1, fun x => x ^ k2]
  have hfun : (fun z : Fin 3 → ℝ => z 0 ^ k0 * z 1 ^ k1 * z 2 ^ k2) =
      fun z => ∏ i : Fin 3, f i (z i) := by
    ext z
    simp [Fin.prod_univ_three, f, mul_assoc]
  rw [hfun]
  refine Integrable.fintype_prod (f := f) fun i => ?_
  fin_cases i <;> exact integrable_pow_std _

private lemma integral_triple_prod (k0 k1 k2 : ℕ) :
    ∫ z : Fin 3 → ℝ, z 0 ^ k0 * z 1 ^ k1 * z 2 ^ k2
      ∂(Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) =
      (∫ x : ℝ, x ^ k0 ∂gaussianReal 0 1) *
      (∫ x : ℝ, x ^ k1 ∂gaussianReal 0 1) *
      (∫ x : ℝ, x ^ k2 ∂gaussianReal 0 1) := by
  let f : Fin 3 → ℝ → ℝ := ![fun x => x ^ k0, fun x => x ^ k1, fun x => x ^ k2]
  have hfun : (fun z : Fin 3 → ℝ => z 0 ^ k0 * z 1 ^ k1 * z 2 ^ k2) =
      fun z => ∏ i : Fin 3, f i (z i) := by
    ext z
    simp [Fin.prod_univ_three, f, mul_assoc]
  rw [hfun, integral_fintype_prod_eq_prod]
  simp [Fin.prod_univ_three, f, mul_assoc]

private lemma integrable_and_modeTerm (s ρ : ℝ) (hs : 0 < s) (hρ : |ρ| ≤ s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 4)
      (modeLaw s ρ) ∧
    ∫ x : EuclideanSpace ℝ (Fin 3), x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 4 ∂(modeLaw s ρ) =
      3 * s ^ 2 * (s ^ 2 + 2 * ρ ^ 2) := by
  set a : ℝ := Real.sqrt s
  set b : ℝ := ρ / Real.sqrt s
  set c : ℝ := Real.sqrt (s - ρ ^ 2 / s)
  have ha2 : a ^ 2 = s := Real.sq_sqrt hs.le
  have hρ2 : ρ ^ 2 ≤ s ^ 2 := by
    have h1 := abs_le.mp hρ
    nlinarith
  have hsc : 0 ≤ s - ρ ^ 2 / s := by
    rw [sub_nonneg, div_le_iff₀ hs]
    linarith
  have hb2 : b ^ 2 = ρ ^ 2 / s := by
    dsimp [b]; rw [div_pow, Real.sq_sqrt hs.le]
  have hc2 : c ^ 2 = s - ρ ^ 2 / s := Real.sq_sqrt hsc
  set μ : Measure (Fin 3 → ℝ) := Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)
  have hlaw : modeLaw s ρ = μ.map (modeLinMap s ρ) := modeLaw_eq_map_pi s ρ hs hρ
  have hcomp : (fun z : Fin 3 → ℝ =>
      (modeLinMap s ρ z) 0 ^ 2 * (modeLinMap s ρ z) 1 ^ 2 * (modeLinMap s ρ z) 2 ^ 4) =
      fun z => (a ^ 6 * b ^ 2) * (z 0 ^ 4 * z 1 ^ 0 * z 2 ^ 4) +
        (2 * a ^ 6 * b * c) * (z 0 ^ 3 * z 1 ^ 1 * z 2 ^ 4) +
        (a ^ 6 * c ^ 2) * (z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 4) := by
    ext z
    simp [modeLinMap, a, b, c]
    ring
  have hint1 : Integrable (fun z : Fin 3 → ℝ =>
      (a ^ 6 * b ^ 2) * (z 0 ^ 4 * z 1 ^ 0 * z 2 ^ 4)) μ :=
    (integrable_triple_prod 4 0 4).const_mul _
  have hint2 : Integrable (fun z : Fin 3 → ℝ =>
      (2 * a ^ 6 * b * c) * (z 0 ^ 3 * z 1 ^ 1 * z 2 ^ 4)) μ :=
    (integrable_triple_prod 3 1 4).const_mul _
  have hint3 : Integrable (fun z : Fin 3 → ℝ =>
      (a ^ 6 * c ^ 2) * (z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 4)) μ :=
    (integrable_triple_prod 2 2 4).const_mul _
  have hint12 : Integrable (fun z : Fin 3 → ℝ =>
      (a ^ 6 * b ^ 2) * (z 0 ^ 4 * z 1 ^ 0 * z 2 ^ 4) +
        (2 * a ^ 6 * b * c) * (z 0 ^ 3 * z 1 ^ 1 * z 2 ^ 4)) μ :=
    hint1.add hint2
  have hint_comp : Integrable (fun z : Fin 3 → ℝ =>
      (modeLinMap s ρ z) 0 ^ 2 * (modeLinMap s ρ z) 1 ^ 2 * (modeLinMap s ρ z) 2 ^ 4) μ := by
    rw [hcomp]
    exact hint12.add hint3
  constructor
  · rw [hlaw]
    exact (integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop))
      (measurable_modeLinMap s ρ).aemeasurable).mpr hint_comp
  · rw [hlaw, integral_map (measurable_modeLinMap s ρ).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    rw [hcomp, integral_add hint12 hint3, integral_add hint1 hint2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_triple_prod, integral_triple_prod, integral_triple_prod]
    simp only [pow_zero, pow_one, integral_const, probReal_univ, one_smul,
      integral_pow_one_std, integral_pow_two_std, integral_pow_three_std, integral_pow_four_std]
    have ha6 : a ^ 6 = s ^ 3 := by
      calc a ^ 6 = (a ^ 2) ^ 3 := by ring
        _ = s ^ 3 := by rw [ha2]
    have hcalc : a ^ 6 * b ^ 2 * (3 * 1 * 3) + 2 * a ^ 6 * b * c * (0 * 0 * 3) +
        a ^ 6 * c ^ 2 * (1 * 1 * 3) = 3 * s ^ 2 * (s ^ 2 + 2 * ρ ^ 2) := by
      rw [ha6, hb2, hc2]
      field_simp [hs.ne']
      ring
    linarith

theorem solution {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (N : ℕ) (s ρ : ℝ) (hs : 0 < s) (hρ : |ρ| ≤ s)
    (u : Fin N → Omega → EuclideanSpace ℝ (Fin 3)) (hu : ∀ n, HasLaw (u n) (modeLaw s ρ) P)
    (hunc : ∀ n m : Fin N, n ≠ m → ∀ a b : Fin 3, ∫ ω, u n ω a * u m ω b ∂P = 0) :
    ∫ ω, (∑ n, u n ω 0 ^ 2 * u n ω 1 ^ 2 * u n ω 2 ^ 4) ∂P =
      N * (3 * s ^ 2 * (s ^ 2 + 2 * ρ ^ 2)) := by
  have _ := hunc
  have ⟨hint_law, hval⟩ := integrable_and_modeTerm s ρ hs hρ
  let F : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 4
  have hF_meas : AEStronglyMeasurable F (modeLaw s ρ) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hint_u : ∀ n : Fin N, Integrable (fun ω => F (u n ω)) P := by
    intro n
    have h1 : Integrable F (P.map (u n)) := by rwa [(hu n).map_eq]
    have h2 : AEStronglyMeasurable F (P.map (u n)) := by rwa [(hu n).map_eq]
    exact (integrable_map_measure h2 (hu n).aemeasurable).mp h1
  rw [integral_finsetSum Finset.univ (fun n _ => hint_u n)]
  have hterm : ∀ n : Fin N,
      ∫ ω, F (u n ω) ∂P = 3 * s ^ 2 * (s ^ 2 + 2 * ρ ^ 2) := by
    intro n
    change ∫ ω, (F ∘ u n) ω ∂P = _
    rw [(hu n).integral_comp hF_meas]
    exact hval
  simp [hterm]
