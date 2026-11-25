-- Prove2me | solution 1 for Arxiv1310_4241.pec_debye_sources_low_frequency
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:29:58.120415+00:00
-- url     : https://prove2.me/submissions/2c3126a4-6f63-4bb3-95ab-dcf730e9277e

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma hasFDerivAt_expMode (α : ℂ) (ξ η : ℝ) (p : Space) :
    HasFDerivAt (fun q : Space => Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)
      (Complex.exp (α * (p 2 : ℂ) + Complex.I * ((ξ : ℂ) * (p 0 : ℂ) + (η : ℂ) * (p 1 : ℂ))) •
        (α • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
          Complex.I • ((ξ : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
            (η : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))))) p := by
  have h0 : HasFDerivAt (fun q : Space => ((q 0 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt
  have h1 : HasFDerivAt (fun q : Space => ((q 1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt
  have h2 : HasFDerivAt (fun q : Space => ((q 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt
  have harg := (h2.const_mul α).add (((h0.const_mul (ξ : ℂ)).add (h1.const_mul (η : ℂ))).const_mul Complex.I)
  have hexp := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp p harg
  have hexp' : HasFDerivAt (fun q : Space => Complex.exp (α * (q 2 : ℂ)) * mode ξ η q) _ p :=
    hexp.congr_of_eventuallyEq (Eventually.of_forall fun q => by
      simp [Function.comp, Complex.exp_add, mode, planeWave])
  refine hexp'.congr_fderiv ?_
  ext v
  simp [smul_eq_mul, mul_comm]

private lemma pd_const_expMode (i : Fin 3) (c α : ℂ) (ξ η : ℝ) (p : Space) :
    pd i (fun q => c * (Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)) p =
      c * (match i with | 0 => Complex.I * ξ | 1 => Complex.I * η | 2 => α) *
        (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p) := by
  have h := (hasFDerivAt_expMode α ξ η p).const_mul c
  have hproj : ∀ (k j : Fin 3),
      EuclideanSpace.proj (𝕜 := ℝ) k (EuclideanSpace.single j (1 : ℝ)) = if k = j then 1 else 0 := by
    intro k j
    change (EuclideanSpace.single j (1 : ℝ)).ofLp k = _
    simp [PiLp.single_apply]
  rw [pd, h.fderiv]
  fin_cases i <;>
    simp [Complex.exp_add, mode, planeWave, hproj] <;> ring

private lemma sommerfeldRoot_zero (ξ η : ℝ) :
    sommerfeldRoot 0 ξ η = (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) := by
  unfold sommerfeldRoot
  have hnn : 0 ≤ ξ ^ 2 + η ^ 2 := by positivity
  have hz : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (0 : ℂ) ^ 2 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hz]
  have hnot : ¬((((ξ ^ 2 + η ^ 2 : ℝ) : ℂ)).im = 0 ∧ (((ξ ^ 2 + η ^ 2 : ℝ) : ℂ)).re < 0) := by
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_lt]
    exact hnn
  rw [if_neg hnot, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hnn]
  norm_cast
  rw [Real.sqrt_eq_rpow]

private lemma tendsto_sommerfeldRoot_zero (ε μ : ℂ) (ξ η : ℝ) (hρ : 0 < ξ ^ 2 + η ^ 2) :
    Tendsto (fun ω : ℝ => sommerfeldRoot (wavenumber ω ε μ) ξ η)
      (𝓝 0) (𝓝 (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) := by
  let f : ℝ → ℂ := fun ω => (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (wavenumber ω ε μ) ^ 2
  have hf_cont : Continuous f := by
    unfold f wavenumber
    fun_prop
  have hf0 : f 0 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by
    simp [f, wavenumber]
  have hre0 : 0 < (f 0).re := by
    rw [hf0, Complex.ofReal_re]
    exact hρ
  have hcpow_cont : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) (f 0) := by
    have hlog : ContinuousAt Complex.log (f 0) := (Complex.hasDerivAt_log (Or.inl hre0)).continuousAt
    have hcont : ContinuousAt (fun z : ℂ => Complex.exp (Complex.log z * (1 / 2 : ℂ))) (f 0) :=
      Complex.continuous_exp.continuousAt.comp (hlog.mul continuousAt_const)
    have hf0_ne : f 0 ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
    have hev0 : ∀ᶠ z in 𝓝 (f 0), z ≠ 0 := continuousAt_id.eventually_ne hf0_ne
    exact hcont.congr (hev0.mono fun z hz => (Complex.cpow_def_of_ne_zero hz _).symm)
  have hcomp : Tendsto (fun ω : ℝ => (f ω) ^ (1 / 2 : ℂ)) (𝓝 0) (𝓝 ((f 0) ^ (1 / 2 : ℂ))) :=
    hcpow_cont.tendsto.comp hf_cont.continuousAt.tendsto
  have hval : (f 0) ^ (1 / 2 : ℂ) = (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) := by
    rw [hf0, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hρ.le]
    norm_cast
    rw [Real.sqrt_eq_rpow]
  rw [hval] at hcomp
  have hev : ∀ᶠ ω in 𝓝 (0 : ℝ), sommerfeldRoot (wavenumber ω ε μ) ξ η = (f ω) ^ (1 / 2 : ℂ) := by
    have hre_ev : ∀ᶠ ω in 𝓝 (0 : ℝ), 0 < (f ω).re :=
      (Complex.continuous_re.comp hf_cont).continuousAt.eventually (Ioi_mem_nhds hre0)
    filter_upwards [hre_ev] with ω hω
    unfold sommerfeldRoot
    have hnot : ¬(((f ω).im = 0) ∧ (f ω).re < 0) := fun h => not_lt_of_gt hω h.2
    exact if_neg hnot
  exact hcomp.congr' (hev.mono fun _ h => h.symm)

theorem solution (ε μ : ℂ)
    (hk : ∀ ω : ℝ, 0 < ω → IsCausalWavenumber (wavenumber ω ε μ)) (ξ η : ℝ)
    (hξη : (ξ, η) ≠ (0, 0)) (a b : ℂ) :
    Tendsto (fun ω : ℝ => -(64 * Real.pi ^ 4 / csqrt μ) * a * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) /
        (sommerfeldRoot (wavenumber ω ε μ) ξ η - Complex.I * wavenumber ω ε μ))
      (𝓝[>] 0) (𝓝 (-(64 * Real.pi ^ 4 / csqrt μ) * a)) ∧
    Tendsto (fun ω : ℝ => -(8 * Real.pi ^ 2 / csqrt ε) * b * sommerfeldRoot (wavenumber ω ε μ) ξ η /
        (sommerfeldRoot (wavenumber ω ε μ) ξ η - Complex.I * wavenumber ω ε μ))
      (𝓝[>] 0) (𝓝 (-(8 * Real.pi ^ 2 / csqrt ε) * b)) ∧
    ∀ r q : ℂ,
      ((∀ x y : ℝ,
        laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE 0 ε μ ξ η r q)) (pt x y 0) +
            a * planeWave ξ η x y = 0 ∧
          pecH 0 ε μ ξ η r q (pt x y 0) 2 + b * planeWave ξ η x y = 0) ↔
      (r = -(64 * Real.pi ^ 4 / csqrt μ) * a ∧ q = -(8 * Real.pi ^ 2 / csqrt ε) * b)) := by
  have hk1 : wavenumber 1 ε μ ≠ 0 := by
    intro h
    have := (hk 1 zero_lt_one).1
    rw [h] at this
    simp at this
  have hμ : μ ≠ 0 := by
    intro h
    apply hk1
    rw [wavenumber, h, mul_zero, Complex.zero_cpow (by norm_num), mul_zero]
  have hε : ε ≠ 0 := by
    intro h
    apply hk1
    rw [wavenumber, h, zero_mul, Complex.zero_cpow (by norm_num), mul_zero]
  have hcμ : csqrt μ ≠ 0 := by
    rw [csqrt]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hμ)
  have hcε : csqrt ε ≠ 0 := by
    rw [csqrt]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hε)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push Not at h
    exact hξη (Prod.ext (by nlinarith [sq_nonneg ξ, sq_nonneg η]) (by nlinarith [sq_nonneg ξ, sq_nonneg η]))
  have hρ_pos : 0 < Real.sqrt (ξ ^ 2 + η ^ 2) := Real.sqrt_pos.mpr hρ2_real
  have hρ : (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  have hβ_lim : Tendsto (fun ω : ℝ => sommerfeldRoot (wavenumber ω ε μ) ξ η)
      (𝓝[>] 0) (𝓝 (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) :=
    (tendsto_sommerfeldRoot_zero ε μ ξ η hρ2_real).mono_left nhdsWithin_le_nhds
  have hk_lim : Tendsto (fun ω : ℝ => wavenumber ω ε μ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ω : ℝ => wavenumber ω ε μ) := by unfold wavenumber; fun_prop
    have h0 : wavenumber 0 ε μ = 0 := by simp [wavenumber]
    rw [← h0]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hden_lim : Tendsto (fun ω : ℝ => sommerfeldRoot (wavenumber ω ε μ) ξ η - Complex.I * wavenumber ω ε μ)
      (𝓝[>] 0) (𝓝 (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) := by
    have := hβ_lim.sub (hk_lim.const_mul Complex.I)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (tendsto_const_nhds (x := -(64 * (Real.pi : ℂ) ^ 4 / csqrt μ) * a * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ))).div hden_lim hρ
    rw [mul_div_cancel_right₀ _ hρ] at h1
    exact h1
  · have h2 := ((tendsto_const_nhds (x := -(8 * (Real.pi : ℂ) ^ 2 / csqrt ε) * b)).mul hβ_lim).div hden_lim hρ
    rw [mul_div_cancel_right₀ _ hρ] at h2
    exact h2
  · intro r q
    have hw0 : wavenumber 0 ε μ = 0 := by simp [wavenumber]
    have hj0 : pecJ 0 ξ η r q = 0 := by ext i; simp [pecJ]
    have hm0 : nCross 0 = 0 := by ext i; fin_cases i <;> simp [nCross]
    have hslp0 : ∀ c : ℂ, slpUp 0 ξ η c =
        fun p => (c * ghat 0 ξ η 0) * (Complex.exp (-(Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) * (p 2 : ℂ)) * mode ξ η p) := by
      intro c; ext p
      simp only [slpUp, ghatUp, ghat, sommerfeldRoot_zero, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      ring
    have hcurl0 : ∀ p : Space, curl (fun p' i => slpUp 0 ξ η 0 p') p = 0 := by
      have hzero : (fun p' (_ : Fin 3) => slpUp 0 ξ η 0 p') = fun _ _ => 0 := by
        ext p' i; simp [slpUp]
      intro p
      rw [hzero]
      ext i
      fin_cases i <;> simp [curl, pd]
    have hpecE0 : pecE 0 ε μ ξ η r q =
        fun p =>
          ![-(csqrt μ * (r * ghat 0 ξ η 0) * (Complex.I * ξ)) *
              (Complex.exp (-(Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) * (p 2 : ℂ)) * mode ξ η p),
            -(csqrt μ * (r * ghat 0 ξ η 0) * (Complex.I * η)) *
              (Complex.exp (-(Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) * (p 2 : ℂ)) * mode ξ η p),
            -(csqrt μ * (r * ghat 0 ξ η 0) * -(Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) *
              (Complex.exp (-(Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) * (p 2 : ℂ)) * mode ξ η p)] := by
      ext p i
      simp only [pecE, debyeE, hw0, hj0, hm0, Pi.zero_apply, hcurl0, grad, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, mul_zero, zero_mul, zero_sub, sub_zero]
      rw [hslp0 r]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [pd_const_expMode 0]; ring
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [pd_const_expMode 1]; ring
      · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [pd_const_expMode 2]; ring
    have hpecH0_2 : ∀ x y : ℝ, pecH 0 ε μ ξ η r q (pt x y 0) 2 =
        csqrt ε / (8 * (Real.pi : ℂ) ^ 2) * q * planeWave ξ η x y := by
      intro x y
      simp only [pecH, debyeH, hw0, hj0, hm0, Pi.zero_apply, hcurl0, grad, Pi.smul_apply, Pi.add_apply,
        Pi.sub_apply, smul_eq_mul, mul_zero, zero_mul, zero_sub, add_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [hslp0 q, pd_const_expMode 2]
      have hpt : mode ξ η (pt x y 0) = planeWave ξ η x y := by simp [mode, pt]
      have hpt2 : (pt x y 0) 2 = 0 := by simp [pt]
      have hghat0 : ghat 0 ξ η 0 = 1 / (8 * (Real.pi : ℂ) ^ 2 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) := by
        simp [ghat, sommerfeldRoot_zero]
      rw [hpt, hpt2, hghat0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      field_simp [hπ, hρ]
    have hpecE0_op : ∀ x y : ℝ,
        laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE 0 ε μ ξ η r q)) (pt x y 0) =
          csqrt μ / (64 * (Real.pi : ℂ) ^ 4) * r * planeWave ξ η x y := by
      intro x y
      simp only [laplaceSingleLayerOnMode, tangentialDivergence, hpecE0,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [pd_const_expMode 0, pd_const_expMode 1]
      have hpt : mode ξ η (pt x y 0) = planeWave ξ η x y := by simp [mode, pt]
      have hpt2 : (pt x y 0) 2 = 0 := by simp [pt]
      have hghat0 : ghat 0 ξ η 0 = 1 / (8 * (Real.pi : ℂ) ^ 2 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) := by
        simp [ghat, sommerfeldRoot_zero]
      have hsq : ((Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) ^ 2 = (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 := by
        norm_cast
        exact Real.sq_sqrt hρ2_real.le
      rw [hpt, hpt2, hghat0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      field_simp [hπ, hρ]
      ring_nf
      simp only [Complex.I_sq, hsq]
      ring
    constructor
    · intro hall
      have h00 := hall 0 0
      have hpw : planeWave ξ η 0 0 = 1 := by simp [planeWave]
      rw [hpecE0_op 0 0, hpecH0_2 0 0, hpw] at h00
      simp only [mul_one] at h00
      rcases h00 with ⟨hr, hq⟩
      constructor
      · field_simp [hcμ, hπ] at hr ⊢; linear_combination hr
      · field_simp [hcε, hπ] at hq ⊢; linear_combination hq
    · rintro ⟨rfl, rfl⟩ x y
      rw [hpecE0_op x y, hpecH0_2 x y]
      constructor
      · field_simp [hcμ, hπ]; ring
      · field_simp [hcε, hπ]; ring
