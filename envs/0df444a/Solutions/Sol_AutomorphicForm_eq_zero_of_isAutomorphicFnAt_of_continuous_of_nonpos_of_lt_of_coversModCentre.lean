-- Prove2me | solution 1 for AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/abc1f8a7-02fa-5fa2-b325-1a2a1f27fb4f

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent
open NumberField.AdelicVolume
open scoped ENNReal

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

private theorem lintegral_eq_top_of_disjoint_translates (μ : Measure G) [μ.IsMulLeftInvariant]
    (f : G → ℝ≥0∞) (γ : ℕ → G) (hf : ∀ k x, f (γ k * x) = f x)
    (O : Set G) (hO : MeasurableSet O) (hpos : ∫⁻ x in O, f x ∂μ ≠ 0)
    (W : Set G) (hsub : ∀ k, (fun x => γ k * x) '' O ⊆ W)
    (hdisj : Pairwise (Function.onFun Disjoint fun k => (fun x => γ k * x) '' O)) :
    ∫⁻ x in W, f x ∂μ = ⊤ := by
  have himg : ∀ k, (fun x => γ k * x) '' O = (fun x => (γ k)⁻¹ * x) ⁻¹' O := by
    intro k
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨(γ k)⁻¹ * x, hx, by simp⟩
  have hmeas : ∀ k, MeasurableSet ((fun x => γ k * x) '' O) := by
    intro k
    rw [himg]
    exact measurable_const_mul _ hO
  have heq : ∀ k, ∫⁻ x in (fun x => γ k * x) '' O, f x ∂μ = ∫⁻ x in O, f x ∂μ := by
    intro k
    rw [← lintegral_indicator (hmeas k), ← lintegral_indicator hO,
      ← lintegral_mul_left_eq_self (fun x => ((fun x => γ k * x) '' O).indicator f x) (γ k)]
    congr 1
    funext x
    by_cases hx : x ∈ O
    · have hx' : γ k * x ∈ (fun x => γ k * x) '' O := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hf]
    · have hx' : γ k * x ∉ (fun x => γ k * x) '' O := by
        rintro ⟨y, hy, hyx⟩
        exact hx (mul_left_cancel (hyx : γ k * y = γ k * x) ▸ hy)
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, ∫⁻ x in O, f x ∂μ := (ENNReal.tsum_const_eq_top_of_ne_zero hpos).symm
    _ = ∑' k : ℕ, ∫⁻ x in (fun x => γ k * x) '' O, f x ∂μ := by simp_rw [heq]
    _ = ∫⁻ x in ⋃ k, (fun x => γ k * x) '' O, f x ∂μ := (lintegral_iUnion hmeas hdisj f).symm
    _ ≤ ∫⁻ x in W, f x ∂μ := lintegral_mono_set (Set.iUnion_subset hsub)

end Generic

section Completion

variable {K : Type} [Field K]

private theorem norm_intCast_completion (w : InfinitePlace K) (m : ℤ) :
    ‖((m : ℤ) : w.Completion)‖ = |(m : ℝ)| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    map_intCast, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_ratCast_completion (w : InfinitePlace K) (q : ℚ) :
    ‖((q : ℚ) : w.Completion)‖ = |(q : ℝ)| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

end Completion

section Unipotent

private def lowerUnip (n : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; n, 1], by simp [Matrix.det_fin_two]⟩

end Unipotent

section Window

variable {L : Type*} [NormedField L]

private theorem xWindowSq_le_div (s : GL (Fin 2) L) :
    xWindowSq s ≤ topNormSq (s : Matrix (Fin 2) (Fin 2) L) / rowNormSq (s : Matrix (Fin 2) (Fin 2) L) := by
  unfold xWindowSq
  exact sub_le_self _ (sq_nonneg _)

private theorem topNormSq_le_of_entries {M : Matrix (Fin 2) (Fin 2) L} {β : ℝ} (_hβ : 0 ≤ β)
    (h : ∀ i j, ‖M i j‖ ≤ β) : topNormSq M ≤ 2 * β ^ 2 := by
  unfold topNormSq
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (h 0 0) 2
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (h 0 1) 2
  linarith

private theorem sq_le_rowNormSq (M : Matrix (Fin 2) (Fin 2) L) (j : Fin 2) :
    ‖M 1 j‖ ^ 2 ≤ rowNormSq M := by
  unfold rowNormSq
  fin_cases j
  · simp
  · simp

end Window

section Adelic

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
private theorem coe_mapGL_lowerUnip {w : InfinitePlace K} (n : ℤ) :
    ((Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = !![1, 0; (n : w.Completion), 1] := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.mapGL, lowerUnip]
  fin_cases i <;> fin_cases j <;> simp [eq_intCast]

omit [NumberField K] in
private theorem lowerUnip_mul_apply_zero {w : InfinitePlace K} (n : ℤ) (s : GL (Fin 2) w.Completion)
    (j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) * s : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 j = (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_mapGL_lowerUnip]
  simp

omit [NumberField K] in
private theorem lowerUnip_mul_apply_one {w : InfinitePlace K} (n : ℤ) (s : GL (Fin 2) w.Completion)
    (j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) * s : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 j
      = (n : w.Completion) * (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j
          + (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_mapGL_lowerUnip]
  simp

omit [NumberField K] in
private theorem det_lowerUnip_mul {w : InfinitePlace K} (n : ℤ) (s : GL (Fin 2) w.Completion) :
    ((Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) * s : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = (s : Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Units.val_mul, Matrix.det_mul, coe_mapGL_lowerUnip, Matrix.det_fin_two_of]
  simp

private noncomputable def aC (w : InfinitePlace K) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    GL (Fin 2) w.Completion :=
  archComponent K w (glArch (𝓞 K) K g)

private theorem aC_mul (w : InfinitePlace K) (g g' : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    aC w (g * g') = aC w g * aC w g' := by
  unfold aC
  rw [map_mul, map_mul]

private theorem continuous_aC (w : InfinitePlace K) : Continuous (aC (K := K) w) :=
  (continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K)

private theorem archDetNorm_eq_aC (w : InfinitePlace K) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    archDetNorm w g = ‖((aC w g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ :=
  rfl

private noncomputable def unipT (n : ℤ) : AutomorphicForm.AdelicGL2 (𝓞 K) K :=
  AutomorphicForm.globalPoints (𝓞 K) K (Matrix.SpecialLinearGroup.mapGL K (lowerUnip n))

private theorem aC_unipT_mul (w : InfinitePlace K) (n : ℤ) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    aC w (unipT n * g) = Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) * aC w g := by
  rw [aC_mul]
  unfold aC unipT
  rw [archComponent_glArch_globalPoints_mapGL]

private theorem glFin_unipT_mul {g : AutomorphicForm.AdelicGL2 (𝓞 K) K}
    (hg : glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K) (n : ℤ) :
    glFin (𝓞 K) K (unipT n * g) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [map_mul]
  exact mul_mem (glFin_globalPoints_mapGL_mem _) hg

private theorem archDetNorm_unipT_mul (w : InfinitePlace K) (n : ℤ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) : archDetNorm w (unipT n * g) = archDetNorm w g := by
  rw [archDetNorm_eq_aC, archDetNorm_eq_aC, aC_unipT_mul, det_lowerUnip_mul]

private theorem toFun_unipT_mul {pins : AutomorphicForm.CarrierPins K}
    {Ψ : AutomorphicForm.HeckeEigensystem K ℂ} (R : AutomorphicForm.SmoothCuspRealizationAt K pins Ψ)
    (n : ℤ) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) : R.toFun (unipT n * g) = R.toFun g :=
  R.left_invariant _ g

omit [NumberField K] in
private theorem xWindowSq_lowerUnip_mul_le {w : InfinitePlace K} (s : GL (Fin 2) w.Completion)
    {τ β u : ℝ} (hτ : 0 < τ) (hβ : 0 ≤ β) (j : Fin 2)
    (hj : τ ≤ ‖(s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖)
    (hent : ∀ i j', ‖(s : Matrix (Fin 2) (Fin 2) w.Completion) i j'‖ ≤ β)
    (n : ℕ) (hn : 2 * β ≤ ((n : ℝ) * τ - β) * |u|) :
    xWindowSq (Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) * s) ≤ u ^ 2 := by
  set A := Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip n) * s with hA
  have hAtop : ∀ j', ‖(A : Matrix (Fin 2) (Fin 2) w.Completion) 0 j'‖ ≤ β := by
    intro j'
    rw [hA, lowerUnip_mul_apply_zero]
    exact hent 0 j'
  have htop : topNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion) ≤ 2 * β ^ 2 := by
    unfold topNormSq
    have h0 := pow_le_pow_left₀ (norm_nonneg _) (hAtop 0) 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hAtop 1) 2
    linarith
  have hbot : (n : ℝ) * τ - β ≤ ‖(A : Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖ := by
    rw [hA, lowerUnip_mul_apply_one]
    set a := (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j
    set b := (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 j
    have hna : (n : ℝ) * τ ≤ ‖((n : ℤ) : w.Completion) * a‖ := by
      rw [norm_mul, norm_intCast_completion]
      have : |((n : ℤ) : ℝ)| = (n : ℝ) := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg n)
    have hb : ‖b‖ ≤ β := hent 1 j
    have htri : ‖((n : ℤ) : w.Completion) * a‖ ≤ ‖((n : ℤ) : w.Completion) * a + b‖ + ‖b‖ := by
      have := norm_sub_le (((n : ℤ) : w.Completion) * a + b) b
      simpa using this
    linarith
  have hnτ : 0 ≤ (n : ℝ) * τ - β := by
    by_contra hneg
    push Not at hneg
    have hnt : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
    have hprod : 0 ≤ (β - (n : ℝ) * τ) * |u| := mul_nonneg (by linarith) (abs_nonneg u)
    nlinarith [hprod, hn, hβ, hnt]
  have hrow : ((n : ℝ) * τ - β) ^ 2 ≤ rowNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion) :=
    (pow_le_pow_left₀ hnτ hbot 2).trans (sq_le_rowNormSq _ j)
  have hrowpos : 0 < rowNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion) := rowNormSq_pos A
  have hkey : 2 * β ^ 2 ≤ u ^ 2 * ((n : ℝ) * τ - β) ^ 2 := by
    have h1 : (2 * β) ^ 2 ≤ (((n : ℝ) * τ - β) * |u|) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hn 2
    have h2 : (((n : ℝ) * τ - β) * |u|) ^ 2 = u ^ 2 * ((n : ℝ) * τ - β) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    nlinarith [h1, h2, sq_nonneg β]
  calc xWindowSq A
      ≤ topNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion)
          / rowNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion) := xWindowSq_le_div A
    _ ≤ u ^ 2 := by
        rw [div_le_iff₀ hrowpos]
        calc topNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion) ≤ 2 * β ^ 2 := htop
          _ ≤ u ^ 2 * ((n : ℝ) * τ - β) ^ 2 := hkey
          _ ≤ u ^ 2 * rowNormSq (A : Matrix (Fin 2) (Fin 2) w.Completion) :=
              mul_le_mul_of_nonneg_left hrow (sq_nonneg u)

omit [NumberField K] in
private theorem abs_sub_mul_le_of_eq {w : InfinitePlace K} {s s' : GL (Fin 2) w.Completion} {a b : ℤ}
    (h : Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip a) * s
        = Matrix.SpecialLinearGroup.mapGL w.Completion (lowerUnip b) * s')
    {τ β : ℝ} (j : Fin 2) (hj : τ ≤ ‖(s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖)
    (hs : ‖(s : Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖ ≤ β)
    (hs' : ‖(s' : Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖ ≤ β) :
    |((a - b : ℤ) : ℝ)| * τ ≤ 2 * β := by
  have h0 := congrArg (fun A : GL (Fin 2) w.Completion => (A : Matrix (Fin 2) (Fin 2) w.Completion) 0 j) h
  have h1 := congrArg (fun A : GL (Fin 2) w.Completion => (A : Matrix (Fin 2) (Fin 2) w.Completion) 1 j) h
  simp only [lowerUnip_mul_apply_zero, lowerUnip_mul_apply_one] at h0 h1
  set x := (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j
  set y := (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 j
  set y' := (s' : Matrix (Fin 2) (Fin 2) w.Completion) 1 j
  have hdiff : ((a - b : ℤ) : w.Completion) * x = y' - y := by
    rw [← h0] at h1
    push_cast
    linear_combination h1
  have hτ0 : τ ≤ ‖x‖ := hj
  have hnorm : ‖((a - b : ℤ) : w.Completion) * x‖ ≤ 2 * β := by
    rw [hdiff]
    calc ‖y' - y‖ ≤ ‖y'‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ β + β := add_le_add hs' hs
      _ = 2 * β := by ring
  rw [norm_mul, norm_intCast_completion] at hnorm
  calc |((a - b : ℤ) : ℝ)| * τ ≤ |((a - b : ℤ) : ℝ)| * ‖x‖ :=
        mul_le_mul_of_nonneg_left hτ0 (abs_nonneg _)
    _ ≤ 2 * β := hnorm

private noncomputable def archRescale (q : InfinitePlace K → ℚ)
    (hq : ∀ w : InfinitePlace K, ((q w : ℚ) : w.Completion) ≠ 0) : (AdeleRing (𝓞 K) K)ˣ where
  val := (fun w => ((q w : ℚ) : w.Completion), 1)
  inv := (fun w => ((q w : ℚ) : w.Completion)⁻¹, 1)
  val_inv := by
    refine Prod.ext (funext fun w => ?_) (one_mul 1)
    exact mul_inv_cancel₀ (hq w)
  inv_val := by
    refine Prod.ext (funext fun w => ?_) (one_mul 1)
    exact inv_mul_cancel₀ (hq w)

private theorem archRescale_fst (q : InfinitePlace K → ℚ) (hq) (w : InfinitePlace K) :
    ((archRescale q hq : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = ((q w : ℚ) : w.Completion) :=
  rfl

private theorem archRescale_snd (q : InfinitePlace K → ℚ) (hq) :
    ((archRescale q hq : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 :=
  rfl

private theorem archDetNorm_centralScalar_mul' (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    archDetNorm w (AutomorphicForm.centralScalar (𝓞 K) K z * g)
      = (‖((z : AdeleRing (𝓞 K) K)).1 w‖ * ‖((z : AdeleRing (𝓞 K) K)).1 w‖) * archDetNorm w g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  set s := archComponent K w (glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then ((z : AdeleRing (𝓞 K) K)).1 w else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

private theorem glFin_centralScalar_archRescale (q : InfinitePlace K → ℚ) (hq) :
    glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (archRescale q hq)) = 1 :=
  glFin_scalar_eq_one K (archRescale_snd q hq) (centralScalar_apply_eq _ 0)
    (centralScalar_apply_ne _ (by decide)) (centralScalar_apply_ne _ (by decide))
    (centralScalar_apply_eq _ 1)

private theorem exists_rat_sq_mul_mem {d₁ d₂ δ : ℝ} (hd : d₁ < d₂) (hd₂ : 0 < d₂) (hδ : 0 < δ) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ d₁ < (q : ℝ) ^ 2 * δ ∧ (q : ℝ) ^ 2 * δ < d₂ := by
  set lo : ℝ := max d₁ 0 with hlo
  have hlo0 : 0 ≤ lo := le_max_right _ _
  have hlod : lo < d₂ := max_lt hd hd₂
  have hdiv : lo / δ < d₂ / δ := div_lt_div_of_pos_right hlod hδ
  have hsqrt : Real.sqrt (lo / δ) < Real.sqrt (d₂ / δ) :=
    Real.sqrt_lt_sqrt (div_nonneg hlo0 hδ.le) hdiv
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hsqrt
  have hqpos : 0 < (q : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hq₁
  refine ⟨q, hqpos, ?_, ?_⟩
  · have h1 : lo / δ < (q : ℝ) ^ 2 := Real.lt_sq_of_sqrt_lt hq₁
    have h2 : lo < (q : ℝ) ^ 2 * δ := (div_lt_iff₀ hδ).mp h1
    exact lt_of_le_of_lt (le_max_left _ _) h2
  · have h1 : (q : ℝ) ^ 2 < d₂ / δ := (Real.lt_sqrt hqpos.le).mp hq₂
    exact (lt_div_iff₀ hδ).mp h1

private theorem exists_rescale {d₁ d₂ : ℝ} (hd : d₁ < d₂) (hd₂ : 0 < d₂)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ,
      glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) = 1 ∧
      ∀ w : InfinitePlace K, d₁ < archDetNorm w (AutomorphicForm.centralScalar (𝓞 K) K z * g) ∧
        archDetNorm w (AutomorphicForm.centralScalar (𝓞 K) K z * g) < d₂ := by
  have hchoice : ∀ w : InfinitePlace K, ∃ q : ℚ, 0 < (q : ℝ) ∧
      d₁ < (q : ℝ) ^ 2 * archDetNorm w g ∧ (q : ℝ) ^ 2 * archDetNorm w g < d₂ :=
    fun w => exists_rat_sq_mul_mem hd hd₂ (archDetNorm_pos w g)
  choose q hqpos hq₁ hq₂ using hchoice
  have hnorm : ∀ w : InfinitePlace K, ‖((q w : ℚ) : w.Completion)‖ = (q w : ℝ) := by
    intro w
    rw [norm_ratCast_completion, abs_of_pos (hqpos w)]
  have hne : ∀ w : InfinitePlace K, ((q w : ℚ) : w.Completion) ≠ 0 := by
    intro w
    rw [← norm_pos_iff, hnorm w]
    exact hqpos w
  refine ⟨archRescale q hne, glFin_centralScalar_archRescale q hne, fun w => ?_⟩
  rw [archDetNorm_centralScalar_mul', archRescale_fst, hnorm w, ← sq]
  exact ⟨hq₁ w, hq₂ w⟩

omit [NumberField K] in
private theorem exists_top_entry_ne_zero {w : InfinitePlace K} (s : GL (Fin 2) w.Completion) :
    ∃ j : Fin 2, (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero s
  apply hdet
  rw [Matrix.det_fin_two, hcon 0, hcon 1]
  ring

end Adelic

section NullX

variable {K : Type} [Field K] [NumberField K]

private theorem lagrange_identity (α β γ δ : ℂ) :
    (‖α‖ ^ 2 + ‖β‖ ^ 2) * (‖γ‖ ^ 2 + ‖δ‖ ^ 2) - ‖α * δ - β * γ‖ ^ 2
      = ‖α * (starRingEnd ℂ) γ + β * (starRingEnd ℂ) δ‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

omit [NumberField K] in
private theorem conjSum_eq_zero_of_xWindowSq_nonpos {w : InfinitePlace K} (M : GL (Fin 2) w.Completion)
    (h : xWindowSq M ≤ 0) :
    InfinitePlace.Completion.extensionEmbedding w ((M : Matrix (Fin 2) (Fin 2) w.Completion) 0 0)
        * (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w
            ((M : Matrix (Fin 2) (Fin 2) w.Completion) 1 0))
      + InfinitePlace.Completion.extensionEmbedding w ((M : Matrix (Fin 2) (Fin 2) w.Completion) 0 1)
        * (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w
            ((M : Matrix (Fin 2) (Fin 2) w.Completion) 1 1)) = 0 := by
  set e := InfinitePlace.Completion.extensionEmbedding w with he
  set N := (M : Matrix (Fin 2) (Fin 2) w.Completion) with hN
  have hnorm : ∀ x : w.Completion, ‖e x‖ = ‖x‖ := fun x =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  have hdet : e N.det = e (N 0 0) * e (N 1 1) - e (N 0 1) * e (N 1 0) := by
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
  have hlag := lagrange_identity (e (N 0 0)) (e (N 0 1)) (e (N 1 0)) (e (N 1 1))
  rw [← hdet] at hlag
  simp only [hnorm] at hlag
  have hr : 0 < rowNormSq N := rowNormSq_pos M
  have hX : ‖e (N 0 0) * (starRingEnd ℂ) (e (N 1 0)) + e (N 0 1) * (starRingEnd ℂ) (e (N 1 1))‖ ^ 2
      ≤ 0 := by
    rw [← hlag]
    unfold xWindowSq localHeight at h
    have key : (topNormSq N / rowNormSq N - (‖N.det‖ / rowNormSq N) ^ 2) * rowNormSq N ^ 2
        = topNormSq N * rowNormSq N - ‖N.det‖ ^ 2 := by
      field_simp
    have h2 : (topNormSq N / rowNormSq N - (‖N.det‖ / rowNormSq N) ^ 2) * rowNormSq N ^ 2 ≤ 0 := by
      nlinarith [h, sq_nonneg (rowNormSq N)]
    rw [key] at h2
    unfold topNormSq rowNormSq at h2
    linarith
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hX (sq_nonneg _)))

variable {L : Type*} [Field L]

private def unipL (t : L) : GL (Fin 2) L where
  val := !![1, t; 0, 1]
  inv := !![1, -t; 0, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem coe_unipL (t : L) :
    ((unipL t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, t; 0, 1] := rfl

private theorem mul_unipL_mul_apply_00 (A B : GL (Fin 2) L) (t : L) :
    ((A * unipL t * B : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0
      = ((A : Matrix (Fin 2) (Fin 2) L) 0 0 * (B : Matrix (Fin 2) (Fin 2) L) 0 0
          + (A : Matrix (Fin 2) (Fin 2) L) 0 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 0)
        + t * ((A : Matrix (Fin 2) (Fin 2) L) 0 0 * (B : Matrix (Fin 2) (Fin 2) L) 1 0) := by
  rw [Units.val_mul, Units.val_mul, coe_unipL]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem mul_unipL_mul_apply_01 (A B : GL (Fin 2) L) (t : L) :
    ((A * unipL t * B : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1
      = ((A : Matrix (Fin 2) (Fin 2) L) 0 0 * (B : Matrix (Fin 2) (Fin 2) L) 0 1
          + (A : Matrix (Fin 2) (Fin 2) L) 0 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 1)
        + t * ((A : Matrix (Fin 2) (Fin 2) L) 0 0 * (B : Matrix (Fin 2) (Fin 2) L) 1 1) := by
  rw [Units.val_mul, Units.val_mul, coe_unipL]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem mul_unipL_mul_apply_10 (A B : GL (Fin 2) L) (t : L) :
    ((A * unipL t * B : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0
      = ((A : Matrix (Fin 2) (Fin 2) L) 1 0 * (B : Matrix (Fin 2) (Fin 2) L) 0 0
          + (A : Matrix (Fin 2) (Fin 2) L) 1 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 0)
        + t * ((A : Matrix (Fin 2) (Fin 2) L) 1 0 * (B : Matrix (Fin 2) (Fin 2) L) 1 0) := by
  rw [Units.val_mul, Units.val_mul, coe_unipL]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem mul_unipL_mul_apply_11 (A B : GL (Fin 2) L) (t : L) :
    ((A * unipL t * B : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1
      = ((A : Matrix (Fin 2) (Fin 2) L) 1 0 * (B : Matrix (Fin 2) (Fin 2) L) 0 1
          + (A : Matrix (Fin 2) (Fin 2) L) 1 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 1)
        + t * ((A : Matrix (Fin 2) (Fin 2) L) 1 0 * (B : Matrix (Fin 2) (Fin 2) L) 1 1) := by
  rw [Units.val_mul, Units.val_mul, coe_unipL]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem finite_roots_quadratic {X₀ X₁ X₂ : ℂ} (h : X₁ ≠ 0 ∨ X₂ ≠ 0) :
    {ζ : ℂ | X₀ + ζ * X₁ + ζ ^ 2 * X₂ = 0}.Finite := by
  set p : Polynomial ℂ := Polynomial.C X₀ + Polynomial.C X₁ * Polynomial.X
    + Polynomial.C X₂ * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 : p.coeff 1 = X₁ := by simp [hp, Polynomial.coeff_C]
    have h2 : p.coeff 2 = X₂ := by simp [hp]
    rw [h0, Polynomial.coeff_zero] at h1 h2
    rcases h with h | h
    · exact h h1.symm
    · exact h h2.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  intro ζ hζ
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  have hζ' : X₀ + ζ * X₁ + ζ ^ 2 * X₂ = 0 := hζ
  linear_combination hζ'

omit [NumberField K] in
private theorem finite_bad_params {w : InfinitePlace K} (A B : GL (Fin 2) w.Completion) :
    {t : w.Completion |
      (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w t)
          = InfinitePlace.Completion.extensionEmbedding w t ∧
        xWindowSq (A * unipL t * B) ≤ 0}.Finite := by
  set e := InfinitePlace.Completion.extensionEmbedding w with he
  set a := e ((A : Matrix (Fin 2) (Fin 2) w.Completion) 0 0) with ha
  set b := e ((A : Matrix (Fin 2) (Fin 2) w.Completion) 0 1) with hb
  set c := e ((A : Matrix (Fin 2) (Fin 2) w.Completion) 1 0) with hc
  set d := e ((A : Matrix (Fin 2) (Fin 2) w.Completion) 1 1) with hd
  set p := e ((B : Matrix (Fin 2) (Fin 2) w.Completion) 0 0) with hp
  set q := e ((B : Matrix (Fin 2) (Fin 2) w.Completion) 0 1) with hq
  set r := e ((B : Matrix (Fin 2) (Fin 2) w.Completion) 1 0) with hr
  set s := e ((B : Matrix (Fin 2) (Fin 2) w.Completion) 1 1) with hs
  set X₀ : ℂ := (a * p + b * r) * ((starRingEnd ℂ) c * (starRingEnd ℂ) p + (starRingEnd ℂ) d * (starRingEnd ℂ) r)
    + (a * q + b * s) * ((starRingEnd ℂ) c * (starRingEnd ℂ) q + (starRingEnd ℂ) d * (starRingEnd ℂ) s) with hX₀
  set X₁ : ℂ := (a * p + b * r) * ((starRingEnd ℂ) c * (starRingEnd ℂ) r)
    + (a * r) * ((starRingEnd ℂ) c * (starRingEnd ℂ) p + (starRingEnd ℂ) d * (starRingEnd ℂ) r)
    + (a * q + b * s) * ((starRingEnd ℂ) c * (starRingEnd ℂ) s)
    + (a * s) * ((starRingEnd ℂ) c * (starRingEnd ℂ) q + (starRingEnd ℂ) d * (starRingEnd ℂ) s) with hX₁
  set X₂ : ℂ := (a * r) * ((starRingEnd ℂ) c * (starRingEnd ℂ) r)
    + (a * s) * ((starRingEnd ℂ) c * (starRingEnd ℂ) s) with hX₂
  have hrs : r * (starRingEnd ℂ) r + s * (starRingEnd ℂ) s
      = ((Complex.normSq r + Complex.normSq s : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj]
    push_cast
    ring
  have hRpos : 0 < Complex.normSq r + Complex.normSq s := by
    rcases bottom_row_ne_zero B with h | h
    · have : r ≠ 0 := (map_ne_zero e).mpr h
      exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr this) (Complex.normSq_nonneg _)
    · have : s ≠ 0 := (map_ne_zero e).mpr h
      exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr this)
  have hR : ((Complex.normSq r + Complex.normSq s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRpos.ne'
  have hdetA : a * d - b * c ≠ 0 := by
    have h0 := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [Matrix.det_fin_two] at h0
    have : e ((A : Matrix (Fin 2) (Fin 2) w.Completion).det) ≠ 0 := by
      rw [Matrix.det_fin_two]
      exact (map_ne_zero e).mpr h0
    rwa [Matrix.det_fin_two, map_sub, map_mul, map_mul] at this
  have hnz : X₁ ≠ 0 ∨ X₂ ≠ 0 := by
    by_cases hc0 : c = 0
    ·
      have had : a * d ≠ 0 := by simpa [hc0] using hdetA
      left
      have : X₁ = a * (starRingEnd ℂ) d * (r * (starRingEnd ℂ) r + s * (starRingEnd ℂ) s) := by
        simp only [hX₁, hc0, map_zero, zero_mul, mul_zero, zero_add, add_zero]
        ring
      rw [this, hrs]
      exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul had)
        ((map_ne_zero (starRingEnd ℂ)).mpr (right_ne_zero_of_mul had))) hR
    · by_cases ha0 : a = 0
      ·
        have hbc : b * c ≠ 0 := by
          intro hbc
          apply hdetA
          rw [ha0, zero_mul, zero_sub, hbc, neg_zero]
        left
        have : X₁ = b * (starRingEnd ℂ) c * (r * (starRingEnd ℂ) r + s * (starRingEnd ℂ) s) := by
          simp only [hX₁, ha0, zero_mul, zero_add, add_zero]
          ring
        rw [this, hrs]
        exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul hbc)
          ((map_ne_zero (starRingEnd ℂ)).mpr hc0)) hR
      ·
        right
        have : X₂ = a * (starRingEnd ℂ) c * (r * (starRingEnd ℂ) r + s * (starRingEnd ℂ) s) := by
          simp only [hX₂]
          ring
        rw [this, hrs]
        exact mul_ne_zero (mul_ne_zero ha0 ((map_ne_zero (starRingEnd ℂ)).mpr hc0)) hR
  refine ((finite_roots_quadratic (X₀ := X₀) hnz).preimage e.injective.injOn).subset ?_
  rintro t ⟨hreal, hxw⟩
  have hX := conjSum_eq_zero_of_xWindowSq_nonpos (A * unipL t * B) hxw
  rw [mul_unipL_mul_apply_00, mul_unipL_mul_apply_01, mul_unipL_mul_apply_10,
    mul_unipL_mul_apply_11] at hX
  simp only [map_add, map_mul] at hX
  show X₀ + e t * X₁ + (e t) ^ 2 * X₂ = 0
  rw [← he] at hX
  simp only [← ha, ← hb, ← hc, ← hd, ← hp, ← hq, ← hr, ← hs, hreal] at hX
  simp only [hX₀, hX₁, hX₂]
  linear_combination hX

omit [NumberField K] in
private theorem exists_param_notMem (w : InfinitePlace K) {C : Set w.Completion} (hC : C.Countable) :
    ∃ t : w.Completion, t ∉ C ∧
      (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w t)
        = InfinitePlace.Completion.extensionEmbedding w t := by
  by_contra hcon
  push Not at hcon
  have hinj : ∃ f : ℝ → w.Completion, Function.Injective f ∧ ∀ x : ℝ, f x ∈ C := by
    rcases w.isReal_or_isComplex with hw | hw
    · have hsurj := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw
      refine ⟨Function.surjInv hsurj, Function.injective_surjInv hsurj, fun x => ?_⟩
      by_contra hx
      apply hcon _ hx
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, Complex.conj_ofReal]
    · have hsurj := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
      refine ⟨fun x : ℝ => Function.surjInv hsurj (x : ℂ), fun x y hxy => ?_, fun x => ?_⟩
      · have h := congrArg (InfinitePlace.Completion.extensionEmbedding w) hxy
        rw [Function.surjInv_eq hsurj, Function.surjInv_eq hsurj] at h
        exact_mod_cast h
      · by_contra hx
        apply hcon _ hx
        rw [Function.surjInv_eq hsurj, Complex.conj_ofReal]
  obtain ⟨f, hfinj, hfC⟩ := hinj
  haveI : Countable C := hC.to_subtype
  have hcount : Countable ℝ :=
    Function.Injective.countable (f := fun x : ℝ => (⟨f x, hfC x⟩ : C))
      (fun x y hxy => hfinj (congrArg Subtype.val hxy))
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hcount)

private theorem countable_GL2 : Countable (GL (Fin 2) K) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Units.val_injective.countable

open scoped Classical in
private noncomputable def tAdele (w : InfinitePlace K) (t : w.Completion) : AdeleRing (𝓞 K) K :=
  (Function.update (0 : InfiniteAdeleRing K) w t, 0)

private noncomputable def unipAdelic (w : InfinitePlace K) (t : w.Completion) :
    AutomorphicForm.AdelicGL2 (𝓞 K) K where
  val := !![1, tAdele w t; 0, 1]
  inv := !![1, -(tAdele w t); 0, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

open scoped Classical in
private theorem aC_unipAdelic (w : InfinitePlace K) (t : w.Completion) :
    aC w (unipAdelic w t) = unipL t := by
  apply Units.ext
  ext i j
  simp only [aC, archComponent_apply, glArch_apply, coe_unipL]
  fin_cases i <;> fin_cases j <;> simp [unipAdelic, tAdele] <;> rfl

private theorem aC_centralScalar_apply (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((aC w (AutomorphicForm.centralScalar (𝓞 K) K z) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then ((z : AdeleRing (𝓞 K) K)).1 w else 0 := by
  simp only [aC, archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem units_fst_apply_ne_zero (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ((z : AdeleRing (𝓞 K) K)).1 w ≠ 0 := by
  have h := congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) z.val_inv
  exact left_ne_zero_of_mul_eq_one (show ((z : AdeleRing (𝓞 K) K)).1 w
    * (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 from h)

private theorem xWindowSq_aC_centralScalar_mul (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ)
    (X : GL (Fin 2) w.Completion) :
    xWindowSq (aC w (AutomorphicForm.centralScalar (𝓞 K) K z) * X) = xWindowSq X :=
  xWindowSq_scalar_entries_mul (units_fst_apply_ne_zero z w)
    (by rw [aC_centralScalar_apply, if_pos rfl]) (by rw [aC_centralScalar_apply, if_neg (by decide)])
    (by rw [aC_centralScalar_apply, if_neg (by decide)]) (by rw [aC_centralScalar_apply, if_pos rfl]) X

private theorem not_coversModCentre_of_u_eq_zero {c d₁ d₂ : ℝ}
    (T : Finset (AutomorphicForm.AdelicGL2 (𝓞 K) K)) :
    ¬ CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c 0 d₁ d₂) := by
  intro hcov
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  haveI : Countable (GL (Fin 2) K) := countable_GL2
  set bad : Set w₀.Completion := ⋃ γ : GL (Fin 2) K, ⋃ x₀ ∈ T,
    {t : w₀.Completion |
      (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w₀ t)
          = InfinitePlace.Completion.extensionEmbedding w₀ t ∧
        xWindowSq (aC w₀ (AutomorphicForm.globalPoints (𝓞 K) K γ) * unipL t * aC w₀ x₀⁻¹) ≤ 0} with hbad
  have hcount : bad.Countable :=
    Set.countable_iUnion fun γ => T.countable_toSet.biUnion fun x₀ _ => (finite_bad_params _ _).countable
  obtain ⟨t, ht, hreal⟩ := exists_param_notMem w₀ hcount
  obtain ⟨γ, z, hmem⟩ := hcov (unipAdelic w₀ t)
  obtain ⟨x₀, hx₀, hs⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨s, hsS, hsx⟩ := hs
  simp only at hsx
  rw [mem_centreCutSiegelSet_iff] at hsS
  have hx : xWindowSq (aC w₀ s) ≤ (0 : ℝ) ^ 2 := hsS.2.2.1 w₀
  have hs_eq : s = AutomorphicForm.centralScalar (𝓞 K) K z
      * (AutomorphicForm.globalPoints (𝓞 K) K γ * unipAdelic w₀ t * x₀⁻¹) := by
    rw [← mul_assoc, ← mul_centralScalar_comm, eq_mul_inv_iff_mul_eq]
    exact hsx
  apply ht
  refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨x₀, hx₀, hreal, ?_⟩⟩
  rw [hs_eq, aC_mul, xWindowSq_aC_centralScalar_mul, aC_mul, aC_mul, aC_unipAdelic] at hx
  simpa using hx

end NullX

section Core

variable {K : Type} [Field K] [NumberField K]

private theorem no_function_of_ne_zero {c u d₁ d₂ : ℝ} {T : Finset (AutomorphicForm.AdelicGL2 (𝓞 K) K)}
    (hc : c ≤ 0) (hd : d₁ < d₂) (hu : u ≠ 0)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (U : Ideal (𝓞 K) → Subgroup (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (B : Set (AdeleRing (𝓞 K) K))
    (ξ : (AutomorphicForm.productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B).Z →* ℂˣ)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hauto : AutomorphicForm.IsAutomorphicFnAt K
      (AutomorphicForm.productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ξ φ)
    (hcont : Continuous φ) (g₀ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hg₀ : φ g₀ ≠ 0) : False := by
  revert ξ hauto
  set Sset := centreCutSiegelSet K c u d₁ d₂ with hSset
  set W := ⋃ x ∈ T, (· * x) '' Sset with hW
  set pins := AutomorphicForm.productionPinsOf K W U gen B with hpins
  intro ξ hauto
  letI : MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  set μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : MeasurableMul (AutomorphicForm.AdelicGL2 (𝓞 K) K) :=
    ⟨fun g => (continuous_const_mul g).measurable, fun g => (continuous_mul_const g).measurable⟩
  have hls := (AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K pins.μ pins.Z ξ pins.D φ).mp hauto
  have hL : AutomorphicForm.IsLsXiFunction (𝓞 K) K pins.Z ξ φ := hls.1
  have hmem : MemLp φ 2 (μ.restrict W) := hls.2
  obtain ⟨γ₀, z₀, hmemW⟩ := hcov g₀
  set h₁ := AutomorphicForm.globalPoints (𝓞 K) K γ₀ * g₀ * AutomorphicForm.centralScalar (𝓞 K) K z₀ with hh₁
  have hφh₁ : φ h₁ ≠ 0 := by
    have hz₀ : z₀ ∈ pins.Z := by
      show z₀ ∈ (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
      exact Subgroup.mem_top z₀
    have hinv : φ (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * g₀) = φ g₀ := hL.left_invariant γ₀ g₀
    rw [hh₁, mul_centralScalar_comm, hL.central_transform ⟨z₀, hz₀⟩, hinv]
    exact mul_ne_zero (Units.ne_zero _) hg₀
  obtain ⟨x₀, hx₀T, hs₁img⟩ := Set.mem_iUnion₂.mp hmemW
  obtain ⟨s₁, hs₁, hs₁x₀⟩ := hs₁img
  simp only at hs₁x₀
  rw [mem_centreCutSiegelSet_iff] at hs₁
  obtain ⟨hs₁fin, -, -, hs₁det⟩ := hs₁
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hd₂ : 0 < d₂ := lt_of_lt_of_le (archDetNorm_pos w₀ s₁) (hs₁det w₀).2
  obtain ⟨z, hzfin, hzdet⟩ := exists_rescale hd hd₂ s₁
  set s₂ := AutomorphicForm.centralScalar (𝓞 K) K z * s₁ with hs₂
  set h₂ := AutomorphicForm.centralScalar (𝓞 K) K z * h₁ with hh₂
  have hh₂x₀ : h₂ * x₀⁻¹ = s₂ := by
    rw [hh₂, ← hs₁x₀, hs₂, mul_assoc, mul_inv_cancel_right]
  have hφh₂ : φ h₂ ≠ 0 := by
    have hz : z ∈ pins.Z := by
      show z ∈ (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
      exact Subgroup.mem_top z
    rw [hh₂, hL.central_transform ⟨z, hz⟩]
    exact mul_ne_zero (Units.ne_zero _) hφh₁
  have hs₂fin : glFin (𝓞 K) K s₂ ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [hs₂, map_mul, hzfin, one_mul]
    exact hs₁fin
  have hcol : ∀ w : InfinitePlace K, ∃ j : Fin 2,
      ((aC w s₂ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 j ≠ 0 :=
    fun w => exists_top_entry_ne_zero (aC w s₂)
  choose jc hjc using hcol
  set τ : InfinitePlace K → ℝ := fun w =>
    ‖((aC w s₂ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 (jc w)‖ / 2 with hτdef
  have hτpos : ∀ w, 0 < τ w := fun w => half_pos (norm_pos_iff.mpr (hjc w))
  set ent : InfinitePlace K → Fin 2 → Fin 2 → AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ := fun w i j h =>
    ‖((aC w (h * x₀⁻¹) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j‖ with hentdef
  have hent_cont : ∀ w i j, Continuous (ent w i j) := fun w i j =>
    ((continuous_entry i j).comp ((continuous_aC w).comp (continuous_mul_const x₀⁻¹))).norm
  set β : InfinitePlace K → ℝ := fun w =>
    ent w 0 0 h₂ + ent w 0 1 h₂ + ent w 1 0 h₂ + ent w 1 1 h₂ + 1 with hβdef
  have hent_nonneg : ∀ w i j h, 0 ≤ ent w i j h := fun w i j h => norm_nonneg _
  have hβpos : ∀ w, 0 ≤ β w := fun w => by
    have := hent_nonneg w 0 0 h₂; have := hent_nonneg w 0 1 h₂
    have := hent_nonneg w 1 0 h₂; have := hent_nonneg w 1 1 h₂
    simp only [hβdef]; linarith
  have hβlt : ∀ w i j, ent w i j h₂ < β w := by
    intro w i j
    have h00 := hent_nonneg w 0 0 h₂; have h01 := hent_nonneg w 0 1 h₂
    have h10 := hent_nonneg w 1 0 h₂; have h11 := hent_nonneg w 1 1 h₂
    simp only [hβdef]
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  have hτlt : ∀ w, τ w < ent w 0 (jc w) h₂ := by
    intro w
    simp only [hentdef, hh₂x₀]
    exact half_lt_self (norm_pos_iff.mpr (hjc w))
  have hdet₂ : ∀ w, archDetNorm w (h₂ * x₀⁻¹) ∈ Set.Ioo d₁ d₂ := by
    intro w
    rw [hh₂x₀]
    exact hzdet w
  have hfin₂ : glFin (𝓞 K) K (h₂ * x₀⁻¹) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [hh₂x₀]; exact hs₂fin
  have hopen_fin : IsOpen {h : AutomorphicForm.AdelicGL2 (𝓞 K) K |
      glFin (𝓞 K) K (h * x₀⁻¹) ∈ finiteIntegralGL2 (𝓞 K) K} :=
    (isOpen_finiteLevelZero (𝓞 K) K top_ne_bot).preimage
      ((continuous_glFin (𝓞 K) K).comp (continuous_mul_const x₀⁻¹))
  have hev : ∀ᶠ h in nhds h₂,
      glFin (𝓞 K) K (h * x₀⁻¹) ∈ finiteIntegralGL2 (𝓞 K) K ∧
      (∀ w, archDetNorm w (h * x₀⁻¹) ∈ Set.Ioo d₁ d₂) ∧
      (∀ w, τ w ≤ ent w 0 (jc w) h) ∧
      (∀ w, ∀ i j, ent w i j h ≤ β w) ∧ φ h ≠ 0 := by
    have hev₁ : ∀ᶠ h in nhds h₂, glFin (𝓞 K) K (h * x₀⁻¹) ∈ finiteIntegralGL2 (𝓞 K) K :=
      hopen_fin.mem_nhds hfin₂
    refine hev₁.and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ ?_)))
    · rw [Filter.eventually_all]
      intro w
      exact ((continuous_archDetNorm w).comp (continuous_mul_const x₀⁻¹)).continuousAt.eventually_mem
        (Ioo_mem_nhds (hdet₂ w).1 (hdet₂ w).2)
    · rw [Filter.eventually_all]
      intro w
      exact ((hent_cont w 0 (jc w)).continuousAt.eventually_const_lt (hτlt w)).mono fun _ h => h.le
    · rw [Filter.eventually_all]
      intro w
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      exact ((hent_cont w i j).continuousAt.eventually_lt_const (hβlt w i j)).mono fun _ h => h.le
    · exact hcont.continuousAt.eventually_ne hφh₂
  obtain ⟨O, hOsub, hOopen, hh₂O⟩ := mem_nhds_iff.mp hev
  set Nw : InfinitePlace K → ℕ := fun w => ⌈(2 * β w / |u| + β w) / τ w⌉₊ with hNw
  set N₀ : ℕ := Finset.univ.sup Nw with hN₀
  have hupos : 0 < |u| := abs_pos.mpr hu
  have hthr : ∀ w : InfinitePlace K, ∀ n : ℕ, N₀ ≤ n → 2 * β w ≤ ((n : ℝ) * τ w - β w) * |u| := by
    intro w n hn
    have h1 : Nw w ≤ n := le_trans (Finset.le_sup (f := Nw) (Finset.mem_univ w)) hn
    have h2 : (2 * β w / |u| + β w) / τ w ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have h3 : 2 * β w / |u| + β w ≤ (n : ℝ) * τ w := (div_le_iff₀ (hτpos w)).mp h2
    have h4 : 2 * β w / |u| ≤ (n : ℝ) * τ w - β w := by linarith
    have h5 : 2 * β w ≤ ((n : ℝ) * τ w - β w) * |u| := (div_le_iff₀ hupos).mp h4
    exact h5
  set M : ℕ := ⌈2 * β w₀ / τ w₀⌉₊ + 1 with hM
  have hMτ : 2 * β w₀ < (M : ℝ) * τ w₀ := by
    have h1 : 2 * β w₀ / τ w₀ < (M : ℝ) := by
      rw [hM]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
    exact (div_lt_iff₀ (hτpos w₀)).mp h1
  set idx : ℕ → ℕ := fun k => N₀ + k * M with hidx
  set γ : ℕ → AutomorphicForm.AdelicGL2 (𝓞 K) K := fun k => unipT (idx k : ℤ) with hγ
  have htrans : ∀ k, (fun x => γ k * x) '' O ⊆ W := by
    rintro k _ ⟨h, hhO, rfl⟩
    obtain ⟨hfin, hdet, hτh, hβh, -⟩ := hOsub hhO
    have hS : unipT (idx k : ℤ) * (h * x₀⁻¹) ∈ Sset := by
      rw [hSset, mem_centreCutSiegelSet_iff]
      refine ⟨glFin_unipT_mul hfin _, fun w => ?_, fun w => ?_, fun w => ?_⟩
      · exact hc.trans (localHeight_pos _).le
      · show xWindowSq (aC w (unipT (idx k : ℤ) * (h * x₀⁻¹))) ≤ u ^ 2
        rw [aC_unipT_mul]
        refine xWindowSq_lowerUnip_mul_le (aC w (h * x₀⁻¹)) (hτpos w) (hβpos w) (jc w) (hτh w)
          (fun i j => hβh w i j) (idx k) (hthr w (idx k) (Nat.le_add_right _ _))
      · rw [archDetNorm_unipT_mul]
        exact Set.Ioo_subset_Icc_self (hdet w)
    refine Set.mem_iUnion₂.mpr ⟨x₀, hx₀T, unipT (idx k : ℤ) * (h * x₀⁻¹), hS, ?_⟩
    show unipT (idx k : ℤ) * (h * x₀⁻¹) * x₀ = γ k * h
    rw [hγ]
    simp [mul_assoc]
  have hdisj : Pairwise (Function.onFun Disjoint fun k => (fun x => γ k * x) '' O) := by
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨h, hhO, rfl⟩ ⟨h', hh'O, hh'⟩
    obtain ⟨-, -, hτh, hβh, -⟩ := hOsub hhO
    obtain ⟨-, -, hτh', hβh', -⟩ := hOsub hh'O
    have heq : aC w₀ (unipT (idx l : ℤ) * (h' * x₀⁻¹)) = aC w₀ (unipT (idx k : ℤ) * (h * x₀⁻¹)) := by
      congr 1
      have hh'' : γ l * h' = γ k * h := hh'
      have : γ l * h' * x₀⁻¹ = γ k * h * x₀⁻¹ := by rw [hh'']
      simpa only [hγ, mul_assoc] using this
    rw [aC_unipT_mul, aC_unipT_mul] at heq
    have hsep := abs_sub_mul_le_of_eq heq (jc w₀) (hτh' w₀) (hβh' w₀ 1 (jc w₀)) (hβh w₀ 1 (jc w₀))
    have hlk : (1 : ℝ) ≤ |((l : ℝ) - k)| := by
      have hne : (l : ℤ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkl.symm)
      have h1 : (1 : ℤ) ≤ |(l : ℤ) - k| := Int.one_le_abs hne
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|(l : ℤ) - k| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using h2
    have hcast : |((((idx l : ℕ) : ℤ) - ((idx k : ℕ) : ℤ) : ℤ) : ℝ)| = |((l : ℝ) - k)| * (M : ℝ) := by
      simp only [hidx]
      push_cast
      rw [show (N₀ : ℝ) + l * M - (N₀ + k * M) = ((l : ℝ) - k) * M by ring, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    rw [hcast] at hsep
    have hMτ' : (M : ℝ) * τ w₀ ≤ |((l : ℝ) - k)| * (M : ℝ) * τ w₀ := by
      have hMτnn : 0 ≤ (M : ℝ) * τ w₀ := mul_nonneg (Nat.cast_nonneg M) (hτpos w₀).le
      calc (M : ℝ) * τ w₀ = 1 * ((M : ℝ) * τ w₀) := (one_mul _).symm
        _ ≤ |((l : ℝ) - k)| * ((M : ℝ) * τ w₀) := mul_le_mul_of_nonneg_right hlk hMτnn
        _ = |((l : ℝ) - k)| * (M : ℝ) * τ w₀ := (mul_assoc _ _ _).symm
    linarith
  set f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ≥0∞ := fun h => ‖φ h‖ₑ ^ (2 : ℝ) with hfdef
  have hfmeas : Measurable f := hcont.measurable.enorm.pow_const (2 : ℝ)
  have hfO : ∀ h ∈ O, f h ≠ 0 := by
    intro h hh
    have hφ : φ h ≠ 0 := (hOsub hh).2.2.2.2
    simp only [hfdef]
    exact (ENNReal.rpow_pos (enorm_pos.mpr hφ) (enorm_ne_top)).ne'
  have hpos : ∫⁻ x in O, f x ∂μ ≠ 0 := by
    have hsupp : Function.support f ∩ O = O :=
      Set.inter_eq_right.mpr fun h hh => hfO h hh
    have := (setLIntegral_pos_iff hfmeas (s := O)).mpr (by rw [hsupp]; exact hOopen.measure_pos μ ⟨h₂, hh₂O⟩)
    exact this.ne'
  have hfinv : ∀ k x, f (γ k * x) = f x := by
    intro k x
    simp only [hfdef, hγ, unipT]
    rw [hL.left_invariant]
  have htop : ∫⁻ x in W, f x ∂μ = ⊤ :=
    lintegral_eq_top_of_disjoint_translates μ f γ hfinv O hOopen.measurableSet hpos W htrans hdisj
  have hlt : ∫⁻ x in W, ‖φ x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μ < ⊤ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hmem.eLpNorm_lt_top
  have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
  rw [h2] at hlt
  exact absurd htop hlt.ne

end Core

open AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : c ≤ 0) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ) :
    φ = 0 := by
  by_cases hu : u = 0
  · subst hu
    exact absurd hcov (not_coversModCentre_of_u_eq_zero T)
  · funext g
    by_contra hg
    exact no_function_of_ne_zero hc hd hu hcov _ _ _ ξ φ hφ hcont g hg

end S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre (solution)
