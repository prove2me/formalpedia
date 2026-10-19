-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:32:42.935122+00:00
-- url     : https://prove2.me/submissions/3a3bd7b8-b481-4c9c-9594-ed0ca814cd2e

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le_of_ne_pow_six
import Mathlib


section
section
/-! # L3S_Dual: the duality form of the large sieve with a weighted Gram matrix

For finitely many "characters" `φ r : β → ℂ` (`r ∈ T`) and a weight `W ≥ 0` with `W ≥ 1` on `B`:
if the weighted Gram entries `H(r, r') = ∑'_I W I φ_r(I) conj φ_r'(I)` satisfy `‖H(r,r)‖ ≤ D` and
`‖H(r, r')‖ ≤ O` for `r ≠ r'`, then `∑_r ‖∑_{I ∈ B} b I φ_r(I)‖² ≤ (D + |T| O) ∑_{I ∈ B} ‖b I‖²`. -/

set_option autoImplicit false

open Complex

namespace ArtinPrimitiveRoots

namespace L3S

theorem dual_sieve {α β : Type*} [DecidableEq α] (T : Finset α) (B : Finset β)
    (φ : α → β → ℂ) (b : β → ℂ) (W : β → ℝ) (hW0 : ∀ I, 0 ≤ W I) (hW1 : ∀ I ∈ B, 1 ≤ W I)
    (hs : ∀ r r', Summable (fun I => (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))))
    (D O : ℝ) (hD : 0 ≤ D) (hO : 0 ≤ O)
    (hH : ∀ r ∈ T, ∀ r' ∈ T,
      ‖∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))‖ ≤ if r = r' then D else O) :
    ∑ r ∈ T, ‖∑ I ∈ B, b I * φ r I‖ ^ 2 ≤ (D + T.card * O) * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  set S : α → ℂ := fun r => ∑ I ∈ B, b I * φ r I with hS
  set c : α → ℂ := fun r => starRingEnd ℂ (S r) with hc
  set L : ℝ := ∑ r ∈ T, ‖S r‖ ^ 2 with hL
  set Dv : β → ℂ := fun I => ∑ r ∈ T, c r * φ r I with hDv
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcn : ∀ r, ‖c r‖ = ‖S r‖ := fun r => by simp [hc]
  -- Step 1: `L = ∑_B b Dv`
  have h1 : (L : ℂ) = ∑ I ∈ B, b I * Dv I := by
    simp only [hL, hDv, Finset.mul_sum]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Complex.conj_mul', hc]
    simp only [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    ring
  -- Step 2: Cauchy–Schwarz
  have h2 : L ^ 2 ≤ (∑ I ∈ B, ‖b I‖ ^ 2) * ∑ I ∈ B, ‖Dv I‖ ^ 2 := by
    have hLe : L ≤ ∑ I ∈ B, ‖b I‖ * ‖Dv I‖ := by
      have : L = ‖(L : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hL0]
      rw [this, h1]
      refine (norm_sum_le _ _).trans ?_
      exact le_of_eq (Finset.sum_congr rfl fun I _ => norm_mul _ _)
    calc L ^ 2 ≤ (∑ I ∈ B, ‖b I‖ * ‖Dv I‖) ^ 2 := pow_le_pow_left₀ hL0 hLe 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq B _ _
  -- Step 4: the weighted sum of `‖Dv‖²` as a Gram form
  set f : β → ℂ := fun I => ∑ r ∈ T, ∑ r' ∈ T,
    c r * starRingEnd ℂ (c r') * ((W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))) with hf
  have hfI : ∀ I, ((W I * ‖Dv I‖ ^ 2 : ℝ) : ℂ) = f I := by
    intro I
    push_cast
    rw [← Complex.mul_conj', hDv, map_sum, Finset.sum_mul_sum]
    simp only [hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [map_mul]; ring
  have hfs : Summable f := by
    refine summable_sum fun r _ => summable_sum fun r' _ => ?_
    exact (hs r r').mul_left _
  have hWs : Summable fun I => W I * ‖Dv I‖ ^ 2 := by
    have := (Complex.reCLM.summable hfs)
    refine this.congr fun I => ?_
    simp only [Complex.reCLM_apply, ← hfI, Complex.ofReal_re]
  have htf : ((∑' I, W I * ‖Dv I‖ ^ 2 : ℝ) : ℂ) = ∑ r ∈ T, ∑ r' ∈ T, c r * starRingEnd ℂ (c r') *
      ∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I)) := by
    rw [Complex.ofReal_tsum]
    simp_rw [hfI]
    simp only [hf]
    rw [Summable.tsum_finsetSum (fun r _ => summable_sum fun r' _ => (hs r r').mul_left _)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Summable.tsum_finsetSum (fun r' _ => (hs r r').mul_left _)]
    refine Finset.sum_congr rfl fun r' _ => ?_
    exact (hs r r').tsum_mul_left _
  -- Step 3: positivity
  have h3 : ∑ I ∈ B, ‖Dv I‖ ^ 2 ≤ ∑' I, W I * ‖Dv I‖ ^ 2 := by
    calc ∑ I ∈ B, ‖Dv I‖ ^ 2 ≤ ∑ I ∈ B, W I * ‖Dv I‖ ^ 2 :=
          Finset.sum_le_sum fun I hI => le_mul_of_one_le_left (sq_nonneg _) (hW1 I hI)
      _ ≤ _ := hWs.sum_le_tsum B fun I _ => mul_nonneg (hW0 I) (sq_nonneg _)
  -- Step 5: the Gram bound
  have h5 : ∑' I, W I * ‖Dv I‖ ^ 2 ≤ (D + T.card * O) * L := by
    have hn : ∑' I, W I * ‖Dv I‖ ^ 2 = ‖((∑' I, W I * ‖Dv I‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg
        (tsum_nonneg fun I => mul_nonneg (hW0 I) (sq_nonneg _))]
    rw [hn, htf]
    have hb : ∀ r ∈ T, ∀ r' ∈ T, ‖c r * starRingEnd ℂ (c r') *
        ∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))‖ ≤
        ‖S r‖ * ‖S r'‖ * ((if r = r' then D else 0) + O) := by
      intro r hr r' hr'
      simp only [norm_mul, RCLike.norm_conj, hcn]
      refine mul_le_mul_of_nonneg_left ((hH r hr r' hr').trans ?_) (by positivity)
      split_ifs <;> linarith
    calc ‖∑ r ∈ T, ∑ r' ∈ T, c r * starRingEnd ℂ (c r') *
          ∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))‖
        ≤ ∑ r ∈ T, ∑ r' ∈ T, ‖S r‖ * ‖S r'‖ * ((if r = r' then D else 0) + O) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r' hr' => hb r hr r' hr')
      _ = D * L + O * (∑ r ∈ T, ‖S r‖) ^ 2 := by
          simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
          rw [sq, Finset.sum_mul_sum]
          congr 1
          · simp only [Finset.sum_ite_eq, hL, Finset.mul_sum]
            refine Finset.sum_congr rfl fun r hr => ?_
            rw [if_pos hr]; ring
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r' _ => ?_
            ring
      _ ≤ D * L + O * (T.card * L) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq
      _ = (D + T.card * O) * L := by ring
  -- conclusion
  have hfin : L ^ 2 ≤ ((D + T.card * O) * ∑ I ∈ B, ‖b I‖ ^ 2) * L := by
    calc L ^ 2 ≤ (∑ I ∈ B, ‖b I‖ ^ 2) * ((D + T.card * O) * L) :=
          h2.trans (mul_le_mul_of_nonneg_left (h3.trans h5)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      _ = _ := by ring
  rcases hL0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · rw [sq] at hfin
    exact le_of_mul_le_mul_right hfin hpos

end L3S

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3P_Shift: one-variable contour shifts of vertical line integrals

* `C3P_shift`: no pole, with a decaying integrable majorant `g (Im s)` on the strip;
* `C3P_shift_pole`: one simple pole `p` inside the strip, `f = A / (s - p)`; the majorant is only
  required on the two lines and for `|Im s| ≥ 1`.

The pole computation follows `OAI.SevenEighths.PrincipalMellinResidues.verticalIntegral_simple_pole`
(copied and adapted). -/

set_option maxHeartbeats 1000000

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

lemma integrable_line_of_le {f : ℂ → ℂ} {g : ℝ → ℝ} {c : ℝ}
    (hc : ContinuousOn f {s | s.re = c}) (hg : Integrable g)
    (hb : ∀ t : ℝ, ‖f (c + t * I)‖ ≤ g t) :
    Integrable fun t : ℝ => f (c + t * I) := by
  refine hg.mono' ?_ (Eventually.of_forall hb)
  refine (hc.comp_continuous (by fun_prop) fun t => ?_).aestronglyMeasurable
  simp

lemma horizontal_tendsto {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atTop (𝓝 0)) (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → 1 ≤ T → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + T * I)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℝ => g T * |b - a|) atTop (𝓝 0) := by
    simpa using hg.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  exact hb x T hx.1.le hx.2 hT

lemma horizontal_tendsto_neg {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atBot (𝓝 0))
    (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → T ≤ -1 → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + (-T) * I)) atTop (𝓝 0) := by
  have hg' : Tendsto (fun T : ℝ => g (-T)) atTop (𝓝 0) := hg.comp tendsto_neg_atTop_atBot
  have hexp : Tendsto (fun T : ℝ => g (-T) * |b - a|) atTop (𝓝 0) := by
    simpa using hg'.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  have := hb x (-T) hx.1.le hx.2 (by linarith)
  simpa using this

/-- Shifting a vertical line integral across a strip on which `f` is holomorphic, given an
integrable majorant `g (Im s)` tending to `0` at `±∞`. -/
theorem C3P_shift {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {s | a ≤ s.re ∧ s.re ≤ b})
    (hg : Integrable g) (hgt : Tendsto g atTop (𝓝 0)) (hgb : Tendsto g atBot (𝓝 0))
    (hb : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g s.im) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  have hc : ∀ c, a ≤ c → c ≤ b → ContinuousOn f {s | s.re = c} := fun c h1 h2 =>
    hf.continuousOn.mono fun s hs => by simp only [Set.mem_ofPred_eq] at hs ⊢; constructor <;> linarith
  have hia := integrable_line_of_le (hc a le_rfl hab) hg fun t => by
    simpa using hb (a + t * I) (by simp) (by simp [hab])
  have hib := integrable_line_of_le (hc b hab le_rfl) hg fun t => by
    simpa using hb (b + t * I) (by simp [hab]) (by simp)
  have hrect : ∀ T : ℝ, (∫ x : ℝ in a..b, f (x + (-T) * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
      I • (∫ y : ℝ in -T..T, f (b + y * I)) - I • (∫ y : ℝ in -T..T, f (a + y * I)) = 0 := by
    intro T
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
      (hf.mono fun z hz => by
        rw [mem_reProdIm, Set.uIcc_of_le hab] at hz
        exact ⟨hz.1.1, hz.1.2⟩)
    simpa using this
  have hup := horizontal_tendsto (f := f) hab hgt fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hlow := horizontal_tendsto_neg (f := f) hab hgb fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (a + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (a + τ * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (b + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (b + τ * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h1 := ((hlow.sub hup).add ((hvb.const_smul I).sub (hva.const_smul I)))
  have h2 : Tendsto (fun T : ℝ => (0 : ℂ)) atTop
      (𝓝 ((0 - 0) + ((I • ∫ τ : ℝ, f (b + τ * I)) - I • ∫ τ : ℝ, f (a + τ * I)))) := by
    refine h1.congr fun T => ?_
    rw [← hrect T]
    ring
  have h3 := tendsto_nhds_unique tendsto_const_nhds h2
  simp only [sub_self, zero_add, smul_eq_mul] at h3
  rw [← mul_sub, eq_comm, mul_eq_zero, sub_eq_zero] at h3
  exact (h3.resolve_left I_ne_zero).symm

/-! ### A simple pole -/

end C3P

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Gamma: the Γ-kernel of the zero detector (8.6)–(8.7)

Generic pieces copied and adapted from the OpenAI 7/8 port
(`OAI.SevenEighths.GammaZeroDetector`, `GammaDetectorExpansion`, `CubicGammaExponential`):

* `gamma_rapid_bound`: `(1 + |Im z|)^n ‖Γ z‖ ≤ C` on `a ≤ Re z ≤ b`, `a > 0`;
* `literal_detector_bound`: for entire `f, g` with `f 0 = 0`, polynomial growth of `f` and a bound
  on `g` in `-1/4 ≤ Re z ≤ 2`, `‖∫ Y^z Γ(z) f(z) g(z)‖ ≤ π G A B Y^{-1/4}` on the line `Re z = 2`
  (the `v`-line moved to `Re v = -1/4`; the pole at `0` is cancelled by `f 0 = 0`);
* `gamma_expansion`: termwise Mellin inversion `(2π)⁻¹ ∫ Γ(v) x^{-v} = e^{-x}` for a Dirichlet
  series. The contour shift uses `C3P.C3P_shift`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L3Z

lemma norm_Gamma_le_real (z : ℂ) (hz : 0 < z.re) : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc a b, Real.Gamma x ≤ C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx => ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Gamma (z + n) = Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := real_Gamma_compact_bound (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

theorem gamma_rapid_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Gamma z‖ ≤ C₀ :=
      (norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza, hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

theorem gamma_differentiableAt_right {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma tendsto_inv_one_add_sq_atTop (C : ℝ) :
    Tendsto (fun t : ℝ => C * (1 + t ^ 2)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  simpa using (tendsto_inv_atTop_zero.comp h).const_mul C

lemma tendsto_inv_one_add_sq_atBot (C : ℝ) :
    Tendsto (fun t : ℝ => C * (1 + t ^ 2)⁻¹) atBot (𝓝 0) := by
  have := (tendsto_inv_one_add_sq_atTop C).comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def, neg_sq] using this

/-! ### Termwise Mellin inversion -/

noncomputable def line (t : ℝ) : ℂ := 2 + t * I

@[simp] theorem line_re (t : ℝ) : (line t).re = 2 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

theorem gamma_line_integrable : Integrable (fun t : ℝ => Gamma (line t)) := by
  obtain ⟨C, hC, hbound⟩ := gamma_rapid_bound 2 2 (by norm_num) 2
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    exact fun t => (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp
      (by unfold line; fun_prop)
  · filter_upwards [] with t
    have hb := hbound (line t) (by simp) (by simp)
    simp only [line_im] at hb
    have hp : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [norm_nonneg (Gamma (line t))]

theorem gamma_mellin_inverse {x : ℝ} (hx : 0 < x) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t : ℝ, (x : ℂ) ^ (-line t) * Gamma (line t)) = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (2 : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (GammaIntegral_convergent (by norm_num : 0 < (2 : ℂ).re))
  have hline (t : ℝ) : mellin f (line t) = Gamma (line t) := hm _ (by simp)
  have hv : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun t : ℝ => mellin f (line t))
    simpa only [hline] using gamma_line_integrable
  have hi := mellinInv_mellin_eq 2 f hx hf hv (by unfold f; fun_prop)
  change (1 / (2 * Real.pi)) • (∫ t : ℝ, (x : ℂ) ^ (-line t) • mellin f (line t)) = f x at hi
  simp_rw [hline] at hi
  simp only [smul_eq_mul, f, ofReal_exp, ofReal_neg] at hi
  convert hi using 1; simp [one_div, Complex.real_smul]

noncomputable def gammaTerm (a : ℂ) (N : ℝ) (ρ : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  (Y : ℂ) ^ (line t) * Gamma (line t) * a * (N : ℂ) ^ (-(ρ + line t))

theorem gammaTerm_separate (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    gammaTerm a N ρ Y t = (a * (N : ℂ) ^ (-ρ)) *
      (((N / Y : ℝ) : ℂ) ^ (-line t) * Gamma (line t)) := by
  rw [gammaTerm, neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hN.ne'),
    ofReal_div, div_cpow_ofReal_nonneg hN.le hY.le, cpow_neg (Y : ℂ), div_inv_eq_mul]
  ring

theorem gammaTerm_integral (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, gammaTerm a N ρ Y t) =
      a * (N : ℂ) ^ (-ρ) * Complex.exp (-(N : ℂ) / (Y : ℂ)) := by
  simp_rw [gammaTerm_separate a hN hY ρ]
  rw [integral_const_mul]
  calc
    _ = (a * (N : ℂ) ^ (-ρ)) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((N / Y : ℝ) : ℂ) ^ (-line t) * Gamma (line t)) := by ring
    _ = _ := by rw [gamma_mellin_inverse (div_pos hN hY)]; push_cast; rw [neg_div]

@[simp] theorem gammaTerm_zero (N : ℝ) (ρ : ℂ) (Y t : ℝ) : gammaTerm 0 N ρ Y t = 0 := by
  simp [gammaTerm]

theorem gammaTerm_norm (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    ‖gammaTerm a N ρ Y t‖ = (Y ^ 2 * (‖a‖ * N ^ (-(ρ.re + 2)))) * ‖Gamma (line t)‖ := by
  simp only [gammaTerm, norm_mul, norm_cpow_eq_rpow_re_of_pos hY,
    norm_cpow_eq_rpow_re_of_pos hN, neg_re, add_re, line_re, Real.rpow_two]
  ring

theorem gammaTerm_integrable (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    Integrable (gammaTerm a N ρ Y) := by
  apply (gamma_line_integrable.norm.const_mul (Y ^ 2 * (‖a‖ * N ^ (-(ρ.re + 2))))).mono'
  · apply Continuous.aestronglyMeasurable
    have hl : Continuous line := by unfold line; fun_prop
    have hg : Continuous (fun t : ℝ => Gamma (line t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp
        hl.continuousAt
    have hy := (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hY.ne'))).continuous.comp hl
    have hn := (((differentiable_const ρ).add differentiable_id).neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr hN.ne'))).continuous.comp hl
    exact ((hy.mul hg).mul continuous_const).mul hn
  · exact ae_of_all _ (fun t => (gammaTerm_norm a hN hY ρ t).le)

theorem gamma_expansion {ι : Type*} [Countable ι] (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 ≤ N i) (hzero : ∀ i, N i = 0 → a i = 0)
    (ρ : ℂ) {Y : ℝ} (hY : 0 < Y)
    (hsum : Summable (fun i => ‖a i‖ * (N i) ^ (-(ρ.re + 2)))) :
    HasSum (fun i => a i * (N i : ℂ) ^ (-ρ) * Complex.exp (-(N i : ℂ) / (Y : ℂ)))
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, ∑' i, gammaTerm (a i) (N i) ρ Y t) := by
  have hint (i : ι) : Integrable (gammaTerm (a i) (N i) ρ Y) := by
    by_cases hi : N i = 0
    · rw [hzero i hi]
      have he : gammaTerm 0 (N i) ρ Y = fun _ : ℝ => 0 := funext (gammaTerm_zero _ _ _)
      rw [he]
      exact integrable_zero ℝ ℂ volume
    · exact gammaTerm_integrable _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ
  have hnorm (i : ι) (t : ℝ) :
      ‖gammaTerm (a i) (N i) ρ Y t‖ =
        (Y ^ 2 * (‖a i‖ * (N i) ^ (-(ρ.re + 2)))) * ‖Gamma (line t)‖ := by
    by_cases hi : N i = 0
    · simp [hzero i hi]
    · exact gammaTerm_norm _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ t
  have hnormsum : Summable (fun i => ∫ t : ℝ, ‖gammaTerm (a i) (N i) ρ Y t‖) := by
    simp_rw [hnorm, integral_const_mul]
    have e : (fun i => Y ^ 2 * (‖a i‖ * N i ^ (-(ρ.re + 2))) * ∫ t : ℝ, ‖Gamma (line t)‖) =
        fun i => (Y ^ 2 * (∫ t : ℝ, ‖Gamma (line t)‖)) * (‖a i‖ * N i ^ (-(ρ.re + 2))) := by
      funext i; ring
    rw [e]
    exact hsum.mul_left _
  have hi := (hasSum_integral_of_summable_integral_norm hint hnormsum).mul_left
    (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have he (i : ι) : (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, gammaTerm (a i) (N i) ρ Y t) =
      a i * (N i : ℂ) ^ (-ρ) * Complex.exp (-(N i : ℂ) / (Y : ℂ)) := by
    by_cases hn : N i = 0
    · simp [hzero i hn]
    · exact gammaTerm_integral _ (lt_of_le_of_ne (hN i) (Ne.symm hn)) hY ρ
  simpa only [he] using hi

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3S_Mellin: the exponentially smoothed sum of a Dirichlet series with an entire continuation

If `D(s) = ∑ a_i N_i^{-s}` (absolutely convergent on `Re s = 2`) continues to an entire `Λ` with
`‖Λ z‖ ≤ K (1 + |Im z|)^n` on `δ ≤ Re z ≤ 2`, then `‖∑ a_i e^{-N_i/Y}‖ ≤ C K Y^δ` for `Y ≥ 1`, with `C`
depending only on `δ, n`. Mellin inversion of `Γ` (L3Z `gamma_expansion`) and a shift from `Re s = 2` to
`Re s = δ` (C3P `C3P_shift`). -/

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L3S

/-- The kernel `Y^z Γ(z) Λ(z)`. -/
noncomputable def kern (Λ : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ := (Y : ℂ) ^ z * Gamma z * Λ z

lemma kern_bound {δ : ℝ} (n : ℕ) {G : ℝ}
    (hgam : ∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → (1 + |z.im|) ^ (n + 2) * ‖Gamma z‖ ≤ G)
    {Λ : ℂ → ℂ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → ‖Λ z‖ ≤ K * (1 + |z.im|) ^ n) {Y : ℝ} (hY : 0 < Y)
    (z : ℂ) (h1 : δ ≤ z.re) (h2 : z.re ≤ 2) :
    ‖kern Λ Y z‖ ≤ Y ^ z.re * (G * K) * (1 + z.im ^ 2)⁻¹ := by
  have hpos : 0 < 1 + z.im ^ 2 := by positivity
  have hb : (1 + z.im ^ 2) * (‖Gamma z‖ * ‖Λ z‖) ≤ G * K := by
    have hsq : 1 + z.im ^ 2 ≤ (1 + |z.im|) ^ 2 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
    calc (1 + z.im ^ 2) * (‖Gamma z‖ * ‖Λ z‖)
        ≤ (1 + |z.im|) ^ 2 * (‖Gamma z‖ * (K * (1 + |z.im|) ^ n)) := by
          gcongr
          exact hK z h1 h2
      _ = K * ((1 + |z.im|) ^ (n + 2) * ‖Gamma z‖) := by ring
      _ ≤ K * G := mul_le_mul_of_nonneg_left (hgam z h1 h2) hK0
      _ = G * K := by ring
  unfold kern
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have : ‖Gamma z‖ * ‖Λ z‖ ≤ (G * K) * (1 + z.im ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith
  calc Y ^ z.re * ‖Gamma z‖ * ‖Λ z‖ = Y ^ z.re * (‖Gamma z‖ * ‖Λ z‖) := by ring
    _ ≤ Y ^ z.re * ((G * K) * (1 + z.im ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem smoothed_bound {ι : Type*} [Countable ι] {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ι → ℂ) (Nf : ι → ℝ), (∀ i, 0 ≤ Nf i) → (∀ i, Nf i = 0 → a i = 0) →
      Summable (fun i => ‖a i‖ * Nf i ^ (-(2 : ℝ))) →
      ∀ Λ : ℂ → ℂ, Differentiable ℂ Λ →
        (∀ s : ℂ, 1 < s.re → Λ s = ∑' i, a i * (Nf i : ℂ) ^ (-s)) →
        ∀ K : ℝ, 0 ≤ K → (∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → ‖Λ z‖ ≤ K * (1 + |z.im|) ^ n) →
        ∀ Y : ℝ, 1 ≤ Y →
          ‖∑' i, a i * Complex.exp (-(Nf i : ℂ) / (Y : ℂ))‖ ≤ C * K * Y ^ δ := by
  obtain ⟨G, hG, hgam⟩ := L3Z.gamma_rapid_bound δ 2 hδ (n + 2)
  refine ⟨G / 2, by positivity, ?_⟩
  intro a Nf hN hzero hsum Λ hΛ hΛeq K hK0 hK Y hY
  have hY0 : 0 < Y := by linarith
  have hexp := L3Z.gamma_expansion a Nf hN hzero 0 hY0 (by simpa using hsum)
  simp only [neg_zero, Complex.cpow_zero, mul_one] at hexp
  -- the integrand on `Re = 2`
  have hint : ∀ t : ℝ, ∑' i, L3Z.gammaTerm (a i) (Nf i) 0 Y t = kern Λ Y (L3Z.line t) := by
    intro t
    have hre : 1 < (L3Z.line t).re := by simp
    unfold L3Z.gammaTerm kern
    rw [hΛeq _ hre, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [zero_add]; ring
  simp_rw [hint] at hexp
  rw [hexp.tsum_eq]
  -- the shift
  have hshift : (∫ t : ℝ, kern Λ Y ((δ : ℂ) + t * I)) = ∫ t : ℝ, kern Λ Y ((2 : ℝ) + t * I) := by
    refine C3P.C3P_shift (g := fun t => (Y ^ (2 : ℝ) * (G * K)) * (1 + t ^ 2)⁻¹) hδ2 ?_
      (integrable_inv_one_add_sq.const_mul _) (L3Z.tendsto_inv_one_add_sq_atTop _)
      (L3Z.tendsto_inv_one_add_sq_atBot _) ?_
    · intro z hz
      have hz0 : 0 < z.re := hδ.trans_le hz.1
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold kern
      refine ((DifferentiableAt.const_cpow differentiableAt_id
        (Or.inl (Complex.ofReal_ne_zero.2 hY0.ne'))).mul
        (L3Z.gamma_differentiableAt_right hz0)).mul (hΛ z)
    · intro s h1 h2
      refine (kern_bound n hgam hK0 hK hY0 s h1 h2).trans ?_
      gcongr
  have hline : (fun t : ℝ => kern Λ Y (L3Z.line t)) = fun t : ℝ => kern Λ Y ((2 : ℝ) + t * I) := by
    funext t; unfold L3Z.line; push_cast; rfl
  rw [hline, ← hshift, norm_mul]
  have hnorm : ‖∫ t : ℝ, kern Λ Y ((δ : ℂ) + t * I)‖ ≤ ∫ t : ℝ, (Y ^ δ * (G * K)) * (1 + t ^ 2)⁻¹ := by
    refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
      (ae_of_all _ fun t => ?_)
    have := kern_bound n hgam hK0 hK hY0 ((δ : ℂ) + t * I) (by simp) (by simp [hδ2])
    simpa using this
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hnorm
  have hpi : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hpi]
  calc (2 * Real.pi)⁻¹ * ‖∫ t : ℝ, kern Λ Y ((δ : ℂ) + t * I)‖
      ≤ (2 * Real.pi)⁻¹ * (Y ^ δ * (G * K) * Real.pi) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = G / 2 * K * Y ^ δ := by field_simp

end L3S

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_le_one (hv : v ∉ placesOf 𝔪) (r : SInt 𝔪) : v.valuation F (r : F) ≤ 1 := r.2 v hv

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

/-- Elements of `v^j R` have valuation at most `exp(-j)`. -/
lemma val_le_of_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) {r : SInt 𝔪}
    (hr : r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (r : F) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.map] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_alg, val_alg]
    exact (v.intValuation_le_pow_iff_mem a j).2 ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * exp (-(j : ℤ)) :=
          mul_le_mul' (val_le_one hv a) hx
      _ = _ := one_mul _

/-- An element of `𝓞` not in `v` has an inverse modulo `v^j`. -/
lemma exists_mul_sub_one_mem (j : ℕ) {d : 𝓞 F} (hd : d ∉ v.asIdeal) :
    ∃ c : 𝓞 F, c * d - 1 ∈ v.asIdeal ^ j := by
  have h1 : IsCoprime v.asIdeal (Ideal.span {d}) := by
    obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hd
    exact Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * d, Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self d), by rw [add_comm]; exact hyi⟩
  obtain ⟨i, hi, x, hx, hix⟩ := (h1.pow_left (m := j)).exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨c, ?_⟩
  have : c * d - 1 = -i := by linear_combination hix
  rw [this]
  exact neg_mem hi

/-- Every `x ∈ F` with `v(x) ≤ 1` is congruent modulo `v^j` (in valuation) to an element of `𝓞`. -/
lemma exists_val_sub_le (j : ℕ) (x : F) (hx : v.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, v.valuation F (x - algebraMap (𝓞 F) F a) ≤ exp (-(j : ℤ)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) x hx
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  refine ⟨c * n, ?_⟩
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have heq : x - algebraMap (𝓞 F) F (c * n) =
      -(x * algebraMap (𝓞 F) F (c * d - 1)) := by
    have hnd' : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
    rw [map_mul, ← hnd', map_sub, map_mul, map_one]; ring
  rw [heq, Valuation.map_neg, map_mul, val_alg]
  calc v.valuation F x * v.intValuation (c * d - 1) ≤ 1 * exp (-(j : ℤ)) :=
        mul_le_mul' hx ((v.intValuation_le_pow_iff_mem _ j).2 hc)
    _ = _ := one_mul _

/-- Elements of `R` of valuation at most `exp(-j)` lie in `v^j R`. -/
lemma mem_of_val_le (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : v.valuation F (r : F) ≤ exp (-(j : ℤ))) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hv)
  have hnd' : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have hn : n ∈ v.asIdeal ^ j := by
    rw [← v.intValuation_le_pow_iff_mem, ← val_alg (v := v), ← hnd', map_mul, hvd, mul_one]
    exact h
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  have heq : r = algebraMap (𝓞 F) (SInt 𝔪) (c * n) -
      r * algebraMap (𝓞 F) (SInt 𝔪) (c * d - 1) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg, coe_alg, map_mul, map_sub, map_mul,
      map_one, ← hnd']
    ring
  rw [heq]
  exact sub_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hn))
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc))

lemma mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      v.valuation F (r : F) ≤ exp (-(j : ℤ)) :=
  ⟨val_le_of_mem hv j, mem_of_val_le hv j r⟩

lemma alg_mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      a ∈ v.asIdeal ^ j := by
  rw [mem_map_pow_iff hv, coe_alg, val_alg, v.intValuation_le_pow_iff_mem]

lemma exists_sub_mem_map_pow (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈
      (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j (r : F) (r.2 v hv)
  exact ⟨a, mem_of_val_le hv j _ (by rw [Subalgebra.coe_sub, coe_alg]; exact ha)⟩

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

lemma quotHom_bijective (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Function.Bijective (quotHom 𝔪 (v.asIdeal ^ j)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, alg_mem_map_pow_iff hv] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow hv j r
    exact ⟨Ideal.Quotient.mk _ a, by rw [quotHom_mk]; exact (Ideal.Quotient.eq.mpr ha).symm⟩

/-- `𝓞/v^j ≃+* R/v^j R`. -/
noncomputable def quotEquiv (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    𝓞 F ⧸ v.asIdeal ^ j ≃+* SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  RingEquiv.ofBijective _ (quotHom_bijective hv j)

lemma finite_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Finite (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ v.asIdeal ^ j) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ (quotEquiv hv j).toEquiv

lemma natCard_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Nat.card (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal ^ j := by
  rw [← Nat.card_congr (quotEquiv hv j).toEquiv, ← map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- `v R` is a maximal ideal of `R`. -/
lemma isMaximal_map (hv : v ∉ placesOf 𝔪) :
    (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := by
  have e := quotEquiv (𝔪 := 𝔪) hv 1
  rw [pow_one] at e
  apply Ideal.Quotient.maximal_of_isField
  have : (v.asIdeal).IsMaximal := v.isMaximal
  have hf : IsField (𝓞 F ⧸ v.asIdeal) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp this
  exact MulEquiv.isField hf e.symm.toMulEquiv

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {v : HeightOneSpectrum (𝓞 F)}

lemma absNorm_ne_one (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

lemma quotHom_bijective_one (h : v ∉ placesOf 𝔪) :
    Function.Bijective (quotHom 𝔪 v.asIdeal) := by
  have := quotHom_bijective (𝔪 := 𝔪) h 1
  rwa [pow_one] at this

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

/-- Choice-free value of a root of unity: if `f ζ = f ω ^ i` then `ι ζ = ι ω ^ i`. -/
lemma iota_eq_pow_of_map {K : Type*} [CommRing K] [IsDomain K] (f : 𝓞 F →+* K) {m : ℕ}
    (hm : 0 < m) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω m) (hωf : IsPrimitiveRoot (f ω) m)
    {ζ : 𝓞 F} (hζ : ζ ^ m = 1) {i : ℕ} (h : f ζ = f ω ^ i) : ι (ζ : F) = ι (ω : F) ^ i := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one hζ
  have hpow : ∀ (z : K) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have hpowC : ∀ (z : ℂ) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have h1 : f ω ^ j = f ω ^ (i % m) := by
    rw [← map_pow, h, hpow _ hωf.pow_eq_one]
  have hji : j = i % m := hωf.pow_inj hj (Nat.mod_lt _ hm) h1
  have hιω : ι (ω : F) ^ m = 1 := by
    rw [← map_pow, ← map_pow (algebraMap (𝓞 F) F), hω.pow_eq_one, map_one, map_one]
  rw [show ((ω ^ j : 𝓞 F) : F) = (ω : F) ^ j from map_pow (algebraMap (𝓞 F) F) ω j, map_pow, hji,
    ← hpowC _ hιω]

end roots

section chi

/-- The function underlying `sexticResidueSymbol` on `L = R / P R`. -/
noncomputable def sexFun (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ := by
  classical
  exact if y = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
    then ι (h.choose : F) else 0

lemma sexticResidueSymbol_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x =
      sexFun ι 𝔪 v (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) x) := by
  unfold sexticResidueSymbol sexFun
  congr 1

variable {ι : F →+* ℂ}

/-- The image of `ω` in `L`. -/
noncomputable abbrev omegaL (ω : 𝓞 F) : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) ω)

lemma sexFun_zero : sexFun ι 𝔪 v (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  classical
  unfold sexFun; rw [if_pos rfl]

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

theorem map_equiv_symm_map (f : R ≃+* S) (I : Ideal R) : (I.map f).map f.symm = I := by
  ext x
  rw [mem_map_equiv, RingEquiv.symm_symm, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem map_equiv_coe (f : R ≃+* S) (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

omit [NumberField F] [NumberField F'] in
theorem mapRingEquiv_symm (e : F ≃+* F') :
    RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
  ext x; rfl

/-- `S`-integrality transports along `e`. -/
theorem mem_integer_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) :
    e x ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).integer F' := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro v' hv'
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v'.asIdeal.comap (eO : 𝓞 F →+* 𝓞 F')
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply v'.ne_bot
        rw [← Ideal.map_comap_of_surjective (eO : 𝓞 F →+* 𝓞 F') eO.surjective v'.asIdeal, h,
          Ideal.map_bot] }
  have hv : v ∉ placesOf 𝔪 := by
    intro h
    apply hv'
    change 𝔪.map eO ≤ v'.asIdeal
    rw [← map_equiv_coe]
    exact Ideal.map_le_iff_le_comap.2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x (hx v hv)
  have hd : eO d ∉ v'.asIdeal := d.2
  have hnd' : e x * algebraMap (𝓞 F') F' (eO d) = algebraMap (𝓞 F') F' (eO n) := by
    have := congrArg e hnd
    rw [map_mul] at this
    exact this
  have h1 : v'.valuation F' (algebraMap (𝓞 F') F' (eO d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h2 : v'.valuation F' (algebraMap (𝓞 F') F' (eO n)) ≤ 1 := v'.valuation_le_one _
  rw [← hnd', map_mul, h1, mul_one] at h2
  exact h2

/-- The ring `R = 𝓞_S` transports along `e`. -/
def sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    SInt 𝔪 ≃+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun x := ⟨e x, mem_integer_map e 𝔪 x x.2⟩
  invFun y := ⟨e.symm y, by
    have := mem_integer_map e.symm (𝔪.map (RingOfIntegers.mapRingEquiv e)) y y.2
    rwa [mapRingEquiv_symm, map_equiv_symm_map] at this⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[simp] theorem sIntEquiv_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ((sIntEquiv e 𝔪 x : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') = e x := rfl

@[simp] theorem sIntEquiv_symm_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F))
    (y : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    (((sIntEquiv e 𝔪).symm y : SInt 𝔪) : F) = e.symm y := rfl

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

/-! ### `AllowedGen` transports -/

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3S_Sym: the pair character `conj χ_I(x) χ_I(y) = χ_I(x⁵ y)` on exterior ideals

* `sext_conj`, `rs_conj`: `conj χ_P(x) = χ_P(x)^5` (the values are `0` or sixth roots of unity);
* `sext_mul`: `χ_P(xy) = χ_P(x) χ_P(y)` at an exterior prime `P ∌ 6` (C3I's `chi` construction with
  `6 ∣ N P − 1` in place of `12 ∣ N P − 1` and without the different condition);
* `rs_pair`: for `I` exterior, all of whose primes avoid `6`, `conj χ_I(x) χ_I(y) = χ_I(x⁵ y)`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (ι : F →+* ℂ)

lemma conj_eq_pow_five {z : ℂ} (hz : z = 0 ∨ z ^ 6 = 1) : starRingEnd ℂ z = z ^ 5 := by
  rcases hz with rfl | h6
  · simp
  · have h1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)
    have h2 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj', h1]; simp
    calc starRingEnd ℂ z = starRingEnd ℂ z * z ^ 6 := by rw [h6, mul_one]
      _ = (z * starRingEnd ℂ z) * z ^ 5 := by ring
      _ = z ^ 5 := by rw [h2, one_mul]

lemma sext_cases (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 P x = 0 ∨ sexticResidueSymbol ι 𝔪 P x ^ 6 = 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · exact Or.inl rfl
  · right
    rw [← map_pow, ← map_pow]
    have := h2.choose_spec.1
    rw [this]; simp
  · exact Or.inl rfl

lemma sext_conj (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P x) = sexticResidueSymbol ι 𝔪 P x ^ 5 :=
  conj_eq_pow_five (sext_cases ι P x)

lemma rs_conj (I : Ideal (𝓞 F)) (x : SInt 𝔪) :
    starRingEnd ℂ (residueSymbol ι 𝔪 I x) = residueSymbol ι 𝔪 I x ^ 5 := by
  unfold residueSymbol
  rw [map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_pow]
  congr 1
  exact Multiset.map_congr rfl fun P _ => sext_conj ι P x

section mul

variable {v : HeightOneSpectrum (𝓞 F)}

lemma omegaL_prim' (hv : v ∉ placesOf 𝔪) (hcop : (Ideal.absNorm v.asIdeal).Coprime 6)
    {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (C3I.omegaL (𝔪 := 𝔪) (v := v) ω) 6 := by
  have h1 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
    hω.idealQuotient_mk (C3I.absNorm_ne_one v) hcop
  exact h1.map_of_injective (C3I.quotHom_bijective_one (𝔪 := 𝔪) hv).1

lemma pow_card_sub_one_L' (hv : v ∉ placesOf 𝔪)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    y ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  haveI := C3I.isMaximal_map (𝔪 := 𝔪) hv
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    have := C3I.finite_quot (𝔪 := 𝔪) hv 1
    rwa [pow_one] at this
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hc : Nat.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal := by
    have := C3I.natCard_quot (𝔪 := 𝔪) hv 1
    rwa [pow_one, pow_one] at this
  rw [← hc, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one y hy

lemma exists_pow_e' (hv : v ∉ placesOf 𝔪) (h6N : 6 ∣ Ideal.absNorm v.asIdeal - 1)
    (hcop : (Ideal.absNorm v.asIdeal).Coprime 6) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ∃ i : ℕ, i < 6 ∧ y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = C3I.omegaL ω ^ i := by
  haveI := C3I.isMaximal_map (𝔪 := 𝔪) hv
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h6 : (y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, Nat.mul_div_cancel' h6N, pow_card_sub_one_L' hv hy]
  obtain ⟨i, hi, hi'⟩ := (omegaL_prim' hv hcop hω).eq_pow_of_pow_eq_one h6
  exact ⟨i, hi, hi'.symm⟩

lemma sexFun_eq_pow' (hv : v ∉ placesOf 𝔪) (hcop : (Ideal.absNorm v.asIdeal).Coprime 6)
    {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = C3I.omegaL ω ^ i) :
    C3I.sexFun ι 𝔪 v y = ι (ω : F) ^ i := by
  haveI := C3I.isMaximal_map (𝔪 := 𝔪) hv
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) :=
    ⟨ω ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
      rw [map_pow, map_pow, hi]⟩
  classical
  unfold C3I.sexFun
  rw [if_neg hy, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set f : 𝓞 F →+* SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (SInt 𝔪))
  exact C3I.iota_eq_pow_of_map ι f (by norm_num) hω (omegaL_prim' hv hcop hω) h1 (by
    change Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) hex.choose) = C3I.omegaL ω ^ i
    rw [h2, hi])

/-- `6 ∣ N P − 1` at a prime `P ∌ 6` when `F` contains a primitive sixth root of unity. -/
lemma six_dvd_absNorm_sub_one {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (v : HeightOneSpectrum (𝓞 F))
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) : 6 ∣ Ideal.absNorm v.asIdeal - 1 := by
  classical
  set P := v.asIdeal
  letI : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P v.ne_bot
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hinj : ∀ a b : 𝓞 F, a ^ 6 = 1 → b ^ 6 = 1 →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := fun a b ha hb h =>
    C0R.eq_of_pow_six P h6 ha hb (Ideal.Quotient.eq.mp h)
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk P ω) 6 := by
    refine ⟨by rw [← map_pow, hω.pow_eq_one, map_one], fun l hl => ?_⟩
    have : ω ^ l = 1 := hinj _ _ (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow])
      (one_pow 6) (by rw [map_pow, hl, map_one])
    exact hω.dvd_of_pow_eq_one l this
  have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk P ω) (hη.ne_zero (by norm_num))
  rw [hcard] at this
  exact hη.dvd_of_pow_eq_one _ this

lemma coprime_six_of_dvd (v : HeightOneSpectrum (𝓞 F)) (h : 6 ∣ Ideal.absNorm v.asIdeal - 1) :
    (Ideal.absNorm v.asIdeal).Coprime 6 := by
  have h1 := C3I.absNorm_pos v
  obtain ⟨k, hk⟩ := h
  have : Ideal.absNorm v.asIdeal = 6 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (6 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

/-- `χ_P` as a multiplicative character of `R / P R`, at an exterior prime `P ∌ 6`. -/
noncomputable def chi' {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (hv : v ∉ placesOf 𝔪)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) :
    MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun := C3I.sexFun ι 𝔪 v
  map_one' := by
    have h6N := six_dvd_absNorm_sub_one hω v h6
    have h10 : (1 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 0 := fun h =>
      (C3I.isMaximal_map (𝔪 := 𝔪) hv).ne_top
        ((Ideal.eq_top_iff_one _).2 (Ideal.Quotient.eq_zero_iff_mem.1 h))
    rw [sexFun_eq_pow' ι hv (coprime_six_of_dvd v h6N) hω h10 (i := 0)
      (by rw [one_pow, pow_zero])]
    simp
  map_mul' := by
    have h6N := six_dvd_absNorm_sub_one hω v h6
    have hcop := coprime_six_of_dvd v h6N
    haveI := C3I.isMaximal_map (𝔪 := 𝔪) hv
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro x y
    by_cases hx : x = 0
    · simp [hx, C3I.sexFun_zero]
    by_cases hy : y = 0
    · simp [hy, C3I.sexFun_zero]
    obtain ⟨i, -, hi⟩ := exists_pow_e' hv h6N hcop hω hx
    obtain ⟨j, -, hj⟩ := exists_pow_e' hv h6N hcop hω hy
    rw [sexFun_eq_pow' ι hv hcop hω hx hi, sexFun_eq_pow' ι hv hcop hω hy hj,
      sexFun_eq_pow' ι hv hcop hω (mul_ne_zero hx hy) (i := i + j) (by rw [mul_pow, hi, hj, pow_add]),
      pow_add]
  map_nonunit' := by
    haveI := C3I.isMaximal_map (𝔪 := 𝔪) hv
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro a ha
    have : a = 0 := by
      by_contra h'
      exact ha (Ne.isUnit h')
    rw [this]; exact C3I.sexFun_zero

lemma chi'_mk {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (hv : v ∉ placesOf 𝔪)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (x : SInt 𝔪) :
    chi' ι hω hv h6 (Ideal.Quotient.mk _ x) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
  (C3I.sexticResidueSymbol_eq ι 𝔪 v x).symm

/-- **Multiplicativity** of `χ_P` at an exterior prime `P ∌ 6`. -/
theorem sext_mul {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (hv : v ∉ placesOf 𝔪)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (x y : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (x * y) =
      sexticResidueSymbol ι 𝔪 v.asIdeal x * sexticResidueSymbol ι 𝔪 v.asIdeal y := by
  rw [← chi'_mk ι hω hv h6, ← chi'_mk ι hω hv h6, ← chi'_mk ι hω hv h6, map_mul, map_mul]

theorem sext_pow {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (hv : v ∉ placesOf 𝔪)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (x : SInt 𝔪) (k : ℕ) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (x ^ k) = sexticResidueSymbol ι 𝔪 v.asIdeal x ^ k := by
  rw [← chi'_mk ι hω hv h6, ← chi'_mk ι hω hv h6, map_pow, map_pow]

end mul

/-- **The pair character.** -/
theorem rs_pair {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → (6 : 𝓞 F) ∉ P)
    {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (x y : SInt 𝔪) :
    starRingEnd ℂ (residueSymbol ι 𝔪 I x) * residueSymbol ι 𝔪 I y =
      residueSymbol ι 𝔪 I (x ^ 5 * y) := by
  rw [rs_conj]
  unfold residueSymbol
  rw [← Multiset.prod_map_pow, ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  have hPp : Prime P := prime_of_normalized_factor P hP
  have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
  have hPI : I ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
  have hPi : P.IsPrime := (Ideal.prime_iff_isPrime hP0).1 hPp
  have hPE : IsExterior 𝔪 P := ⟨hP0, eq_top_iff.2 (hI.2 ▸ sup_le_sup_right hPI 𝔪)⟩
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPi, hP0⟩
  have hv : v ∉ placesOf 𝔪 := fun hm => hPi.ne_top (eq_top_iff.2 (hPE.2 ▸ sup_le le_rfl hm))
  have h6v : (6 : 𝓞 F) ∉ v.asIdeal := h6 P hPi hPE
  change sexticResidueSymbol ι 𝔪 v.asIdeal x ^ 5 * sexticResidueSymbol ι 𝔪 v.asIdeal y =
    sexticResidueSymbol ι 𝔪 v.asIdeal (x ^ 5 * y)
  rw [sext_mul ι hω hv h6v, sext_pow ι hω hv h6v]

end L3S

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3K_Val: valuations of a generator `u` of `𝔲 R` at exterior primes

For `u ∈ R = SInt 𝔪` with `u R = 𝔲 R` and an exterior prime `v`: `v(u) = e^{−e}` where
`𝔲 ≤ v^e`, `𝔲 ≰ v^{e+1}`. Hence `v(u) = 1` if `v ∤ 𝔲`, and `v(u)` is not an even sixth power of
`e^{±1}` when `v ∣ 𝔲` and `𝔲` is sixth-power-free. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma sInt_val_le_one' (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

lemma coe_algebraMap_sInt' (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

lemma val_algebraMap_le (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} {e : ℕ} (hx : x ∈ v.asIdeal ^ e) :
    v.valuation F (algebraMap (𝓞 F) F x) ≤ exp (-(e : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x e).2 hx

lemma val_le_of_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) : v.valuation F (u : F) ≤ exp (-(e : ℤ)) := by
  have hmem : u ∈ 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hu]; exact Ideal.mem_span_singleton_self u
  clear hu
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [coe_algebraMap_sInt']
    exact val_algebraMap_le v (he hy)
  | zero => simp
  | add x y _ _ hx hy =>
    have : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
    rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    have : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [this, map_mul]
    calc v.valuation F (r : F) * v.valuation F (x : F) ≤ 1 * exp (-(e : ℤ)) :=
          mul_le_mul' (sInt_val_le_one' r v hv) hx
      _ = _ := one_mul _

lemma lt_val_of_not_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {n : ℕ}
    (hn : ¬ 𝔲 ≤ v.asIdeal ^ n) : exp (-(n : ℤ)) < v.valuation F (u : F) := by
  obtain ⟨x, hx𝔲, hxn⟩ := SetLike.not_le_iff_exists.1 hn
  have hx : algebraMap (𝓞 F) (SInt 𝔪) x ∈ Ideal.span {u} := by
    rw [hu]; exact Ideal.mem_map_of_mem _ hx𝔲
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : exp (-(n : ℤ)) < v.valuation F (algebraMap (𝓞 F) F x) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    by_contra h; push Not at h
    exact hxn ((v.intValuation_le_pow_iff_mem x n).1 h)
  have h2 : algebraMap (𝓞 F) F x = (r : F) * (u : F) := by
    rw [← coe_algebraMap_sInt', ← hr]; rfl
  rw [h2, map_mul] at h1
  calc exp (-(n : ℤ)) < v.valuation F (r : F) * v.valuation F (u : F) := h1
    _ ≤ 1 * v.valuation F (u : F) := mul_le_mul' (sInt_val_le_one' r v hv) le_rfl
    _ = _ := one_mul _

/-- `v(u) = e^{−e}` when `𝔲 ≤ v^e` and `𝔲 ≰ v^{e+1}`. -/
lemma val_eq_exp (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) (he1 : ¬ 𝔲 ≤ v.asIdeal ^ (e + 1)) :
    v.valuation F (u : F) = exp (-(e : ℤ)) := by
  have hle := val_le_of_le v hv hu he
  have hlt := lt_val_of_not_le v hv hu he1
  have hne : v.valuation F (u : F) ≠ 0 := ne_of_gt ((zero_lt_iff.2 (exp_ne_zero)).trans hlt)
  rw [← exp_log hne] at hle hlt ⊢
  rw [exp_le_exp] at hle
  rw [exp_lt_exp] at hlt
  congr 1
  push_cast at hlt
  omega

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Freq: a nonprincipal frequency element is not a sixth power

* `span_freqElt`: `u R = 𝔲 R` for `u = freqElt g r`, `𝔲 = r.1.1`;
* `freqElt_ne_pow_six`: for `r ≠ principalFreq`, `u ∉ F^{×6}` (`𝔲 ≠ ⊤`: an exterior valuation of `u`
  lies in `1..5`; `𝔲 = ⊤`: `u = rep(ε) gen ⊤` with `gen ⊤ ∈ U_S^6` and `ε ≠ 1`). -/

set_option autoImplicit false

open NumberField IsDedekindDomain WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma isUnit_rep (ε : SClass 𝔪) : IsUnit (SClass.rep ε) :=
  Units.isUnit _

lemma span_freqElt (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪) :
    Ideal.span {freqElt g r} = r.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [freqElt, Ideal.span_singleton_mul_left_unit (isUnit_rep r.2), g.span_gen _ r.1.2.1]

lemma rep_coe (ε : SClass 𝔪) :
    ((SClass.rep ε : SInt 𝔪) : F) =
      (((Function.surjInv QuotientGroup.mk_surjective ε : SUnit 𝔪) : Fˣ) : F) := rfl

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3S_Dist: distinct rows give distinct row characters

For frequency classes `r ≠ r'`, `u_r⁵ u_r'` is not a sixth power in `F` (the distinctness of the `ω_u` of
p. 51): if it were, then at each exterior prime the orders `e, e' ∈ {0, …, 5}` of `u, u'` satisfy
`e ≡ e' (mod 6)`, so `𝔲 = 𝔲'`; then the `S`-unit parts agree modulo `U_S⁶`. -/

set_option autoImplicit false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3S

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The order of `u` at an exterior prime: `v(u) = e^{-e}`, `e ≤ 5`, `e = count v 𝔲`. -/
lemma ord_spec (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    (h6 : IsSixthPowerFree 𝔲) {u : SInt 𝔪}
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ e : ℕ, e ≤ 5 ∧ v.valuation F (u : F) = exp (-(e : ℤ)) ∧
      (normalizedFactors 𝔲).count v.asIdeal = e := by
  classical
  have hex : ∃ n, ¬ 𝔲 ≤ v.asIdeal ^ n := by
    refine ⟨6, fun hle => ?_⟩
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  set n₀ := Nat.find hex
  have hn₀ : ¬ 𝔲 ≤ v.asIdeal ^ n₀ := Nat.find_spec hex
  have hn₀6 : n₀ ≤ 6 := Nat.find_min' hex (fun hle => by
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this))
  have hn₀1 : 1 ≤ n₀ := by
    by_contra hlt; push Not at hlt
    interval_cases hn : n₀
    exact hn₀ (by simp)
  have he : 𝔲 ≤ v.asIdeal ^ (n₀ - 1) := by
    by_contra hc
    exact Nat.find_min hex (by omega : n₀ - 1 < n₀) hc
  have he1 : ¬ 𝔲 ≤ v.asIdeal ^ (n₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hn₀1]
  have := v.isPrime
  exact ⟨n₀ - 1, by omega, L3K.val_eq_exp v hv hu he he1,
    Ideal.count_normalizedFactors_eq he he1⟩

lemma coe_ne_zero_of_span {u : SInt 𝔪} {𝔲 : Ideal (𝓞 F)} (h𝔲 : 𝔲 ≠ ⊥)
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) : (u : F) ≠ 0 := by
  intro h0
  have : u = 0 := Subtype.ext h0
  rw [this, Ideal.span_singleton_eq_bot.2 rfl] at hu
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔲
  have hxm : algebraMap (𝓞 F) (SInt 𝔪) x ∈ 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ hx
  rw [← hu, Ideal.mem_bot] at hxm
  apply hx0
  have := congrArg (fun z : SInt 𝔪 => (z : F)) hxm
  simpa using this

/-- Exterior sixth-power-free ideals with `u⁵ u' ∈ F^{×6}` are equal. -/
lemma ideal_eq_of_pow_six {𝔲 𝔲' : Ideal (𝓞 F)} (hE : IsExterior 𝔪 𝔲) (hE' : IsExterior 𝔪 𝔲')
    (h6 : IsSixthPowerFree 𝔲) (h6' : IsSixthPowerFree 𝔲') {u u' : SInt 𝔪}
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hu' : Ideal.span {u'} = 𝔲'.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {b : F} (hb : b ^ 6 = (u : F) ^ 5 * (u' : F)) : 𝔲 = 𝔲' := by
  classical
  have hu0 := coe_ne_zero_of_span hE.1 hu
  have hu0' := coe_ne_zero_of_span hE'.1 hu'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hb
    exact mul_ne_zero (pow_ne_zero 5 hu0) hu0' hb.symm
  -- every prime factor of an exterior ideal is an exterior height-one prime
  have hfac : ∀ {I : Ideal (𝓞 F)}, IsExterior 𝔪 I → ∀ P ∈ normalizedFactors I,
      ∃ v : HeightOneSpectrum (𝓞 F), v.asIdeal = P ∧ ¬ 𝔪 ≤ v.asIdeal := by
    intro I hI P hP
    have hPp : Prime P := prime_of_normalized_factor P hP
    have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
    have hPI : I ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
    have hPi : P.IsPrime := (Ideal.prime_iff_isPrime hP0).1 hPp
    refine ⟨⟨P, hPi, hP0⟩, rfl, fun hm => hPi.ne_top ?_⟩
    rw [eq_top_iff, ← hI.2]; exact sup_le hPI hm
  have hcount : ∀ P, (normalizedFactors 𝔲).count P = (normalizedFactors 𝔲').count P := by
    intro P
    by_cases hP : ∃ v : HeightOneSpectrum (𝓞 F), v.asIdeal = P ∧ ¬ 𝔪 ≤ v.asIdeal
    · obtain ⟨v, rfl, hv⟩ := hP
      obtain ⟨e, he5, hve, hce⟩ := ord_spec v hv h6 hu
      obtain ⟨e', he5', hve', hce'⟩ := ord_spec v hv h6' hu'
      rw [hce, hce']
      have hvb : v.valuation F b ≠ 0 := by simpa using hb0
      have := congrArg (v.valuation F) hb
      rw [map_pow, map_mul, map_pow, hve, hve', ← exp_log hvb, ← exp_nsmul, ← exp_nsmul,
        ← exp_add, exp_inj] at this
      simp only [nsmul_eq_mul] at this
      push_cast at this
      omega
    · have h1 : P ∉ normalizedFactors 𝔲 := fun hm => hP (hfac hE P hm)
      have h2 : P ∉ normalizedFactors 𝔲' := fun hm => hP (hfac hE' P hm)
      rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
  have hnf : normalizedFactors 𝔲 = normalizedFactors 𝔲' := Multiset.ext.2 hcount
  rw [← Ideal.prod_normalizedFactors_eq_self hE.1, ← Ideal.prod_normalizedFactors_eq_self hE'.1,
    hnf]

/-- **Distinct rows.** -/
theorem freqElt_pow_mul_ne_pow_six (g : AllowedGen ι 𝔪) {r r' : FreqClass 𝔪} (hrr : r ≠ r') :
    ∀ b : F, b ^ 6 ≠ ((freqElt g r ^ 5 * freqElt g r' : SInt 𝔪) : F) := by
  classical
  intro b hb
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow] at hb
  have h𝔲 : r.1.1 = r'.1.1 :=
    ideal_eq_of_pow_six r.1.2.1 r'.1.2.1 r.1.2.2 r'.1.2.2 (L3K.span_freqElt g r)
      (L3K.span_freqElt g r') hb
  apply hrr
  refine Prod.ext (Subtype.ext h𝔲) ?_
  -- the `S`-unit parts
  set w := Function.surjInv (QuotientGroup.mk_surjective
    (s := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) r.2
  set w' := Function.surjInv (QuotientGroup.mk_surjective
    (s := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) r'.2
  have hw : (w : SClass 𝔪) = r.2 := Function.surjInv_eq _ _
  have hw' : (w' : SClass 𝔪) = r'.2 := Function.surjInv_eq _ _
  have hu : (freqElt g r : F) = ((w : Fˣ) : F) * (g.gen r.1.1 : F) := by
    rw [freqElt, Subalgebra.coe_mul, L3K.rep_coe]
  have hu' : (freqElt g r' : F) = ((w' : Fˣ) : F) * (g.gen r.1.1 : F) := by
    rw [freqElt, Subalgebra.coe_mul, L3K.rep_coe, h𝔲]
  set G := (g.gen r.1.1 : F)
  have hG0 : G ≠ 0 := by
    have := coe_ne_zero_of_span r.1.2.1.1 (L3K.span_freqElt g r)
    rw [hu] at this
    exact right_ne_zero_of_mul this
  have hW0 : ((w : Fˣ) : F) ≠ 0 := (w : Fˣ).ne_zero
  set c : F := b / (G * ((w : Fˣ) : F))
  have hc : c ^ 6 = ((w' : Fˣ) : F) * ((w : Fˣ) : F)⁻¹ := by
    rw [hu, hu'] at hb
    simp only [c, div_pow, mul_pow, hb]
    field_simp
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, zero_pow (by norm_num)] at hc
    exact mul_ne_zero (w' : Fˣ).ne_zero (inv_ne_zero hW0) hc.symm
  have hcu : Units.mk0 c hc0 ∈ (placesOf 𝔪).unit F := by
    intro v hv
    have hw1 : v.valuation F (((w' : Fˣ) : F) * ((w : Fˣ) : F)⁻¹) = 1 := by
      rw [map_mul, map_inv₀, w'.2 v hv, w.2 v hv, inv_one, mul_one]
    rw [← hc, map_pow] at hw1
    have hne : v.valuation F c ≠ 0 := by simpa using hc0
    show v.valuation F c = 1
    rw [← exp_log hne] at hw1 ⊢
    rw [← exp_nsmul, ← exp_zero, exp_inj] at hw1
    rw [← exp_zero, exp_inj]
    simp at hw1; omega
  have hmem : w⁻¹ * w' ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range := by
    refine ⟨⟨Units.mk0 c hc0, hcu⟩, ?_⟩
    apply Subtype.ext; apply Units.ext
    simp [powMonoidHom_apply, hc, mul_comm]
  rw [← hw, ← hw']
  exact QuotientGroup.eq.2 hmem

end L3S

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3Z_Mob: Möbius sums over the ideals of `𝓞 F`

* `idealsUpTo R`: the nonzero ideals of norm `≤ R` (a `Finset`); `Countable (Ideal (𝓞 F))`;
* `sum_moebius_divisors`: `∑_{J ∣ I} μ(J) = [I = 1]` (after `IdealMobiusDivisorSum` of the 7/8
  port, generalized from `ℤ[ω]`);
* `alpha X n = ∑_{d ∣ n, q_d ≤ X} μ(d)`: the coefficients (8.5): `α(1) = 1`, `α(n) = 0` for
  `1 < q_n ≤ X`, and `|α(n)| ≤ 2^{ω(n)} ≪_δ q_n^δ`;
* `card_idealsUpTo_le`: Rankin's bound `#{q ≤ R} ≤ R^σ ∑ q^{-σ}`. -/

open NumberField UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] Classical.propDecidable

open Classical in
/-- The nonzero ideals of norm at most `R`. -/
noncomputable def idealsUpTo (F : Type*) [Field F] [NumberField F] (R : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊R⌋₊).subset
    (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ R} ⊆
        {I | Ideal.absNorm I ≤ ⌊R⌋₊} from fun I hI => Nat.le_floor hI.2)).toFinset

lemma mem_idealsUpTo {R : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ idealsUpTo F R ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ R := by
  simp [idealsUpTo]

instance countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I | Ideal.absNorm I ≤ n} := by
    ext I; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨_, le_rfl⟩
  have : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [h]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_le n).countable
  exact Set.countable_univ_iff.1 this

lemma absNorm_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : 0 < Ideal.absNorm I :=
  Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h))

/-- Rankin: `∑_{q_I ≤ R} f(I) ≤ R^σ ∑_I q_I^{-σ} f(I)`-type count, in the form
`#{q ≤ R} ≤ R^σ ∑' q^{-σ}`. -/
lemma card_idealsUpTo_le {σ : ℝ} (hσ : 0 ≤ σ) {R : ℝ} (hR : 0 ≤ R)
    (hs : Summable fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) :
    ((idealsUpTo F R).card : ℝ) ≤
      R ^ σ * ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  have h1 : ∀ I ∈ idealsUpTo F R, (1 : ℝ) ≤ R ^ σ * ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
    intro I hI
    rw [mem_idealsUpTo] at hI
    have hq : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast absNorm_pos hI.1
    rw [Real.rpow_neg hq.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    exact Real.rpow_le_rpow hq.le hI.2 hσ
  calc (∑ I ∈ idealsUpTo F R, (1 : ℝ)) ≤ ∑ I ∈ idealsUpTo F R,
        R ^ σ * ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := Finset.sum_le_sum h1
    _ = R ^ σ * ∑ I ∈ idealsUpTo F R, ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact hs.sum_le_tsum _ (fun _ _ => by positivity)

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3S_Aux: elementary pieces of the row large sieve

* `exp_neg_le`: `e^{-x} ≤ 2 x^{-σ}` for `x > 0`, `0 ≤ σ ≤ 2` (the Rankin step for the weight);
* `kummerL_eq_tsum'`: `kummerL` as a sum over all ideals, with the exterior indicator;
* `span_pow_mul`: `(u⁵ u') R = (𝔲⁵ 𝔲') R`;
* `card_freq_le`: `#T ≤ #{𝔲 : N𝔲 ≤ 2U} · #(U_S/U_S⁶)`. -/

set_option autoImplicit false

open NumberField

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3S

lemma exp_neg_le {σ : ℝ} (h0 : 0 ≤ σ) (h2 : σ ≤ 2) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 2 * x ^ (-σ) := by
  rcases le_or_gt 1 x with h1 | h1
  · have hq := Real.quadratic_le_exp_of_nonneg hx.le
    have hpos : 0 < Real.exp x := Real.exp_pos x
    have hle : Real.exp (-x) ≤ 2 * x ^ (-(2 : ℝ)) := by
      rw [Real.exp_neg, Real.rpow_neg hx.le, Real.rpow_two, ← div_eq_mul_inv,
        inv_le_comm₀ hpos (by positivity), inv_div]
      nlinarith [sq_nonneg x]
    exact hle.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (by norm_num))
  · have h3 : 1 ≤ x ^ (-σ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx h1.le (by linarith)
    have h4 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

open Classical in
lemma kummerL_eq_tsum' (ι : F →+* ℂ) (u : SInt 𝔪) (s : ℂ) :
    kummerL ι 𝔪 u s = ∑' I : Ideal (𝓞 F),
      (if IsExterior 𝔪 I then residueSymbol ι 𝔪 I u else 0) *
        (((Ideal.absNorm I : ℝ) : ℂ)) ^ (-s) := by
  unfold kummerL
  rw [← tsum_subtype_eq_of_support_subset (s := {I | IsExterior 𝔪 I})
    (f := fun I : Ideal (𝓞 F) => (if IsExterior 𝔪 I then residueSymbol ι 𝔪 I u else 0) *
      (((Ideal.absNorm I : ℝ) : ℂ)) ^ (-s))]
  · refine tsum_congr fun I => ?_
    simp only [if_pos I.2, Complex.ofReal_natCast]
  · intro I hI
    by_contra hne
    apply hI
    simp only
    rw [if_neg (show ¬ IsExterior 𝔪 I from hne), zero_mul]

lemma span_pow_mul {u u' : SInt 𝔪} {𝔲 𝔲' : Ideal (𝓞 F)}
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hu' : Ideal.span {u'} = 𝔲'.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    Ideal.span {u ^ 5 * u'} = (𝔲 ^ 5 * 𝔲').map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, hu',
    Ideal.map_mul, Ideal.map_pow]

lemma card_freq_le [Fintype (SClass 𝔪)] (T : Finset (FreqClass 𝔪)) (R : ℝ)
    (hT : ∀ r ∈ T, (Ideal.absNorm r.1.1 : ℝ) ≤ R) :
    T.card ≤ (L3Z.idealsUpTo F R).card * Fintype.card (SClass 𝔪) := by
  classical
  rw [← Finset.card_univ, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun r => (r.1.1, r.2)) (fun r hr => ?_) ?_
  · simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
    exact L3Z.mem_idealsUpTo.2 ⟨r.1.2.1.1, hT r hr⟩
  · intro r _ r' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2

end L3S

end ArtinPrimitiveRoots

end
end
end

section
section
/-!
# L2B_SUnit: `U_S / U_S⁶` is finite; ideals are countable

`U_S` is finitely generated: the valuations at the finitely many places of `S` give a map to
`ℤ^S` whose kernel is the image of `(𝓞 F)ˣ` (finitely generated by Dirichlet's unit theorem).
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F]

theorem placesOf_finite {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  refine (Ideal.finite_factors (R := 𝓞 F) h𝔪).subset fun v hv => ?_
  exact Ideal.dvd_iff_le.2 hv

/-- The valuation vector of an `S`-unit at the places of `S`, additively. -/
noncomputable def valVec (𝔪 : Ideal (𝓞 F)) :
    Additive (SUnit 𝔪) →+ (placesOf 𝔪 → ℤ) where
  toFun x v := Multiplicative.toAdd (v.1.valuationOfNeZero ((Additive.toMul x : SUnit 𝔪) : Fˣ))
  map_zero' := by funext v; simp
  map_add' x y := by funext v; simp

theorem mem_ker_valVec {𝔪 : Ideal (𝓞 F)} (x : Additive (SUnit 𝔪)) (hx : valVec 𝔪 x = 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    v.valuation F (((Additive.toMul x : SUnit 𝔪) : Fˣ) : F) = 1 := by
  by_cases hv : v ∈ placesOf 𝔪
  · have h := congrFun hx ⟨v, hv⟩
    simp only [valVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at h
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, show v.valuationOfNeZero _ = 1 from h]
    rfl
  · exact (Additive.toMul x).2 v hv

theorem val_unit (v : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) :
    v.valuation F ((Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u : Fˣ) : F) = 1 := by
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq]
  rfl

/-- The units of `𝓞 F` as `S`-units. -/
noncomputable def unitsToSUnit (𝔪 : Ideal (𝓞 F)) : (𝓞 F)ˣ →* SUnit 𝔪 where
  toFun u := ⟨Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u, fun v _ => val_unit v u⟩
  map_one' := by ext; simp
  map_mul' u w := by ext; simp

theorem ker_valVec (𝔪 : Ideal (𝓞 F)) :
    LinearMap.ker (valVec 𝔪).toIntLinearMap =
      LinearMap.range (MonoidHom.toAdditive (unitsToSUnit 𝔪)).toIntLinearMap := by
  ext x
  simp only [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, LinearMap.mem_range]
  constructor
  · intro hx
    have hval := mem_ker_valVec x hx
    set y : Fˣ := ((Additive.toMul x : SUnit 𝔪) : Fˣ)
    have h1 : (y : F) ∈ (algebraMap (𝓞 F) F).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ fun v => (hval v).le
    have h2 : ((y⁻¹ : Fˣ) : F) ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ fun v => ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hval v, inv_one]
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hab : a * b = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    refine ⟨Additive.ofMul ⟨a, b, hab, by rw [mul_comm, hab]⟩, ?_⟩
    apply Additive.toMul.injective
    ext
    simp [unitsToSUnit, ha, y]
  · rintro ⟨u, rfl⟩
    funext v
    simp only [valVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
      MonoidHom.toAdditive_apply_apply]
    have : v.1.valuationOfNeZero ((unitsToSUnit 𝔪 (Additive.toMul u) : SUnit 𝔪) : Fˣ) = 1 :=
      HeightOneSpectrum.valuation_of_unit_eq v.1 _
    simp only [toMul_ofMul, this]
    rfl

instance moduleFinite_SUnit {𝔪 : Ideal (𝓞 F)} [Fact (𝔪 ≠ ⊥)] :
    Module.Finite ℤ (Additive (SUnit 𝔪)) := by
  have hfin : Finite (placesOf 𝔪) := (placesOf_finite (Fact.out)).to_subtype
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (valVec 𝔪).toIntLinearMap ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ker_valVec, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _

theorem finite_SClass {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  have : Fact (𝔪 ≠ ⊥) := ⟨h𝔪⟩
  have : Group.FG (SUnit 𝔪) :=
    GroupFG.iff_add_fg.2 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  refine CommGroup.finite_of_fg_isMulTorsion _ fun x => ?_
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨6, by norm_num, ?_⟩
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨y, rfl⟩

instance countable_ideal : Countable (Ideal (𝓞 F)) := by
  have : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
    ext I; simp
  have hc : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [this]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
  exact Set.countable_univ_iff.1 hc

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (n : ℕ) :
    χ.toFun (I ^ n) = χ.toFun I ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, toFun_top]
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- **(a)** A Hecke character of nonzero modulus takes values of norm `≤ 1`. -/
theorem norm_le_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) :
    ‖χ.toFun I‖ ≤ 1 := by
  by_cases h0 : χ.toFun I = 0
  · simp [h0]
  have hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
    have := (χ.eq_zero_iff' I).not.1 h0
    push Not at this
    exact this
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI.1
  have hIh0 : I ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem hI0 h
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hIh0]
    have : (⟨I ^ h, hIh0⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI0⟩ ^ h := rfl
    rw [this, map_pow, hh, pow_card_eq_one]
  set β := Submodule.IsPrincipal.generator (I ^ h)
  have hβ : Ideal.span {β} = I ^ h := Ideal.span_singleton_generator (I ^ h)
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, Ideal.span_singleton_eq_bot.2 rfl] at hβ
    exact hI.1 (pow_eq_zero_iff hpos.ne' |>.1 hβ.symm)
  have hcop : Ideal.span {β} ⊔ 𝔪 = ⊤ := by
    rw [hβ, sup_comm]
    exact Ideal.sup_pow_eq_top' (by rw [sup_comm]; exact hI.2)
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {β} ⊔ 𝔪 := by rw [hcop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 a) ?_
    rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.2 hyz.symm, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hz, sub_zero]
  have : Finite (𝓞 F ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  have : Finite (𝓞 F ⧸ 𝔪)ˣ := Finite.of_injective _ Units.val_injective
  set k := Nat.card (𝓞 F ⧸ 𝔪)ˣ
  have hk : 0 < k := Nat.card_pos
  have hβk : Ideal.Quotient.mk 𝔪 (β ^ k) = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_pow, map_one, ← hunit.unit_spec, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one]
  have hval := χ.map_principal' (β ^ k) (pow_ne_zero _ hβ0) (Ideal.Quotient.eq.1 hβk)
  rw [← Ideal.span_singleton_pow, hβ, ← pow_mul, toFun_pow] at hval
  exact (Complex.norm_eq_one_of_pow_eq_one hval (Nat.mul_ne_zero hpos.ne' hk.ne')).le

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Euler: the row coefficients and the uniform bounds on `Re ξ > 1`

Copied from `L2C_Arith` (which also imports the `ζ^S` library stubs; this module does not):
the coefficient `a(𝔞) = η(𝔞) conj(χ_𝔞(u))` of `twistedL`, its complete multiplicativity and
`‖a‖ ≤ 1`, and the bounds `‖L‖ ≤ ∑ q^{-σ₀}`, `‖L⁻¹‖ ≤ B` on `Re ξ ≥ σ₀ > 1`, uniform in `u`. -/

open NumberField Complex Filter Topology IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F]


/-! ### Residue symbols -/

lemma norm_sexticResidueSymbol_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow]
      have := h2.choose_spec.1
      rw [this]
      simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (norm_sexticResidueSymbol_le ι 𝔪 P x) (norm_nonneg _) ih

/-! ### The twisted coefficient and its `L`-series -/

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3S_Main: RowLargeSieve (Lemma 8.1 on the rows), statement verbatim

Duality (`L3S_Dual`) with the weight `W(I) = e^{1 − N I / N}` on exterior `I`; the Gram entries are
`e ∑_{I ext} e^{−NI/N} χ_I(u_r⁵ u_r')` (`L3S_Sym`), bounded on the diagonal by Rankin
(`≤ 2e N^{1+δ} ζ(1+δ)`) and off it (`r ≠ r'`, so `u_r⁵ u_r' ∉ F^{×6}` by `L3S_Dist`) by the smoothed
Pólya–Vinogradov bound `L3S_Mellin` + the convexity cut `exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le_of_ne_pow_six` with `𝔟 = 𝔲_r 𝔲_r'`
(`N𝔟 < 4U²`). The number of rows is `≤ |U_S/U_S⁶| (2U)^{1+δ} ζ(1+δ)`. This module does not import the
target's stub. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField

noncomputable section

namespace ArtinPrimitiveRoots

open L3S in
theorem chk_exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
        ∀ U N : ℝ, 2 ≤ U → 2 ≤ N → ∀ T : Finset (FreqClass 𝔪),
          (∀ r ∈ T, (Ideal.absNorm r.1.1 : ℝ) < 2 * U) → ∀ B : Finset (Ideal (𝓞 F)),
          (∀ I ∈ B, IsExterior 𝔪 I ∧ (Ideal.absNorm I : ℝ) ≤ N) → ∀ b : Ideal (𝓞 F) → ℂ,
            ∑ r ∈ T, ‖∑ I ∈ B, b I * (χ.toFun I *
                starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r)))‖ ^ 2 ≤
              C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  obtain ⟨N₁, hconv⟩ := exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le_of_ne_pow_six n hn0 hn F ι
  refine ⟨max N₁ (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})), fun 𝔪 h𝔪 hsmall χ g ε hε => ?_⟩
  obtain ⟨A, hA⟩ := hconv 𝔪 h𝔪 (fun P hP hP0 hN => hsmall P hP hP0 (hN.trans (le_max_left _ _))) g
  -- exterior primes avoid `6`
  have h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → (6 : 𝓞 F) ∉ P := by
    intro P hP hE h6P
    have h60 : Ideal.span {(6 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      intro h; have := congrArg (fun x : 𝓞 F => (x : F)) h; simp at this
    have hle : 𝔪 ≤ P := hsmall P hP hE.1 ((Nat.le_of_dvd
      (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
      (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h6P))).trans
      (le_max_right _ _))
    exact hP.ne_top (eq_top_iff.2 (hE.2 ▸ sup_le le_rfl hle))
  -- a primitive sixth root of unity in `𝓞 F`
  obtain ⟨ω, hω⟩ : ∃ ω : 𝓞 F, IsPrimitiveRoot ω 6 := by
    haveI : NeZero n := ⟨hn0.ne'⟩
    have hζn := IsCyclotomicExtension.zeta_spec n ℚ F
    obtain ⟨k, hk⟩ := (show 6 ∣ n from dvd_trans (by norm_num) hn)
    have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ k) 6 :=
      hζn.pow hn0 (by rw [hk]; ring)
    set ζ := IsCyclotomicExtension.zeta n ℚ F ^ k
    refine ⟨⟨ζ, IsIntegral.of_pow (by norm_num : 0 < 6)
      (by rw [hζ6.pow_eq_one]; exact isIntegral_one)⟩, ?_⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) hζ6
      (FaithfulSMul.algebraMap_injective _ _)
  -- parameters
  set δ : ℝ := min (ε / 4) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : 4 * δ ≤ ε := by have := min_le_left (ε / 4) 1; linarith
  obtain ⟨Cc, hCc⟩ := hA δ hδ0
  obtain ⟨Cm, hCm0, hCm⟩ := smoothed_bound (ι := Ideal (𝓞 F)) hδ0 (by linarith) ⌈A⌉₊
  haveI : Finite (SClass 𝔪) := L2B.finite_SClass h𝔪
  letI : Fintype (SClass 𝔪) := Fintype.ofFinite _
  set σ : ℝ := 1 + δ with hσdef
  have hσ1 : 1 < σ := by linarith
  have hZs := T12B.summable_absNorm_rpow (F := F) hσ1
  set Z : ℝ := ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set S : ℝ := (Fintype.card (SClass 𝔪) : ℝ)
  set Cp : ℝ := max Cc 0
  set e1 : ℝ := Real.exp 1
  refine ⟨2 * e1 * Z + 2 ^ σ * 4 ^ (1 / 2 + δ) * Z * S * (e1 * Cm * Cp),
    fun U N hU hN T hT B hB b => ?_⟩
  have hN0 : 0 < N := by linarith
  have hU0 : 0 < U := by linarith
  -- the reduced form
  set b' : Ideal (𝓞 F) → ℂ := fun I => b I * χ.toFun I
  set φ : FreqClass 𝔪 → Ideal (𝓞 F) → ℂ :=
    fun r I => starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r))
  set W : Ideal (𝓞 F) → ℝ := fun I =>
    if IsExterior 𝔪 I then Real.exp (1 - (Ideal.absNorm I : ℝ) / N) else 0
  have hLHS : ∑ r ∈ T, ‖∑ I ∈ B, b I * (χ.toFun I *
      starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r)))‖ ^ 2 =
      ∑ r ∈ T, ‖∑ I ∈ B, b' I * φ r I‖ ^ 2 := by
    simp only [b', φ, mul_assoc]
  have hb' : ∑ I ∈ B, ‖b' I‖ ^ 2 ≤ ∑ I ∈ B, ‖b I‖ ^ 2 := by
    refine Finset.sum_le_sum fun I _ => ?_
    simp only [b', norm_mul]
    have := T12B.norm_le_one h𝔪 χ I
    gcongr
    calc ‖b I‖ * ‖χ.toFun I‖ ≤ ‖b I‖ * 1 := by gcongr
      _ = ‖b I‖ := mul_one _
  -- the weight
  have hW0 : ∀ I, 0 ≤ W I := fun I => by
    simp only [W]; split_ifs <;> positivity
  have hW1 : ∀ I ∈ B, 1 ≤ W I := fun I hI => by
    simp only [W, if_pos (hB I hI).1]
    refine Real.one_le_exp ?_
    have : (Ideal.absNorm I : ℝ) / N ≤ 1 := (div_le_one hN0).2 (hB I hI).2
    linarith
  have hWle : ∀ I, W I ≤ 2 * e1 * N ^ σ * ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
    intro I
    simp only [W]
    split_ifs with hI
    · have hq : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast L3Z.absNorm_pos hI.1
      have hx : 0 < (Ideal.absNorm I : ℝ) / N := div_pos hq hN0
      rw [sub_eq_add_neg, Real.exp_add]
      have := exp_neg_le (by linarith : (0 : ℝ) ≤ σ) (by linarith : σ ≤ 2) hx
      rw [Real.div_rpow hq.le hN0.le, Real.rpow_neg hN0.le, div_inv_eq_mul] at this
      calc e1 * Real.exp (-((Ideal.absNorm I : ℝ) / N))
          ≤ e1 * (2 * ((Ideal.absNorm I : ℝ) ^ (-σ) * N ^ σ)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    · positivity
  have hWs : Summable W :=
    (hZs.mul_left (2 * e1 * N ^ σ)).of_nonneg_of_le hW0 fun I => by
      simpa [mul_assoc] using hWle I
  have hφ1 : ∀ r I, ‖φ r I‖ ≤ 1 := fun r I => by
    simp only [φ, RCLike.norm_conj]; exact L3Z.norm_residueSymbol_le ι 𝔪 I _
  have hterm : ∀ r r' I, ‖(W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))‖ ≤ W I := by
    intro r r' I
    have h1 := hφ1 r I
    have h2 : ‖starRingEnd ℂ (φ r' I)‖ ≤ 1 := by rw [RCLike.norm_conj]; exact hφ1 r' I
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW0 I)]
    calc W I * (‖φ r I‖ * ‖starRingEnd ℂ (φ r' I)‖) ≤ W I * (1 * 1) := by
          have := hW0 I
          gcongr
      _ = W I := by ring
  have hs : ∀ r r', Summable (fun I => (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))) :=
    fun r r' => Summable.of_norm_bounded hWs (hterm r r')
  -- the diagonal
  set D : ℝ := 2 * e1 * N ^ σ * Z
  have hD : ∀ r r', ‖∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))‖ ≤ D := by
    intro r r'
    calc _ ≤ ∑' I, W I :=
          tsum_of_norm_bounded hWs.hasSum (hterm r r')
      _ ≤ ∑' I, 2 * e1 * N ^ σ * ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) :=
          hWs.tsum_le_tsum hWle (hZs.mul_left _)
      _ = D := by rw [tsum_mul_left]
  -- the off-diagonal
  set O : ℝ := e1 * Cm * (Cp * (4 * U ^ 2) ^ (1 / 2 + δ)) * N ^ δ
  have hOff : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' →
      ‖∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I))‖ ≤ O := by
    intro r hr r' hr' hrr
    set u := freqElt g r
    set u' := freqElt g r'
    set 𝔲 := r.1.1
    set 𝔲' := r'.1.1
    set a : Ideal (𝓞 F) → ℂ := fun I =>
      if IsExterior 𝔪 I then residueSymbol ι 𝔪 I (u ^ 5 * u') else 0
    have heq : ∀ I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I)) =
        (e1 : ℂ) * (a I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (N : ℂ))) := by
      intro I
      simp only [W, a, φ]
      split_ifs with hI
      · rw [RCLike.conj_conj, rs_pair ι hω h6 hI u u']
        simp only [e1]
        push_cast
        rw [sub_eq_add_neg, Complex.exp_add, ← neg_div]
        ring
      · simp
    have hH : ∑' I, (W I : ℂ) * (φ r I * starRingEnd ℂ (φ r' I)) =
        (e1 : ℂ) * ∑' I, a I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (N : ℂ)) := by
      simp_rw [heq]; exact tsum_mul_left
    -- the convexity bound for `u⁵ u'`
    have h𝔲0 : 𝔲 ≠ ⊥ := r.1.2.1.1
    have h𝔲0' : 𝔲' ≠ ⊥ := r'.1.2.1.1
    obtain ⟨Λ, hΛd, hΛeq, hΛb⟩ := hCc (u ^ 5 * u') (𝔲 ^ 5 * 𝔲') (𝔲 * 𝔲')
      (mul_ne_zero (pow_ne_zero _ h𝔲0) h𝔲0')
      (span_pow_mul (L3K.span_freqElt g r) (L3K.span_freqElt g r'))
      (freqElt_pow_mul_ne_pow_six g hrr) (mul_ne_zero h𝔲0 h𝔲0') (by
        intro P hP hle
        rcases hP.mul_le.1 hle with h1 | h1
        · exact le_trans Ideal.mul_le_left (hP.le_of_pow_le h1)
        · exact le_trans Ideal.mul_le_right h1)
    have hnb : (Ideal.absNorm (𝔲 * 𝔲') : ℝ) ≤ 4 * U ^ 2 := by
      rw [map_mul, Nat.cast_mul]
      have h1 := hT r hr
      have h2 := hT r' hr'
      have : (Ideal.absNorm 𝔲 : ℝ) * Ideal.absNorm 𝔲' ≤ (2 * U) * (2 * U) :=
        mul_le_mul h1.le h2.le (Nat.cast_nonneg _) (by positivity)
      nlinarith
    set K : ℝ := Cp * (4 * U ^ 2) ^ (1 / 2 + δ)
    have hK0 : 0 ≤ K := by positivity
    have hΛK : ∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → ‖Λ z‖ ≤ K * (1 + |z.im|) ^ ⌈A⌉₊ := by
      intro z h1 h2
      refine (hΛb z (by linarith) (by linarith)).trans ?_
      have hpA : (1 + |z.im|) ^ A ≤ (1 + |z.im|) ^ ⌈A⌉₊ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (Nat.le_ceil A)
      have hb1 : (Ideal.absNorm (𝔲 * 𝔲') : ℝ) ^ (1 / 2 + δ) ≤ (4 * U ^ 2) ^ (1 / 2 + δ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hnb (by linarith)
      calc Cc * (Ideal.absNorm (𝔲 * 𝔲') : ℝ) ^ (1 / 2 + δ) * (1 + |z.im|) ^ A
          ≤ Cp * (Ideal.absNorm (𝔲 * 𝔲') : ℝ) ^ (1 / 2 + δ) * (1 + |z.im|) ^ A := by
            gcongr; exact le_max_left _ _
        _ ≤ Cp * (4 * U ^ 2) ^ (1 / 2 + δ) * (1 + |z.im|) ^ ⌈A⌉₊ := by
            have : 0 ≤ Cp := le_max_right _ _
            gcongr
    have hsum2 : Summable (fun I : Ideal (𝓞 F) => ‖a I‖ * (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ))) := by
      refine (T12B.summable_absNorm_rpow (F := F) (by norm_num : (1 : ℝ) < 2)).of_nonneg_of_le
        (fun _ => by positivity) fun I => ?_
      have ha : ‖a I‖ ≤ 1 := by
        simp only [a]; split_ifs
        · exact L3Z.norm_residueSymbol_le ι 𝔪 I _
        · simp
      calc ‖a I‖ * (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) := by
            gcongr
        _ = _ := one_mul _
    have hsm := hCm a (fun I => (Ideal.absNorm I : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun I hI => by
        have : I = ⊥ := Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast hI)
        simp only [a, this, if_neg (fun h : IsExterior 𝔪 ⊥ => h.1 rfl)])
      hsum2 Λ hΛd (fun s hs => (hΛeq s hs).trans (kummerL_eq_tsum' ι _ s)) K hK0 hΛK N
      (by linarith)
    rw [hH, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc e1 * ‖∑' I, a I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (N : ℂ))‖
        ≤ e1 * (Cm * K * N ^ δ) := mul_le_mul_of_nonneg_left hsm (by positivity)
      _ = O := by simp only [O, K]; ring
  -- duality
  have hO0 : 0 ≤ O := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hdual := dual_sieve T B φ b' W hW0 hW1 hs D O hD0 hO0 (fun r hr r' hr' => by
    split_ifs with h
    · exact hD r r'
    · exact hOff r hr r' hr' h)
  -- counting the rows
  have hcard : (T.card : ℝ) ≤ (2 * U) ^ σ * Z * S := by
    have h1 := card_freq_le T (2 * U) (fun r hr => (hT r hr).le)
    have h2 := L3Z.card_idealsUpTo_le (F := F) (by linarith : (0 : ℝ) ≤ σ) (by positivity : (0 : ℝ) ≤ 2 * U) hZs
    calc (T.card : ℝ) ≤ ((L3Z.idealsUpTo F (2 * U)).card : ℝ) * S := by
          simp only [S]; exact_mod_cast h1
      _ ≤ (2 * U) ^ σ * Z * S := by gcongr
  -- the final arithmetic
  have hNU : 1 ≤ N * U := by nlinarith
  have hNδ : N ^ δ ≤ (N * U) ^ ε := by
    calc N ^ δ ≤ (N * U) ^ δ := Real.rpow_le_rpow hN0.le (by nlinarith) hδ0.le
      _ ≤ (N * U) ^ ε := Real.rpow_le_rpow_of_exponent_le hNU (by linarith)
  have hDb : D ≤ 2 * e1 * Z * (N * (N * U) ^ ε) := by
    have : N ^ σ = N * N ^ δ := by
      rw [hσdef, Real.rpow_add hN0, Real.rpow_one]
    calc D = 2 * e1 * Z * (N * N ^ δ) := by simp only [D, this]; ring
      _ ≤ 2 * e1 * Z * (N * (N * U) ^ ε) := by gcongr
  have hTOb : (T.card : ℝ) * O ≤
      2 ^ σ * 4 ^ (1 / 2 + δ) * Z * S * (e1 * Cm * Cp) * (U ^ 2 * (N * U) ^ ε) := by
    have hU1 : 1 ≤ U := by linarith
    have hpow : (2 * U) ^ σ * (4 * U ^ 2) ^ (1 / 2 + δ) * N ^ δ ≤
        2 ^ σ * 4 ^ (1 / 2 + δ) * (U ^ 2 * (N * U) ^ ε) := by
      rw [Real.mul_rpow (by norm_num) hU0.le, Real.mul_rpow (by norm_num) (by positivity)]
      have hU2 : (U ^ 2) ^ (1 / 2 + δ) = U ^ (1 + 2 * δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num; ring_nf
      rw [hU2]
      have hsplit : U ^ σ * U ^ (1 + 2 * δ) = U ^ 2 * U ^ (3 * δ) := by
        rw [← Real.rpow_add hU0, ← Real.rpow_natCast, ← Real.rpow_add hU0]
        congr 1; push_cast; ring
      have h3 : U ^ (3 * δ) * N ^ δ ≤ (N * U) ^ ε := by
        calc U ^ (3 * δ) * N ^ δ ≤ U ^ (3 * δ) * N ^ (3 * δ) := by
              gcongr
              · linarith
              · linarith
          _ = (N * U) ^ (3 * δ) := by rw [Real.mul_rpow hN0.le hU0.le]; ring
          _ ≤ (N * U) ^ ε := Real.rpow_le_rpow_of_exponent_le hNU (by linarith)
      calc 2 ^ σ * U ^ σ * (4 ^ (1 / 2 + δ) * U ^ (1 + 2 * δ)) * N ^ δ
          = 2 ^ σ * 4 ^ (1 / 2 + δ) * (U ^ 2 * (U ^ (3 * δ) * N ^ δ)) := by
            rw [show 2 ^ σ * U ^ σ * (4 ^ (1 / 2 + δ) * U ^ (1 + 2 * δ)) * N ^ δ =
              2 ^ σ * 4 ^ (1 / 2 + δ) * ((U ^ σ * U ^ (1 + 2 * δ)) * N ^ δ) by ring, hsplit]
            ring
        _ ≤ 2 ^ σ * 4 ^ (1 / 2 + δ) * (U ^ 2 * (N * U) ^ ε) := by gcongr
    have hCp : 0 ≤ Cp := le_max_right _ _
    calc (T.card : ℝ) * O ≤ ((2 * U) ^ σ * Z * S) * O :=
          mul_le_mul_of_nonneg_right hcard hO0
      _ = Z * S * (e1 * Cm * Cp) * ((2 * U) ^ σ * (4 * U ^ 2) ^ (1 / 2 + δ) * N ^ δ) := by
          simp only [O]; ring
      _ ≤ Z * S * (e1 * Cm * Cp) * (2 ^ σ * 4 ^ (1 / 2 + δ) * (U ^ 2 * (N * U) ^ ε)) := by
          gcongr
      _ = _ := by ring
  rw [hLHS]
  have hbs : 0 ≤ ∑ I ∈ B, ‖b I‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNUε : 0 ≤ (N * U) ^ ε := by positivity
  calc ∑ r ∈ T, ‖∑ I ∈ B, b' I * φ r I‖ ^ 2 ≤ (D + T.card * O) * ∑ I ∈ B, ‖b' I‖ ^ 2 := hdual
    _ ≤ (D + T.card * O) * ∑ I ∈ B, ‖b I‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ ≤ (2 * e1 * Z * (N * (N * U) ^ ε) +
          2 ^ σ * 4 ^ (1 / 2 + δ) * Z * S * (e1 * Cm * Cp) * (U ^ 2 * (N * U) ^ ε)) *
          ∑ I ∈ B, ‖b I‖ ^ 2 := by gcongr
    _ = (2 * e1 * Z * N + 2 ^ σ * 4 ^ (1 / 2 + δ) * Z * S * (e1 * Cm * Cp) * U ^ 2) *
          (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by ring
    _ ≤ (2 * e1 * Z + 2 ^ σ * 4 ^ (1 / 2 + δ) * Z * S * (e1 * Cm * Cp)) * (N + U ^ 2) *
          (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
        have hc1 : 0 ≤ 2 * e1 * Z := by positivity
        have hc2 : 0 ≤ 2 ^ σ * 4 ^ (1 / 2 + δ) * Z * S * (e1 * Cm * Cp) := by
          have : 0 ≤ Cp := le_max_right _ _
          positivity
        gcongr
        nlinarith [sq_nonneg U]

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3S_Dev: RowLargeSieve `exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le` (ad4ea5b9)

The target's statement verbatim, under its own name, from `L3S_Main`. Does not import the stub. -/

open NumberField

namespace ArtinPrimitiveRoots

theorem exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
        ∀ U N : ℝ, 2 ≤ U → 2 ≤ N → ∀ T : Finset (FreqClass 𝔪),
          (∀ r ∈ T, (Ideal.absNorm r.1.1 : ℝ) < 2 * U) → ∀ B : Finset (Ideal (𝓞 F)),
          (∀ I ∈ B, IsExterior 𝔪 I ∧ (Ideal.absNorm I : ℝ) ≤ N) → ∀ b : Ideal (𝓞 F) → ℂ,
            ∑ r ∈ T, ‖∑ I ∈ B, b I * (χ.toFun I *
                starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r)))‖ ^ 2 ≤
              C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 :=
  chk_exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
        ∀ U N : ℝ, 2 ≤ U → 2 ≤ N → ∀ T : Finset (FreqClass 𝔪),
          (∀ r ∈ T, (Ideal.absNorm r.1.1 : ℝ) < 2 * U) → ∀ B : Finset (Ideal (𝓞 F)),
          (∀ I ∈ B, IsExterior 𝔪 I ∧ (Ideal.absNorm I : ℝ) ≤ N) → ∀ b : Ideal (𝓞 F) → ℂ,
            ∑ r ∈ T, ‖∑ I ∈ B, b I * (χ.toFun I *
                starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r)))‖ ^ 2 ≤
              C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  exact ArtinPrimitiveRoots.exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le n hn0 hn F ι

end
