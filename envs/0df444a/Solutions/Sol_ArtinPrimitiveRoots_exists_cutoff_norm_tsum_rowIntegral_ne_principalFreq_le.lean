-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T21:08:27.560991+00:00
-- url     : https://prove2.me/submissions/2f87d51e-1022-48af-a584-1845666022b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_freqSeries_mul_twistedL_eq
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one
universe u

section
/-! # L2C_Maj: polynomial majorants `ν_N(t) = (1 + |t|)^{-N}`

* `nu N t = (1 + |t|)^{-N}`: positive, `≤ 1`, antitone in `N`, integrable for `N > 1`, tending to
  `0` at `±∞` for `N > 0`;
* `gauss_split`: `e^{-(a+b)²} ν_{N+M}(b) ≤ e^{N²/4} ν_N(a) ν_M(b)` (`N ≥ 0`);
* `poly_nu`: `(2 + |t|)^A ν_{A+2}(t) ≤ 2^A ν_2(t)`;
* `nu_tail`: `ν_N(t) ≤ (1 + T)^{-(N-2)} ν_2(t)` for `|t| ≥ T ≥ 0`, `N ≥ 2`. -/

open Real MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L2C

noncomputable section

/-- `ν_N(t) = (1 + |t|)^{-N}`. -/
def nu (N t : ℝ) : ℝ := (1 + |t|) ^ (-N)

lemma one_add_abs_pos (t : ℝ) : 0 < 1 + |t| := by positivity

lemma nu_pos (N t : ℝ) : 0 < nu N t := Real.rpow_pos_of_pos (one_add_abs_pos t) _

lemma nu_nonneg (N t : ℝ) : 0 ≤ nu N t := (nu_pos N t).le

lemma nu_anti {N N' : ℝ} (h : N ≤ N') (t : ℝ) : nu N' t ≤ nu N t :=
  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)

lemma nu_add (N M t : ℝ) : nu (N + M) t = nu N t * nu M t := by
  unfold nu
  rw [← Real.rpow_add (one_add_abs_pos t)]
  ring_nf

lemma integrable_nu {N : ℝ} (hN : 1 < N) : Integrable (nu N) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := N) (by simpa using hN)
  exact h.congr (Eventually.of_forall fun t => by simp [nu, Real.norm_eq_abs])

lemma tendsto_nu_atTop {N : ℝ} (hN : 0 < N) : Tendsto (nu N) atTop (𝓝 0) := by
  unfold nu
  have h1 : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop.comp tendsto_id)
  exact (tendsto_rpow_neg_atTop hN).comp h1

lemma tendsto_nu_atBot {N : ℝ} (hN : 0 < N) : Tendsto (nu N) atBot (𝓝 0) := by
  unfold nu
  have h1 : Tendsto (fun t : ℝ => 1 + |t|) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_abs_atBot_atTop
  exact (tendsto_rpow_neg_atTop hN).comp h1

/-- `e^{-x²} (1 + |x|)^N ≤ e^{N²/4}` for `N ≥ 0`. -/
lemma exp_neg_sq_mul_le {N : ℝ} (hN : 0 ≤ N) (x : ℝ) :
    Real.exp (-x ^ 2) * (1 + |x|) ^ N ≤ Real.exp (N ^ 2 / 4) := by
  have h1 : (1 + |x|) ^ N ≤ Real.exp (N * |x|) := by
    calc (1 + |x|) ^ N ≤ (Real.exp |x|) ^ N :=
          Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp |x|]) hN
      _ = Real.exp (N * |x|) := by rw [← Real.exp_mul]; ring_nf
  calc Real.exp (-x ^ 2) * (1 + |x|) ^ N ≤ Real.exp (-x ^ 2) * Real.exp (N * |x|) := by gcongr
    _ = Real.exp (-x ^ 2 + N * |x|) := by rw [Real.exp_add]
    _ ≤ Real.exp (N ^ 2 / 4) := by
        apply Real.exp_le_exp.2
        nlinarith [sq_nonneg (|x| - N / 2), sq_abs x]

/-- `e^{-(a+b)²} ν_{N+M}(b) ≤ e^{N²/4} ν_N(a) ν_M(b)`. -/
lemma gauss_split {N : ℝ} (hN : 0 ≤ N) (M a b : ℝ) :
    Real.exp (-(a + b) ^ 2) * nu (N + M) b ≤ Real.exp (N ^ 2 / 4) * nu N a * nu M b := by
  rw [nu_add]
  have ha := one_add_abs_pos a
  have hb := one_add_abs_pos b
  have hab := one_add_abs_pos (a + b)
  -- (1 + |a|) ≤ (1 + |a + b|)(1 + |b|)
  have htri : 1 + |a| ≤ (1 + |a + b|) * (1 + |b|) := by
    have : |a| ≤ |a + b| + |b| := by
      calc |a| = |(a + b) + (-b)| := by ring_nf
        _ ≤ |a + b| + |-b| := abs_add_le _ _
        _ = |a + b| + |b| := by rw [abs_neg]
    nlinarith [abs_nonneg (a + b), abs_nonneg b]
  have hpow : (1 + |a|) ^ N ≤ (1 + |a + b|) ^ N * (1 + |b|) ^ N := by
    rw [← Real.mul_rpow hab.le hb.le]
    exact Real.rpow_le_rpow ha.le htri hN
  -- ν_N(b) ≤ (1 + |a+b|)^N ν_N(a)
  have hnu : nu N b ≤ (1 + |a + b|) ^ N * nu N a := by
    unfold nu
    rw [Real.rpow_neg hb.le, Real.rpow_neg ha.le]
    rw [inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hb _)]
    have hpa := Real.rpow_pos_of_pos ha N
    calc (1 : ℝ) = (1 + |a|) ^ N * ((1 + |a|) ^ N)⁻¹ := by field_simp
      _ ≤ (1 + |a + b|) ^ N * (1 + |b|) ^ N * ((1 + |a|) ^ N)⁻¹ := by gcongr
      _ = (1 + |b|) ^ N * ((1 + |a + b|) ^ N * ((1 + |a|) ^ N)⁻¹) := by ring
      _ = _ := by ring
  have he := exp_neg_sq_mul_le hN (a + b)
  have hM := nu_nonneg M b
  calc Real.exp (-(a + b) ^ 2) * (nu N b * nu M b)
      ≤ Real.exp (-(a + b) ^ 2) * ((1 + |a + b|) ^ N * nu N a * nu M b) := by gcongr
    _ = (Real.exp (-(a + b) ^ 2) * (1 + |a + b|) ^ N) * nu N a * nu M b := by ring
    _ ≤ Real.exp (N ^ 2 / 4) * nu N a * nu M b := by
        gcongr
        · exact (nu_nonneg N a)

/-- `(2 + |t|)^A ν_{A+2}(t) ≤ 2^A ν_2(t)` for `A ≥ 0`. -/
lemma poly_nu {A : ℝ} (hA : 0 ≤ A) (t : ℝ) : (2 + |t|) ^ A * nu (A + 2) t ≤ 2 ^ A * nu 2 t := by
  rw [nu_add]
  have h1 : (2 + |t|) ^ A ≤ 2 ^ A * (1 + |t|) ^ A := by
    rw [← Real.mul_rpow (by norm_num) (one_add_abs_pos t).le]
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hA
  have h2 : (1 + |t|) ^ A * nu A t = 1 := by
    unfold nu
    rw [← Real.rpow_add (one_add_abs_pos t)]
    simp
  calc (2 + |t|) ^ A * (nu A t * nu 2 t) ≤ 2 ^ A * (1 + |t|) ^ A * (nu A t * nu 2 t) := by
        gcongr
        exact mul_nonneg (nu_nonneg _ _) (nu_nonneg _ _)
    _ = 2 ^ A * ((1 + |t|) ^ A * nu A t) * nu 2 t := by ring
    _ = 2 ^ A * nu 2 t := by rw [h2, mul_one]

/-- `ν_N(t) ≤ (1 + T)^{-(N-2)} ν_2(t)` for `T ≤ |t|`, `0 ≤ T`, `2 ≤ N`. -/
lemma nu_tail {N T t : ℝ} (hN : 2 ≤ N) (hT : 0 ≤ T) (ht : T ≤ |t|) :
    nu N t ≤ (1 + T) ^ (-(N - 2)) * nu 2 t := by
  have h := nu_add (N - 2) 2 t
  rw [show N - 2 + 2 = N by ring] at h
  rw [h]
  gcongr
  · exact nu_nonneg _ _
  · unfold nu
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

end

end L2C

end ArtinPrimitiveRoots
end

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

section
/-! # C3P_Maj: the majorants and the Fubini swaps

`u t = (1 + t²)⁻¹`, `γ x = exp(−x²/2)`, and the three-variable majorant
`u t₁ · u t₂ · γ (t₁ + t₃)`; `e^{−(t₁+t₃)²} u t₃ ≤ 4 u t₁ γ(t₁+t₃)` moves the Gaussian's decay onto
the outer variable. -/

open MeasureTheory Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

/-! ### Integrability of the majorants -/

/-! ### Fubini -/

/-- Moving the outermost of three iterated integrals innermost. -/
theorem swap3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → ℝ → ℝ → E}
    (hf : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (volume.prod (volume.prod volume))) :
    ∫ a, ∫ b, ∫ c, f a b c = ∫ b, ∫ c, ∫ a, f a b c := by
  have h1 : ∀ᵐ a, ∫ b, ∫ c, f a b c = ∫ q : ℝ × ℝ, f a q.1 q.2 ∂(volume.prod volume) := by
    filter_upwards [hf.prod_right_ae] with a ha
    exact (integral_prod (fun q : ℝ × ℝ => f a q.1 q.2) ha).symm
  rw [integral_congr_ae h1]
  have h2 := integral_integral_swap (μ := volume) (ν := volume.prod volume)
    (f := fun a (q : ℝ × ℝ) => f a q.1 q.2) hf
  rw [h2]
  have h3 : Integrable (fun q : ℝ × ℝ => ∫ a, f a q.1 q.2) (volume.prod volume) :=
    hf.integral_prod_right
  rw [integral_prod _ h3]

end C3P

end ArtinPrimitiveRoots
end

section
/-! # L2C_Shift: contour moves of triple line integrals with product majorants

`I3 Φ a b c = ∫ t₁ ∫ t₂ ∫ t₃ Φ(a + it₁, b + it₂, c + it₃)`.

* `shift_z`, `shift_w`, `shift_xi`: move one of the three lines across a strip on which `Φ` is
  holomorphic in that variable, given a product majorant `m₁(t₁) m₂(t₂) m₃(t₃)`;
* `norm_I3_le`: `‖I3‖ ≤ ∫m₁ ∫m₂ ∫m₃`;
* `trunc_xi`: the truncated move of the outer line to the left, across a rectangle of height `T`
  only (the zero-detector step (8.17)–(8.19)). -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L2C

noncomputable section

/-- The triple line integral. -/
def I3 (Φ : ℂ → ℂ → ℂ → ℂ) (a b c : ℝ) : ℂ :=
  ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, Φ (a + t1 * I) (b + t2 * I) (c + t3 * I)

lemma integrable_prod3 {m1 m2 m3 : ℝ → ℝ} (h1 : Integrable m1) (h2 : Integrable m2)
    (h3 : Integrable m3) :
    Integrable (fun p : ℝ × ℝ × ℝ => m1 p.1 * (m2 p.2.1 * m3 p.2.2))
      (volume.prod (volume.prod volume)) :=
  h1.mul_prod (h2.mul_prod h3)

/-- Moving the outermost of three iterated integrals innermost, for any σ-finite outer measure. -/
theorem swap3' {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℝ → ℝ → ℂ}
    (hf : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (μ.prod (volume.prod volume))) :
    ∫ a, (∫ b, ∫ c, f a b c) ∂μ = ∫ b, ∫ c, ∫ a, f a b c ∂μ := by
  have h1 : ∀ᵐ a ∂μ, ∫ b, ∫ c, f a b c = ∫ q : ℝ × ℝ, f a q.1 q.2 ∂(volume.prod volume) := by
    filter_upwards [hf.prod_right_ae] with a ha
    exact (integral_prod (fun q : ℝ × ℝ => f a q.1 q.2) ha).symm
  rw [integral_congr_ae h1]
  have h2 := integral_integral_swap (μ := μ) (ν := volume.prod volume)
    (f := fun a (q : ℝ × ℝ) => f a q.1 q.2) hf
  rw [h2]
  have h3 : Integrable (fun q : ℝ × ℝ => ∫ a, f a q.1 q.2 ∂μ) (volume.prod volume) :=
    hf.integral_prod_right
  rw [integral_prod _ h3]

/-- Moving the inner (`z`) line. -/
theorem shift_z (Φ : ℂ → ℂ → ℂ → ℂ) {a b c c' : ℝ} (hcc : c ≤ c') {m1 m2 m3 : ℝ → ℝ}
    (hm3 : Integrable m3) (h3t : Tendsto m3 atTop (𝓝 0)) (h3b : Tendsto m3 atBot (𝓝 0))
    (hd : ∀ t1 t2 : ℝ, DifferentiableOn ℂ (fun z => Φ (a + t1 * I) (b + t2 * I) z)
      {z | c ≤ z.re ∧ z.re ≤ c'})
    (hb : ∀ (t1 t2 : ℝ) (z : ℂ), c ≤ z.re → z.re ≤ c' →
      ‖Φ (a + t1 * I) (b + t2 * I) z‖ ≤ m1 t1 * m2 t2 * m3 z.im) :
    I3 Φ a b c = I3 Φ a b c' := by
  unfold I3
  congr 1; funext t1; congr 1; funext t2
  exact C3P.C3P_shift (g := fun t => m1 t1 * m2 t2 * m3 t) hcc (hd t1 t2)
    (hm3.const_mul _) (by simpa using h3t.const_mul (m1 t1 * m2 t2))
    (by simpa using h3b.const_mul (m1 t1 * m2 t2)) fun s h1 h2 => hb t1 t2 s h1 h2

/-- Moving the middle (`w`) line. -/
theorem shift_w (Φ : ℂ → ℂ → ℂ → ℂ) {a b b' c : ℝ} (hbb : b ≤ b') {m1 m2 m3 : ℝ → ℝ}
    (hm2 : Integrable m2) (h2t : Tendsto m2 atTop (𝓝 0)) (h2b : Tendsto m2 atBot (𝓝 0))
    (hm3 : Integrable m3)
    (hc : ∀ t1 : ℝ, ∀ x ∈ ({b, b'} : Set ℝ),
      Continuous fun p : ℝ × ℝ => Φ (a + t1 * I) (x + p.1 * I) (c + p.2 * I))
    (hd : ∀ t1 t3 : ℝ, DifferentiableOn ℂ (fun w => Φ (a + t1 * I) w (c + t3 * I))
      {w | b ≤ w.re ∧ w.re ≤ b'})
    (hb : ∀ (t1 t3 : ℝ) (w : ℂ), b ≤ w.re → w.re ≤ b' →
      ‖Φ (a + t1 * I) w (c + t3 * I)‖ ≤ m1 t1 * m2 w.im * m3 t3) :
    I3 Φ a b c = I3 Φ a b' c := by
  unfold I3
  congr 1; funext t1
  have hint : ∀ x ∈ ({b, b'} : Set ℝ), Integrable
      (Function.uncurry fun t2 t3 : ℝ => Φ (a + t1 * I) (x + t2 * I) (c + t3 * I))
      (volume.prod volume) := by
    intro x hx
    refine ((hm2.mul_prod hm3).const_mul (m1 t1)).mono' (hc t1 x hx).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hx' : b ≤ x ∧ x ≤ b' := by
      rcases hx with rfl | rfl
      · exact ⟨le_rfl, hbb⟩
      · exact ⟨hbb, le_rfl⟩
    have := hb t1 p.2 ((x : ℂ) + p.1 * I) (by simpa using hx'.1) (by simpa using hx'.2)
    show ‖Φ (a + t1 * I) (x + p.1 * I) (c + p.2 * I)‖ ≤ m1 t1 * (m2 p.1 * m3 p.2)
    refine this.trans_eq ?_
    simp; ring
  rw [integral_integral_swap (hint b (by simp)), integral_integral_swap (hint b' (by simp))]
  congr 1; funext t3
  exact C3P.C3P_shift (g := fun t => m1 t1 * m3 t3 * m2 t) hbb (hd t1 t3)
    (hm2.const_mul _) (by simpa using h2t.const_mul (m1 t1 * m3 t3))
    (by simpa using h2b.const_mul (m1 t1 * m3 t3))
    fun s h1 h2 => (hb t1 t3 s h1 h2).trans_eq (by ring)

/-- Moving the outer (`ξ`) line. -/
theorem shift_xi (Φ : ℂ → ℂ → ℂ → ℂ) {a a' b c : ℝ} (haa : a ≤ a') {m1 m2 m3 : ℝ → ℝ}
    (hm1 : Integrable m1) (h1t : Tendsto m1 atTop (𝓝 0)) (h1b : Tendsto m1 atBot (𝓝 0))
    (hm2 : Integrable m2) (hm3 : Integrable m3)
    (hc : ∀ x ∈ ({a, a'} : Set ℝ),
      Continuous fun p : ℝ × ℝ × ℝ => Φ (x + p.1 * I) (b + p.2.1 * I) (c + p.2.2 * I))
    (hd : ∀ t2 t3 : ℝ, DifferentiableOn ℂ (fun ξ => Φ ξ (b + t2 * I) (c + t3 * I))
      {ξ | a ≤ ξ.re ∧ ξ.re ≤ a'})
    (hb : ∀ (ξ : ℂ) (t2 t3 : ℝ), a ≤ ξ.re → ξ.re ≤ a' →
      ‖Φ ξ (b + t2 * I) (c + t3 * I)‖ ≤ m1 ξ.im * m2 t2 * m3 t3) :
    I3 Φ a b c = I3 Φ a' b c := by
  have hint : ∀ x ∈ ({a, a'} : Set ℝ), Integrable
      (fun p : ℝ × ℝ × ℝ => Φ (x + p.1 * I) (b + p.2.1 * I) (c + p.2.2 * I))
      (volume.prod (volume.prod volume)) := by
    intro x hx
    refine (integrable_prod3 hm1 hm2 hm3).mono' (hc x hx).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hx' : a ≤ x ∧ x ≤ a' := by
      rcases hx with rfl | rfl
      · exact ⟨le_rfl, haa⟩
      · exact ⟨haa, le_rfl⟩
    have := hb ((x : ℂ) + p.1 * I) p.2.1 p.2.2 (by simpa using hx'.1) (by simpa using hx'.2)
    refine this.trans_eq ?_
    simp; ring
  unfold I3
  rw [C3P.swap3 (f := fun t1 t2 t3 => Φ (a + t1 * I) (b + t2 * I) (c + t3 * I)) (hint a (by simp)),
    C3P.swap3 (f := fun t1 t2 t3 => Φ (a' + t1 * I) (b + t2 * I) (c + t3 * I)) (hint a' (by simp))]
  congr 1; funext t2; congr 1; funext t3
  exact C3P.C3P_shift (g := fun t => m2 t2 * m3 t3 * m1 t) haa (hd t2 t3)
    (hm1.const_mul _) (by simpa using h1t.const_mul (m2 t2 * m3 t3))
    (by simpa using h1b.const_mul (m2 t2 * m3 t3))
    fun s h1 h2 => (hb s t2 t3 h1 h2).trans_eq (by ring)

/-- Norm bound for a two-fold integral with a product majorant. -/
lemma norm_iter2_le' {f : ℝ → ℝ → ℂ} {m2 m3 : ℝ → ℝ} {K : ℝ} (hm2 : Integrable m2)
    (hm3 : Integrable m3) (hb : ∀ t2 t3, ‖f t2 t3‖ ≤ K * m2 t2 * m3 t3) :
    ‖∫ t2, ∫ t3, f t2 t3‖ ≤ K * (∫ t, m2 t) * ∫ t, m3 t := by
  have h1 : ∀ t2, ‖∫ t3, f t2 t3‖ ≤ K * m2 t2 * ∫ t, m3 t := by
    intro t2
    have := norm_integral_le_of_norm_le (hm3.const_mul (K * m2 t2))
      (Eventually.of_forall fun t3 => hb t2 t3)
    rwa [integral_const_mul] at this
  have := norm_integral_le_of_norm_le ((hm2.const_mul K).mul_const (∫ t, m3 t))
    (Eventually.of_forall fun t2 => (h1 t2).trans_eq (by ring))
  rw [integral_mul_const, integral_const_mul] at this
  exact this

/-- Norm bound for `I3` with a product majorant. -/
theorem norm_I3_le (Φ : ℂ → ℂ → ℂ → ℂ) (a b c : ℝ) {m1 m2 m3 : ℝ → ℝ}
    (hm1 : Integrable m1) (hm2 : Integrable m2) (hm3 : Integrable m3)
    (hb : ∀ t1 t2 t3 : ℝ, ‖Φ (a + t1 * I) (b + t2 * I) (c + t3 * I)‖ ≤ m1 t1 * m2 t2 * m3 t3) :
    ‖I3 Φ a b c‖ ≤ (∫ t, m1 t) * (∫ t, m2 t) * ∫ t, m3 t := by
  have h2 : ∀ t1 : ℝ, ‖∫ t2 : ℝ, ∫ t3 : ℝ, Φ (a + t1 * I) (b + t2 * I) (c + t3 * I)‖ ≤
      m1 t1 * (∫ t, m2 t) * ∫ t, m3 t := fun t1 =>
    norm_iter2_le' hm2 hm3 fun t2 t3 => hb t1 t2 t3
  have := norm_integral_le_of_norm_le ((hm1.mul_const (∫ t, m2 t)).mul_const (∫ t, m3 t))
    (Eventually.of_forall h2)
  rw [integral_mul_const, integral_mul_const] at this
  exact this

/-- The truncated move of the outer line from `a` to `a₀ < a` across the rectangle
`[a₀, a] × [−T, T]`, for a function `Φ'` agreeing with `Φ` on the right edge. -/
theorem trunc_xi (Φ Φ' : ℂ → ℂ → ℂ → ℂ) {a0 a b c T N : ℝ} (ha : a0 ≤ a) (hT : 0 ≤ T)
    (hN : 2 ≤ N) {m2 m3 : ℝ → ℝ} (hm2 : Integrable m2) (hm3 : Integrable m3)
    (hm2n : ∀ t, 0 ≤ m2 t) (hm3n : ∀ t, 0 ≤ m3 t) {K1 Kl Kh : ℝ} (hK1 : 0 ≤ K1)
    (hKl : 0 ≤ Kl) (hKh : 0 ≤ Kh)
    (hc : Continuous fun p : ℝ × ℝ × ℝ => Φ (a + p.1 * I) (b + p.2.1 * I) (c + p.2.2 * I))
    (hb : ∀ t1 t2 t3 : ℝ, ‖Φ (a + t1 * I) (b + t2 * I) (c + t3 * I)‖ ≤
      K1 * nu N t1 * m2 t2 * m3 t3)
    (heq : ∀ t1 t2 t3 : ℝ, |t1| ≤ T →
      Φ (a + t1 * I) (b + t2 * I) (c + t3 * I) = Φ' (a + t1 * I) (b + t2 * I) (c + t3 * I))
    (hd : ∀ t2 t3 : ℝ, DifferentiableOn ℂ (fun ξ => Φ' ξ (b + t2 * I) (c + t3 * I))
      {ξ | a0 ≤ ξ.re ∧ ξ.re ≤ a ∧ |ξ.im| ≤ T})
    (hl : ∀ t1 t2 t3 : ℝ, |t1| ≤ T →
      ‖Φ' (a0 + t1 * I) (b + t2 * I) (c + t3 * I)‖ ≤ Kl * nu 2 t1 * m2 t2 * m3 t3)
    (hh : ∀ x t2 t3 : ℝ, a0 ≤ x → x ≤ a →
      ‖Φ' (x + T * I) (b + t2 * I) (c + t3 * I)‖ ≤ Kh * m2 t2 * m3 t3 ∧
      ‖Φ' (x + (-T) * I) (b + t2 * I) (c + t3 * I)‖ ≤ Kh * m2 t2 * m3 t3) :
    ‖I3 Φ a b c‖ ≤ (Kl * (∫ t, nu 2 t) + 2 * (a - a0) * Kh +
      K1 * (1 + T) ^ (-(N - 2)) * ∫ t, nu 2 t) * (∫ t, m2 t) * ∫ t, m3 t := by
  set f : ℝ → ℝ → ℝ → ℂ := fun t1 t2 t3 => Φ (a + t1 * I) (b + t2 * I) (c + t3 * I) with hf
  have hnuN : Integrable (nu N) := integrable_nu (by linarith)
  have hnu2 : Integrable (nu 2) := integrable_nu (by norm_num)
  have hF : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume)) := by
    refine ((integrable_prod3 hnuN hm2 hm3).const_mul K1).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun p => (hb p.1 p.2.1 p.2.2).trans_eq (by ring))
  set Ψ : ℝ → ℂ := fun t1 => ∫ t2, ∫ t3, f t1 t2 t3 with hΨ
  have hΨi : Integrable Ψ := by
    have h1 : (fun t1 => ∫ q : ℝ × ℝ, f t1 q.1 q.2 ∂(volume.prod volume)) =ᵐ[volume] Ψ := by
      filter_upwards [hF.prod_right_ae] with t1 ht1
      exact integral_prod (fun q : ℝ × ℝ => f t1 q.1 q.2) ht1
    exact (hF.integral_prod_left).congr h1
  have hΨb : ∀ t1, ‖Ψ t1‖ ≤ K1 * nu N t1 * (∫ t, m2 t) * ∫ t, m3 t := fun t1 =>
    norm_iter2_le' hm2 hm3 fun t2 t3 => (hb t1 t2 t3).trans_eq (by ring)
  set s : Set ℝ := Ioc (-T) T with hs
  have hI3 : I3 Φ a b c = ∫ t1, Ψ t1 := rfl
  rw [hI3, ← integral_add_compl (s := s) measurableSet_Ioc hΨi]
  -- the tails
  set g : ℝ → ℝ := fun t => K1 * (1 + T) ^ (-(N - 2)) * nu 2 t * (∫ t, m2 t) * ∫ t, m3 t
  have hm2i : 0 ≤ ∫ t, m2 t := integral_nonneg hm2n
  have hm3i : 0 ≤ ∫ t, m3 t := integral_nonneg hm3n
  have hg : Integrable g :=
    (((hnu2.const_mul (K1 * (1 + T) ^ (-(N - 2)))).mul_const _).mul_const _)
  have hg0 : ∀ t, 0 ≤ g t := fun t => by
    have := nu_nonneg 2 t
    have : 0 ≤ (1 + T) ^ (-(N - 2)) := Real.rpow_nonneg (by linarith) _
    positivity
  have htail : ‖∫ t1 in sᶜ, Ψ t1‖ ≤ K1 * (1 + T) ^ (-(N - 2)) * (∫ t, nu 2 t) *
      (∫ t, m2 t) * ∫ t, m3 t := by
    have h1 : ‖∫ t1 in sᶜ, Ψ t1‖ ≤ ∫ t1 in sᶜ, g t1 := by
      refine norm_integral_le_of_norm_le hg.integrableOn ?_
      refine (ae_restrict_iff' measurableSet_Ioc.compl).2 (Eventually.of_forall fun t ht => ?_)
      have hTt : T ≤ |t| := by
        simp only [hs, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      refine (hΨb t).trans ?_
      have := nu_tail hN hT hTt
      simp only [g]
      have hK : 0 ≤ K1 * (∫ t, m2 t) * ∫ t, m3 t := by positivity
      calc K1 * nu N t * (∫ t, m2 t) * ∫ t, m3 t = (K1 * (∫ t, m2 t) * ∫ t, m3 t) * nu N t := by
            ring
        _ ≤ (K1 * (∫ t, m2 t) * ∫ t, m3 t) * ((1 + T) ^ (-(N - 2)) * nu 2 t) := by gcongr
        _ = _ := by ring
    refine h1.trans ((setIntegral_le_integral hg (Eventually.of_forall hg0)).trans_eq ?_)
    simp only [g]
    rw [integral_mul_const, integral_mul_const, integral_const_mul]
  -- the central part
  have hFs : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
      ((volume.restrict s).prod (volume.prod volume)) := by
    have : ((volume : Measure ℝ).restrict s).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) =
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))).restrict
          (s ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [this]
    exact hF.restrict
  have hcen : ∫ t1 in s, Ψ t1 = ∫ t2, ∫ t3, ∫ t1 in s, f t1 t2 t3 := swap3' hFs
  have hrect : ∀ t2 t3 : ℝ, ‖∫ t1 in s, f t1 t2 t3‖ ≤
      (Kl * (∫ t, nu 2 t) + 2 * (a - a0) * Kh) * m2 t2 * m3 t3 := by
    intro t2 t3
    set h : ℂ → ℂ := fun ξ => Φ' ξ (b + t2 * I) (c + t3 * I) with hh'
    have hTT : -T ≤ T := by linarith
    rw [← intervalIntegral.integral_of_le hTT]
    have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h
      ⟨a0, -T⟩ ⟨a, T⟩ ((hd t2 t3).mono fun z hz => by
        rw [mem_reProdIm, Set.uIcc_of_le ha, Set.uIcc_of_le hTT] at hz
        exact ⟨hz.1.1, hz.1.2, abs_le.2 hz.2⟩)
    have hR' : (∫ x in a0..a, h (x + (-T) * I)) - (∫ x in a0..a, h (x + T * I)) +
        I • (∫ y in (-T)..T, h (a + y * I)) - I • (∫ y in (-T)..T, h (a0 + y * I)) = 0 := by
      simpa using hR
    have hfe : ∫ t1 in (-T)..T, f t1 t2 t3 = ∫ y in (-T)..T, h (a + y * I) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le hTT] at hy
      exact heq y t2 t3 (abs_le.2 hy)
    rw [hfe]
    have hkey : I • (∫ y in (-T)..T, h (a + y * I)) =
        I • (∫ y in (-T)..T, h (a0 + y * I)) - (∫ x in a0..a, h (x + (-T) * I)) +
          ∫ x in a0..a, h (x + T * I) := by
      linear_combination hR'
    have hn : ‖∫ y in (-T)..T, h (a + y * I)‖ ≤ ‖∫ y in (-T)..T, h (a0 + y * I)‖ +
        ‖∫ x in a0..a, h (x + (-T) * I)‖ + ‖∫ x in a0..a, h (x + T * I)‖ := by
      have : ‖∫ y in (-T)..T, h (a + y * I)‖ = ‖I • (∫ y in (-T)..T, h (a + y * I))‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
      rw [this, hkey]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
      rw [norm_smul, Complex.norm_I, one_mul]
    have hl' : ‖∫ y in (-T)..T, h (a0 + y * I)‖ ≤ Kl * (∫ t, nu 2 t) * m2 t2 * m3 t3 := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le hTT
        (g := fun y => Kl * m2 t2 * m3 t3 * nu 2 y)
        (Eventually.of_forall fun y hy => (hl y t2 t3 (abs_le.2 ⟨hy.1.le, hy.2⟩)).trans_eq
          (by ring))
        ((hnu2.const_mul _).intervalIntegrable)
      refine h1.trans ?_
      rw [intervalIntegral.integral_of_le hTT]
      have h2 := setIntegral_le_integral (s := Ioc (-T) T) (hnu2.const_mul (Kl * m2 t2 * m3 t3))
        (Eventually.of_forall fun t => by
          have := nu_nonneg 2 t; have := hm2n t2; have := hm3n t3; positivity)
      rw [integral_const_mul (μ := (volume : Measure ℝ))] at h2
      exact h2.trans_eq (by ring)
    have hhor : ∀ s' ∈ ({T, -T} : Set ℝ), ‖∫ x in a0..a, h (x + s' * I)‖ ≤
        Kh * m2 t2 * m3 t3 * (a - a0) := by
      intro s' hs'
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a0) (b := a)
        (C := Kh * m2 t2 * m3 t3) (f := fun x : ℝ => h (x + s' * I)) (fun x hx => by
          rw [Set.uIoc_of_le ha] at hx
          rcases hs' with rfl | rfl
          · exact (hh x t2 t3 hx.1.le hx.2).1
          · simpa using (hh x t2 t3 hx.1.le hx.2).2)
      rwa [abs_of_nonneg (by linarith)] at this
    have h1 := hhor T (by simp)
    have h2 := hhor (-T) (by simp)
    refine hn.trans ?_
    have h2' : ‖∫ x in a0..a, h (x + (-T) * I)‖ ≤ Kh * m2 t2 * m3 t3 * (a - a0) := by
      simpa using h2
    calc _ ≤ Kl * (∫ t, nu 2 t) * m2 t2 * m3 t3 + Kh * m2 t2 * m3 t3 * (a - a0) +
          Kh * m2 t2 * m3 t3 * (a - a0) := by linarith
      _ = _ := by ring
  have hcb : ‖∫ t1 in s, Ψ t1‖ ≤ (Kl * (∫ t, nu 2 t) + 2 * (a - a0) * Kh) *
      (∫ t, m2 t) * ∫ t, m3 t := by
    rw [hcen]
    exact norm_iter2_le' hm2 hm3 hrect
  refine (norm_add_le _ _).trans ?_
  have := add_le_add hcb htail
  refine this.trans_eq ?_
  ring

end

end L2C

end ArtinPrimitiveRoots
end

section
/-! # C3P_Bound: the principal-row integrand and its majorant

`Phi ξ w z = E(ξ,w,z) M(z) Ŵ(w) ζ(6z) ζ(w) G(ξ,w,z)` with `ζ(s) = R(s)/(s − 1)`, where
`E = X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²}`; `Aw` and `Bz` are the numerators at the poles
`w = 1` and `z = 1/6`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

/-- The `Z`-dependent factor `X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²}` of (7.10). -/
def Ef (X Y Z : ℝ) (ξ w z : ℂ) : ℂ :=
  (X : ℂ) ^ ((1 / 2 : ℂ) - z) * (Z : ℂ) ^ (ξ + z - 1) * (Y : ℂ) ^ (w - 1) * cexp ((ξ + z - 1) ^ 2)

/-! ### Elementary bounds -/

lemma norm_cexp_sq (u : ℂ) : ‖cexp (u ^ 2)‖ = Real.exp (u.re ^ 2 - u.im ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

lemma norm_Ef {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (ξ w z : ℂ) :
    ‖Ef X Y Z ξ w z‖ = X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1) *
      Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) := by
  unfold Ef
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_cpow_eq_rpow_re_of_pos hY, norm_cexp_sq]
  simp

end

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Reg: continuity of the integrand on lines and holomorphy on strips -/

open Complex MeasureTheory Filter Topology Set

set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

lemma continuous_line (c : ℝ) : Continuous fun t : ℝ => (c : ℂ) + t * I := by fun_prop

variable {X Y Z : ℝ} {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ}

section Cont

variable {α : Type*} [TopologicalSpace α] {ξf wf zf : α → ℂ}

lemma cont_Ef (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hξ : Continuous ξf) (hw : Continuous wf) (hz : Continuous zf) :
    Continuous fun x => Ef X Y Z (ξf x) (wf x) (zf x) := by
  unfold Ef
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  refine ((((continuous_const.sub hz).const_cpow (Or.inl hX')).mul
    (((hξ.add hz).sub continuous_const).const_cpow (Or.inl hZ'))).mul
    ((hw.sub continuous_const).const_cpow (Or.inl hY'))).mul ?_
  exact Complex.continuous_exp.comp (((hξ.add hz).sub continuous_const).pow 2)

end Cont

section Diff

end Diff

end

end C3P

end ArtinPrimitiveRoots
end

section
/-! # L2C_Row: the row integrand of (7.10) and its contour moves

`Phi X Y Z M Wh q G ξ w z = X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²} M(z) Ŵ(w) q^{−z} G(ξ,w,z)`.

* `norm_Phi_le`: the pointwise majorant
  `P(Re) q^{−Re z} e^{(Re(ξ+z)−1)²} e^{N²/4} C_M C_W 2^A B · ν_N(Im ξ) ν_2(Im w) ν_2(Im z)`,
  from `‖M‖ ≤ C_M ν_{N+2}`, `‖Ŵ‖ ≤ C_W ν_{A+2}`, `‖G‖ ≤ B (2 + |Im w|)^A`;
* `row_shift`: on a box `[a,a'] × [b,b'] × [c,c']` where `G` is continuous, separately
  holomorphic and polynomially bounded in `Im w`, `I3 Φ a' b' c' = I3 Φ a b c`;
* `row_line_bound`: `‖I3 Φ a b c‖ ≤ X^{1/2−c} Z^{a+c−1} Y^{b−1} q^{−c} · K · B`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L2C

noncomputable section

/-- The row integrand. -/
def Phi (X Y Z : ℝ) (M Wh : ℂ → ℂ) (q : ℕ) (G : ℂ → ℂ → ℂ → ℂ) (ξ w z : ℂ) : ℂ :=
  C3P.Ef X Y Z ξ w z * M z * Wh w * (q : ℂ) ^ (-z) * G ξ w z

/-- The closed box of real parts. -/
def Bx (a a' b b' c c' : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {p | a ≤ p.1.re ∧ p.1.re ≤ a' ∧ b ≤ p.2.1.re ∧ p.2.1.re ≤ b' ∧ c ≤ p.2.2.re ∧ p.2.2.re ≤ c'}

lemma norm_natCast_cpow_neg {q : ℕ} (hq : 1 ≤ q) (z : ℂ) :
    ‖(q : ℂ) ^ (-z)‖ = (q : ℝ) ^ (-z.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

/-- The pointwise majorant. -/
theorem norm_Phi_le {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {q : ℕ} (hq : 1 ≤ q)
    {M Wh : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} {ξ w z : ℂ} {N A CM CW B : ℝ} (hN : 0 ≤ N)
    (hA : 0 ≤ A) (hCM : 0 ≤ CM) (hCW : 0 ≤ CW) (hB : 0 ≤ B)
    (hM : ‖M z‖ ≤ CM * nu (N + 2) z.im) (hW : ‖Wh w‖ ≤ CW * nu (A + 2) w.im)
    (hG : ‖G ξ w z‖ ≤ B * (2 + |w.im|) ^ A) :
    ‖Phi X Y Z M Wh q G ξ w z‖ ≤
      (X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1)) * (q : ℝ) ^ (-z.re) *
        (Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp (N ^ 2 / 4) * CM * CW * 2 ^ A * B) *
        (nu N ξ.im * nu 2 w.im * nu 2 z.im) := by
  unfold Phi
  rw [norm_mul, norm_mul, norm_mul, norm_mul, C3P.norm_Ef hX hY hZ, norm_natCast_cpow_neg hq]
  set P := X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1)
  have hP : 0 ≤ P := by positivity
  have hq' : 0 ≤ (q : ℝ) ^ (-z.re) := by positivity
  have he : Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) =
      Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have hgs := gauss_split hN 2 ξ.im z.im
  have hpw := poly_nu hA w.im
  have h1 : ‖M z‖ * Real.exp (-(ξ.im + z.im) ^ 2) ≤
      CM * (Real.exp (N ^ 2 / 4) * nu N ξ.im * nu 2 z.im) := by
    calc ‖M z‖ * Real.exp (-(ξ.im + z.im) ^ 2) ≤ CM * nu (N + 2) z.im *
          Real.exp (-(ξ.im + z.im) ^ 2) := by gcongr
      _ = CM * (Real.exp (-(ξ.im + z.im) ^ 2) * nu (N + 2) z.im) := by ring
      _ ≤ _ := by gcongr
  have h2 : ‖Wh w‖ * ‖G ξ w z‖ ≤ CW * B * (2 ^ A * nu 2 w.im) := by
    calc ‖Wh w‖ * ‖G ξ w z‖ ≤ (CW * nu (A + 2) w.im) * (B * (2 + |w.im|) ^ A) :=
          mul_le_mul hW hG (norm_nonneg _) (by have := nu_nonneg (A + 2) w.im; positivity)
      _ = CW * B * ((2 + |w.im|) ^ A * nu (A + 2) w.im) := by ring
      _ ≤ _ := by gcongr
  have hE0 : 0 ≤ Real.exp ((ξ.re + z.re - 1) ^ 2) := (Real.exp_pos _).le
  calc P * (Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) * ‖M z‖ *
        ‖Wh w‖ * (q : ℝ) ^ (-z.re) * ‖G ξ w z‖
      = P * (q : ℝ) ^ (-z.re) * Real.exp ((ξ.re + z.re - 1) ^ 2) *
        (‖M z‖ * Real.exp (-(ξ.im + z.im) ^ 2)) * (‖Wh w‖ * ‖G ξ w z‖) := by ring
    _ ≤ P * (q : ℝ) ^ (-z.re) * Real.exp ((ξ.re + z.re - 1) ^ 2) *
        (CM * (Real.exp (N ^ 2 / 4) * nu N ξ.im * nu 2 z.im)) * (CW * B * (2 ^ A * nu 2 w.im)) := by
        have hL : 0 ≤ P * (q : ℝ) ^ (-z.re) * Real.exp ((ξ.re + z.re - 1) ^ 2) := by positivity
        have hY1 : 0 ≤ CM * (Real.exp (N ^ 2 / 4) * nu N ξ.im * nu 2 z.im) := by
          have := nu_nonneg N ξ.im; have := nu_nonneg 2 z.im; positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hL) h2
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hL hY1)
    _ = _ := by ring

/-! ### Continuity and holomorphy of the integrand -/

section Reg

variable {X Y Z : ℝ} {M Wh : ℂ → ℂ} {q : ℕ} {G : ℂ → ℂ → ℂ → ℂ}

lemma cont_Phi {α : Type*} [TopologicalSpace α] {S : Set (ℂ × ℂ × ℂ)}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hq : 1 ≤ q)
    (hM : DifferentiableOn ℂ M {z | 0 < z.re}) (hW : Differentiable ℂ Wh)
    (hGc : ContinuousOn (fun p : ℂ × ℂ × ℂ => G p.1 p.2.1 p.2.2) S)
    {ξf wf zf : α → ℂ} (hξ : Continuous ξf) (hw : Continuous wf) (hz : Continuous zf)
    (hz0 : ∀ x, 0 < (zf x).re) (hm : ∀ x, (ξf x, wf x, zf x) ∈ S) :
    Continuous fun x => Phi X Y Z M Wh q G (ξf x) (wf x) (zf x) := by
  unfold Phi
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hG : Continuous fun x => G (ξf x) (wf x) (zf x) :=
    hGc.comp_continuous (hξ.prodMk (hw.prodMk hz)) hm
  have hMc : Continuous fun x => M (zf x) := hM.continuousOn.comp_continuous hz hz0
  exact ((((C3P.cont_Ef hX hY hZ hξ hw hz).mul hMc).mul (hW.continuous.comp hw)).mul
    (hz.neg.const_cpow (Or.inl hq'))).mul hG

lemma diffAt_M' (hM : DifferentiableOn ℂ M {z | 0 < z.re}) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ M z :=
  hM.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

lemma diff_Phi_xi (hZ : 0 < Z) {w z : ℂ} {S : Set ℂ}
    (hG : ∀ ξ ∈ S, DifferentiableAt ℂ (fun x => G x w z) ξ) :
    DifferentiableOn ℂ (fun ξ => Phi X Y Z M Wh q G ξ w z) S := by
  intro ξ hξ
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Phi C3P.Ef
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have h1 : DifferentiableAt ℂ (fun ξ : ℂ => (Z : ℂ) ^ (ξ + z - 1)) ξ :=
    ((differentiableAt_id.add_const z).sub_const 1).const_cpow (Or.inl hZ')
  have h2 : DifferentiableAt ℂ (fun ξ : ℂ => cexp ((ξ + z - 1) ^ 2)) ξ :=
    (((differentiableAt_id.add_const z).sub_const 1).pow 2).cexp
  exact ((((((differentiableAt_const _).mul h1).mul (differentiableAt_const _)).mul h2).mul
    (differentiableAt_const _)).mul (differentiableAt_const _)).mul
    (differentiableAt_const _) |>.mul (hG ξ hξ)

lemma diff_Phi_w (hY : 0 < Y) (hW : Differentiable ℂ Wh) {ξ z : ℂ} {S : Set ℂ}
    (hG : ∀ w ∈ S, DifferentiableAt ℂ (fun x => G ξ x z) w) :
    DifferentiableOn ℂ (fun w => Phi X Y Z M Wh q G ξ w z) S := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Phi C3P.Ef
  have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ (w - 1)) w :=
    (differentiableAt_id.sub_const 1).const_cpow (Or.inl hY')
  exact ((((((differentiableAt_const _).mul (differentiableAt_const _)).mul h1).mul
    (differentiableAt_const _)).mul (differentiableAt_const _)).mul (hW w)).mul
    (differentiableAt_const _) |>.mul (hG w hw)

lemma diff_Phi_z (hX : 0 < X) (hZ : 0 < Z) (hq : 1 ≤ q)
    (hM : DifferentiableOn ℂ M {z | 0 < z.re}) {ξ w : ℂ} {S : Set ℂ}
    (hz0 : ∀ z ∈ S, 0 < z.re) (hG : ∀ z ∈ S, DifferentiableAt ℂ (fun x => G ξ w x) z) :
    DifferentiableOn ℂ (fun z => Phi X Y Z M Wh q G ξ w z) S := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Phi C3P.Ef
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h0 : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ ((1 / 2 : ℂ) - z)) z :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hX')
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) z :=
    (((differentiableAt_const _).add differentiableAt_id).sub_const 1).const_cpow (Or.inl hZ')
  have h2 : DifferentiableAt ℂ (fun z : ℂ => cexp ((ξ + z - 1) ^ 2)) z :=
    ((((differentiableAt_const _).add differentiableAt_id).sub_const 1).pow 2).cexp
  have h3 : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl hq')
  exact ((((((h0.mul h1).mul (differentiableAt_const _)).mul h2).mul
    (diffAt_M' hM (hz0 z hz))).mul (differentiableAt_const _)).mul h3).mul (hG z hz)

end Reg

/-! ### The box move -/

lemma sq_le_of_mem {x l u : ℝ} (h1 : l ≤ x) (h2 : x ≤ u) : x ^ 2 ≤ l ^ 2 + u ^ 2 := by
  rcases le_total 0 x with h | h
  · nlinarith [sq_nonneg l]
  · nlinarith [sq_nonneg u]

/-- On a box where `G` is continuous, separately holomorphic and `≤ B (2 + |Im w|)^A`, the triple
line integral moves from the corner `(a', b', c')` to `(a, b, c)` (first `ξ`, then `z`, then `w`). -/
theorem row_shift {X Y Z : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hZ : 1 ≤ Z) {q : ℕ} (hq : 1 ≤ q)
    {M Wh : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} {a a' b b' c c' A B CM CW : ℝ}
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c') (hc0 : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hCM : 0 ≤ CM) (hCW : 0 ≤ CW)
    (hM : DifferentiableOn ℂ M {z | 0 < z.re})
    (hMd : ∀ z : ℂ, c ≤ z.re → z.re ≤ c' → ‖M z‖ ≤ CM * nu 4 z.im)
    (hW : Differentiable ℂ Wh)
    (hWd : ∀ w : ℂ, b ≤ w.re → w.re ≤ b' → ‖Wh w‖ ≤ CW * nu (A + 2) w.im)
    (hGc : ContinuousOn (fun p : ℂ × ℂ × ℂ => G p.1 p.2.1 p.2.2) (Bx a a' b b' c c'))
    (hGd : ∀ p ∈ Bx a a' b b' c c', DifferentiableAt ℂ (fun x => G x p.2.1 p.2.2) p.1 ∧
      DifferentiableAt ℂ (fun x => G p.1 x p.2.2) p.2.1 ∧
      DifferentiableAt ℂ (fun x => G p.1 p.2.1 x) p.2.2)
    (hGb : ∀ p ∈ Bx a a' b b' c c', ‖G p.1 p.2.1 p.2.2‖ ≤ B * (2 + |p.2.1.im|) ^ A) :
    I3 (Phi X Y Z M Wh q G) a' b' c' = I3 (Phi X Y Z M Wh q G) a b c := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  set Φ := Phi X Y Z M Wh q G with hΦ
  set Kbox := X ^ (1 / 2 - c) * Z ^ (a' + c' - 1) * Y ^ (b' - 1) *
    (Real.exp ((a + c - 1) ^ 2 + (a' + c' - 1) ^ 2) * Real.exp ((2 : ℝ) ^ 2 / 4) * CM * CW *
      2 ^ A * B) with hK
  have hK0 : 0 ≤ Kbox := by positivity
  have hbox : ∀ ξ w z : ℂ, (ξ, w, z) ∈ Bx a a' b b' c c' →
      ‖Φ ξ w z‖ ≤ Kbox * nu 2 ξ.im * nu 2 w.im * nu 2 z.im := by
    intro ξ w z hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    have hb := norm_Phi_le (N := 2) hX0 hY0 hZ0 hq (by norm_num) hA hCM hCW hB
      (by simpa [show (2 : ℝ) + 2 = 4 by norm_num] using hMd z h5 h6) (hWd w h3 h4)
      (hGb (ξ, w, z) ⟨h1, h2, h3, h4, h5, h6⟩)
    refine hb.trans ?_
    have e1 : X ^ (1 / 2 - z.re) ≤ X ^ (1 / 2 - c) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have e2 : Z ^ (ξ.re + z.re - 1) ≤ Z ^ (a' + c' - 1) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have e3 : Y ^ (w.re - 1) ≤ Y ^ (b' - 1) := Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    have e4 : (q : ℝ) ^ (-z.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq) (by linarith)
    have e5 : Real.exp ((ξ.re + z.re - 1) ^ 2) ≤ Real.exp ((a + c - 1) ^ 2 + (a' + c' - 1) ^ 2) :=
      Real.exp_le_exp.2 (sq_le_of_mem (by linarith) (by linarith))
    have hn : 0 ≤ nu 2 ξ.im * nu 2 w.im * nu 2 z.im := by
      have := nu_nonneg 2 ξ.im; have := nu_nonneg 2 w.im; have := nu_nonneg 2 z.im; positivity
    calc X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1) * (q : ℝ) ^ (-z.re) *
          (Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp ((2 : ℝ) ^ 2 / 4) * CM * CW * 2 ^ A * B) *
          (nu 2 ξ.im * nu 2 w.im * nu 2 z.im)
        ≤ X ^ (1 / 2 - c) * Z ^ (a' + c' - 1) * Y ^ (b' - 1) * 1 *
          (Real.exp ((a + c - 1) ^ 2 + (a' + c' - 1) ^ 2) * Real.exp ((2 : ℝ) ^ 2 / 4) * CM * CW *
            2 ^ A * B) * (nu 2 ξ.im * nu 2 w.im * nu 2 z.im) := by gcongr
      _ = _ := by rw [hK]; ring
  have hnu := integrable_nu (N := 2) (by norm_num)
  have hnt := tendsto_nu_atTop (N := 2) (by norm_num)
  have hnb := tendsto_nu_atBot (N := 2) (by norm_num)
  have hlre : ∀ x t : ℝ, ((x : ℂ) + t * I).re = x := fun x t => by simp
  have hlim : ∀ x t : ℝ, ((x : ℂ) + t * I).im = t := fun x t => by simp
  -- step 1: ξ from a' to a at (b', c')
  have s1 : I3 Φ a b' c' = I3 Φ a' b' c' := by
    refine shift_xi Φ haa (m1 := fun t => Kbox * nu 2 t) (m2 := nu 2) (m3 := nu 2)
      (hnu.const_mul _) (by simpa using hnt.const_mul Kbox) (by simpa using hnb.const_mul Kbox)
      hnu hnu ?_ ?_ ?_
    · intro x hx
      have hx' : a ≤ x ∧ x ≤ a' := by
        rcases hx with rfl | rfl
        · exact ⟨le_rfl, haa⟩
        · exact ⟨haa, le_rfl⟩
      refine cont_Phi hX0 hY0 hZ0 hq hM hW hGc ((C3P.continuous_line x).comp continuous_fst)
        ((C3P.continuous_line b').comp (continuous_fst.comp continuous_snd))
        ((C3P.continuous_line c').comp (continuous_snd.comp continuous_snd))
        (fun p => by simp; linarith) (fun p => ?_)
      simp only [Function.comp, Bx, mem_ofPred_eq, hlre]
      exact ⟨hx'.1, hx'.2, hbb, le_rfl, hcc, le_rfl⟩
    · intro t2 t3
      refine diff_Phi_xi hZ0 fun ξ hξ => ?_
      exact (hGd (ξ, (b' : ℂ) + t2 * I, (c' : ℂ) + t3 * I) ⟨hξ.1, hξ.2, by simp [hbb], by simp, by simp [hcc], by simp⟩).1
    · intro ξ t2 t3 h1 h2
      have := hbox ξ ((b' : ℂ) + t2 * I) ((c' : ℂ) + t3 * I) ⟨h1, h2, by simp [hbb], by simp, by simp [hcc], by simp⟩
      simpa [hlim] using this
  -- step 2: z from c' to c at (a, b')
  have s2 : I3 Φ a b' c = I3 Φ a b' c' := by
    refine shift_z Φ hcc (m1 := fun t => Kbox * nu 2 t) (m2 := nu 2) (m3 := nu 2) hnu hnt hnb
      ?_ ?_
    · intro t1 t2
      refine diff_Phi_z hX0 hZ0 hq hM (fun z hz => by linarith [hz.1]) fun z hz => ?_
      exact (hGd ((a : ℂ) + t1 * I, (b' : ℂ) + t2 * I, z) ⟨by simp, by simp [haa], by simp [hbb], by simp, hz.1, hz.2⟩).2.2
    · intro t1 t2 z h1 h2
      have := hbox ((a : ℂ) + t1 * I) ((b' : ℂ) + t2 * I) z ⟨by simp, by simp [haa], by simp [hbb], by simp, h1, h2⟩
      simpa [hlim] using this
  -- step 3: w from b' to b at (a, c)
  have s3 : I3 Φ a b c = I3 Φ a b' c := by
    refine shift_w Φ hbb (m1 := fun t => Kbox * nu 2 t) (m2 := nu 2) (m3 := nu 2) hnu hnt hnb
      hnu ?_ ?_ ?_
    · intro t1 x hx
      have hx' : b ≤ x ∧ x ≤ b' := by
        rcases hx with rfl | rfl
        · exact ⟨le_rfl, hbb⟩
        · exact ⟨hbb, le_rfl⟩
      refine cont_Phi hX0 hY0 hZ0 hq hM hW hGc continuous_const
        ((C3P.continuous_line x).comp continuous_fst)
        ((C3P.continuous_line c).comp continuous_snd)
        (fun p => by simp; linarith) (fun p => ?_)
      simp only [Function.comp, Bx, mem_ofPred_eq, hlre]
      exact ⟨le_rfl, haa, hx'.1, hx'.2, le_rfl, hcc⟩
    · intro t1 t3
      refine diff_Phi_w hY0 hW fun w hw => ?_
      exact (hGd ((a : ℂ) + t1 * I, w, (c : ℂ) + t3 * I) ⟨by simp, by simp [haa], hw.1, hw.2, by simp, by simp [hcc]⟩).2.1
    · intro t1 t3 w h1 h2
      have := hbox ((a : ℂ) + t1 * I) w ((c : ℂ) + t3 * I) ⟨by simp, by simp [haa], h1, h2, by simp, by simp [hcc]⟩
      simpa [hlim] using this
  rw [← s1, ← s2, ← s3]

/-- The bound on the final lines. -/
theorem row_line_bound {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {q : ℕ} (hq : 1 ≤ q)
    {M Wh : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} {a b c A B CM CW : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hCM : 0 ≤ CM) (hCW : 0 ≤ CW)
    (hMd : ∀ t : ℝ, ‖M (c + t * I)‖ ≤ CM * nu 4 t)
    (hWd : ∀ t : ℝ, ‖Wh (b + t * I)‖ ≤ CW * nu (A + 2) t)
    (hGb : ∀ t1 t2 t3 : ℝ, ‖G (a + t1 * I) (b + t2 * I) (c + t3 * I)‖ ≤ B * (2 + |t2|) ^ A) :
    ‖I3 (Phi X Y Z M Wh q G) a b c‖ ≤
      X ^ (1 / 2 - c) * Z ^ (a + c - 1) * Y ^ (b - 1) * (q : ℝ) ^ (-c) *
        (Real.exp ((a + c - 1) ^ 2) * Real.exp 1 * CM * CW * 2 ^ A * (∫ t, nu 2 t) ^ 3) * B := by
  have hnu := integrable_nu (N := 2) (by norm_num)
  set K := X ^ (1 / 2 - c) * Z ^ (a + c - 1) * Y ^ (b - 1) * (q : ℝ) ^ (-c) *
    (Real.exp ((a + c - 1) ^ 2) * Real.exp ((2 : ℝ) ^ 2 / 4) * CM * CW * 2 ^ A * B)
  have h := norm_I3_le (Phi X Y Z M Wh q G) a b c (m1 := fun t => K * nu 2 t) (m2 := nu 2)
    (m3 := nu 2) (hnu.const_mul K) hnu hnu fun t1 t2 t3 => by
      have := norm_Phi_le (N := 2) hX hY hZ hq (ξ := (a : ℂ) + t1 * I) (w := (b : ℂ) + t2 * I)
        (z := (c : ℂ) + t3 * I) (by norm_num) hA hCM hCW hB
        (by simpa [show (2 : ℝ) + 2 = 4 by norm_num] using hMd t3) (by simpa using hWd t2)
        (by simpa using hGb t1 t2 t3)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add] at this
      refine this.trans_eq ?_
      simp only [K]; ring
  refine h.trans_eq ?_
  rw [integral_const_mul]
  simp only [K]
  norm_num
  ring

end

end L2C

end ArtinPrimitiveRoots
end

section
/-! # L2C_Cuts: the candidate cuts beneath C4 = (8.21)

Three statements of the paper, in the bundle's language:

* `RowFactorization` — Proposition 7.3 (7.12)–(7.13) for every frequency `u ≠ 1`, first region:
  `ℱ_u(ξ,w,z) · L^S(ξ, ηχ•(u)) = ζ^S(6z) · L^S(w, χ•(u)) · ℋ_u(ξ,w,z)` initially, with `ℋ_u`
  holomorphic on the first region of (7.13) enlarged by `10⁻⁵` and `ℋ_u ≪_ε q_u^ε` there.
* `KummerConvexity` — (8.14) (Lemma 3.3 + the convexity bound (8.3)): for `u ≠ 1`,
  `L^S(w, χ•(u))` continues to an entire function with
  `L^S(w, χ•(u)) ≪_ε q_u^{1/2+ε} (2 + |Im w|)^A` on `.003 ≤ Re w ≤ 4`.
* `ZeroDetector` — Proposition 8.2 (8.4): exceptional sets `E(U)` with `|E(U)| ≪ U^{1/2}`; for the
  other rows of the dyad `U ≤ q_u < 2U`, `L^S(ξ, ηχ•(u))⁻¹` continues to the rectangle and is
  `≪_ε U^ε` on `Re ξ ≥ .998`, `|Im ξ| ≤ 2U^ρ`.

The two `L`-series are written as sums over the exterior ideals; `χ•(u)(𝔞) = χ_𝔞(u)` is
`residueSymbol ι 𝔪 𝔞 u`, which vanishes on ideals meeting `(u)R`. -/

open NumberField

namespace ArtinPrimitiveRoots

namespace L2C

variable {F : Type*} [Field F] [NumberField F]

/-- **Proposition 7.3 for `u ≠ 1`, first region** (7.12)–(7.13), pp. 46–50. -/
def RowFactorization (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
      ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → ∃ H : ℂ → ℂ → ℂ → ℂ,
        DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) regionOne ∧
        (∀ p ∈ regionOne, ‖H p.1 p.2.1 p.2.2‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ ε) ∧
        ∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
          χ.freqSeries g (freqElt g r) ξ w z * twistedL ι χ (freqElt g r) ξ =
            zetaSF 𝔪 (6 * z) * kummerL ι 𝔪 (freqElt g r) w * H ξ w z

/-- **(8.14)** (Lemma 3.3 and the convexity bound (8.3)), p. 56: for `u ≠ 1` the numerator
`L^S(w, χ•(u))` is entire and `≪_ε q_u^{1/2+ε} (2 + |Im w|)^{A}` on `.003 ≤ Re w ≤ 4`. -/
def KummerConvexity (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ g : AllowedGen ι 𝔪, ∃ A : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
        (∀ w : ℂ, 1 < w.re → Λ w = kummerL ι 𝔪 (freqElt g r) w) ∧
        ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
          ‖Λ w‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + ε) * (2 + |w.im|) ^ A

/-- **Proposition 8.2, (8.4)**, pp. 53–55: there are `ρ > 0`, `U₀` and sets `E(U)` with
`|E(U)| ≪ U^{1/2}` such that for every other row `u ≠ 1` of the dyad `U ≤ q_u < 2U` (`U ≥ U₀`),
`L^S(ξ, ηχ•(u))⁻¹` continues holomorphically to `Re ξ > .997, |Im ξ| < 3U^ρ` and is
`≪_ε U^ε` on `Re ξ ≥ .998, |Im ξ| ≤ 2U^ρ`. -/
def ZeroDetector (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
      ∃ E : ℝ → Finset (FreqClass 𝔪),
        (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 →
          U ≤ (Ideal.absNorm r.1.1 : ℝ) → (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
          ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < 3 * U ^ ρ} ∧
            (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < 3 * U ^ ρ →
              D ξ * twistedL ι χ (freqElt g r) ξ = 1) ∧
            ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → ‖D ξ‖ ≤ C * U ^ ε

end L2C

end ArtinPrimitiveRoots
end

section
/-! # L2C_RowBounds: one nonprincipal row, on the scales `(X, Y) = (Z^{.9}, Z^{.133})`

The row function is `G = ζ^S(6z) Λ(w) ℋ(ξ,w,z) / L(ξ)` (`Gf`), with the hypotheses `RowHyp`:
`ζ^S` holomorphic on `Re s > 1` and `≤ B_Z` on `Re s ≥ 12/5`; `Λ` entire and
`≤ B_Λ (2 + |Im w|)^A` on `.003 ≤ Re w ≤ 4`; `ℋ` holomorphic and `≤ B_H` on `regionOne`; `L`
holomorphic and nonzero on `Re ξ > 1` with `‖L⁻¹‖ ≤ B_L` on `Re ξ ≥ σ₁ = 1.0001`.

* `row_move`: `I3 Φ 4 4 2 = I3 Φ σ₁ .003 .4` (the moves of (8.15)) and `I3 Φ 4 4 2 = I3 Φ 4 4 R₀`
  (the move of (8.20), `R₀ = 10⁶`);
* `row_bound_small`: (8.15), `‖I3 Φ σ₁ .003 .4‖ ≤ K Z^{e₁} q^{−.4} B_Z B_Λ B_H B_L`,
  `e₁ = σ₁ − .642601`;
* `row_bound_large`: (8.20), `‖I3 Φ 4 4 R₀‖ ≤ K Z^{3.849 + R₀/10} q^{−R₀} B_Z B_Λ B_H B_L`;
* `row_bound_good`: (8.17)–(8.19), the truncated move to `Re ξ = .998` with a continuation `D` of
  `1/L` to the rectangle of height `T`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L2C

noncomputable section

/-- `σ₁`. -/
def s1 : ℝ := 10001 / 10000

/-- `R₀`. -/
def R0 : ℝ := 1000000

/-- The row function `ζ^S(6z) Λ(w) ℋ(ξ,w,z) L(ξ)⁻¹`. -/
def Gf (Zs Λ Lt : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) (ξ w z : ℂ) : ℂ :=
  Zs (6 * z) * Λ w * H ξ w z * (Lt ξ)⁻¹

/-- The open set on which `Gf` is regular. -/
def O1 : Set (ℂ × ℂ × ℂ) :=
  {p | 1 < p.1.re ∧ 299 / 100000 < p.2.1.re ∧ 39999 / 100000 < p.2.2.re}

structure RowHyp (Zs Λ Lt : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) (A BZ BΛ BH BL : ℝ) : Prop where
  hZd : DifferentiableOn ℂ Zs {s | 1 < s.re}
  hZb : ∀ s : ℂ, 12 / 5 ≤ s.re → ‖Zs s‖ ≤ BZ
  hΛd : Differentiable ℂ Λ
  hΛb : ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 → ‖Λ w‖ ≤ BΛ * (2 + |w.im|) ^ A
  hHd : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) regionOne
  hHb : ∀ p ∈ regionOne, ‖H p.1 p.2.1 p.2.2‖ ≤ BH
  hLd : DifferentiableOn ℂ Lt {s | 1 < s.re}
  hL0 : ∀ s : ℂ, 1 < s.re → Lt s ≠ 0
  hLb : ∀ s : ℂ, s1 ≤ s.re → ‖(Lt s)⁻¹‖ ≤ BL
  hA : 0 ≤ A
  hBZ : 0 ≤ BZ
  hBΛ : 0 ≤ BΛ
  hBH : 0 ≤ BH
  hBL : 0 ≤ BL

lemma O1_sub {p : ℂ × ℂ × ℂ} (hp : p ∈ O1) : p ∈ regionOne :=
  ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩

lemma isOpen_regionOne : IsOpen regionOne := by
  have h1 : IsOpen {p : ℂ × ℂ × ℂ | 99799 / 100000 < p.1.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have h2 : IsOpen {p : ℂ × ℂ × ℂ | 299 / 100000 < p.2.1.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))
  have h3 : IsOpen {p : ℂ × ℂ × ℂ | 39999 / 100000 < p.2.2.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))
  exact h1.inter (h2.inter h3)

section Reg

variable {Zs Λ Lt : ℂ → ℂ} {H : ℂ → ℂ → ℂ → ℂ} {A BZ BΛ BH BL : ℝ}

lemma H_at (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {p : ℂ × ℂ × ℂ} (hp : p ∈ regionOne) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) p :=
  h.hHd.differentiableAt (isOpen_regionOne.mem_nhds hp)

lemma H_xi (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {ξ w z : ℂ} (hp : (ξ, w, z) ∈ regionOne) :
    DifferentiableAt ℂ (fun x => H x w z) ξ := by
  have := (H_at h hp).comp ξ (f := fun x : ℂ => (x, w, z))
    ((differentiableAt_id.prodMk (differentiableAt_const _)))
  exact this

lemma H_w (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {ξ w z : ℂ} (hp : (ξ, w, z) ∈ regionOne) :
    DifferentiableAt ℂ (fun x => H ξ x z) w := by
  have := (H_at h hp).comp w (f := fun x : ℂ => (ξ, x, z))
    ((differentiableAt_const _).prodMk (differentiableAt_id.prodMk (differentiableAt_const _)))
  exact this

lemma H_z (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {ξ w z : ℂ} (hp : (ξ, w, z) ∈ regionOne) :
    DifferentiableAt ℂ (fun x => H ξ w x) z := by
  have := (H_at h hp).comp z (f := fun x : ℂ => (ξ, w, x))
    ((differentiableAt_const _).prodMk ((differentiableAt_const _).prodMk differentiableAt_id))
  exact this

lemma isOpen_re_gt (c : ℝ) : IsOpen {s : ℂ | c < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

lemma Zs6_at (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {z : ℂ} (hz : 1 / 6 < z.re) :
    DifferentiableAt ℂ (fun x => Zs (6 * x)) z := by
  have h6 : 1 < (6 * z).re := by simp; linarith
  exact ((h.hZd.differentiableAt ((isOpen_re_gt 1).mem_nhds h6)).comp z
    (differentiableAt_id.const_mul 6))

lemma Lt_at (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {ξ : ℂ} (hξ : 1 < ξ.re) :
    DifferentiableAt ℂ (fun x => (Lt x)⁻¹) ξ :=
  (h.hLd.differentiableAt ((isOpen_re_gt 1).mem_nhds hξ)).inv (h.hL0 ξ hξ)

lemma Gf_cont (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => Gf Zs Λ Lt H p.1 p.2.1 p.2.2) O1 := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  unfold Gf
  have hz : 1 / 6 < p.2.2.re := by linarith [hp.2.2]
  have h1 : ContinuousAt (fun p : ℂ × ℂ × ℂ => Zs (6 * p.2.2)) p :=
    ContinuousAt.comp (g := fun x => Zs (6 * x)) (f := fun p : ℂ × ℂ × ℂ => p.2.2) (x := p)
      (Zs6_at h hz).continuousAt (by fun_prop)
  have h2 : ContinuousAt (fun p : ℂ × ℂ × ℂ => Λ p.2.1) p :=
    (h.hΛd.continuous.comp (continuous_fst.comp continuous_snd)).continuousAt
  have h3 : ContinuousAt (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) p :=
    (H_at h (O1_sub hp)).continuousAt
  have h4 : ContinuousAt (fun p : ℂ × ℂ × ℂ => (Lt p.1)⁻¹) p :=
    (Lt_at h hp.1).continuousAt.comp continuous_fst.continuousAt
  exact ((h1.mul h2).mul h3).mul h4

lemma Gf_diff (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {p : ℂ × ℂ × ℂ} (hp : p ∈ O1) :
    DifferentiableAt ℂ (fun x => Gf Zs Λ Lt H x p.2.1 p.2.2) p.1 ∧
      DifferentiableAt ℂ (fun x => Gf Zs Λ Lt H p.1 x p.2.2) p.2.1 ∧
      DifferentiableAt ℂ (fun x => Gf Zs Λ Lt H p.1 p.2.1 x) p.2.2 := by
  obtain ⟨ξ, w, z⟩ := p
  have hr : (ξ, w, z) ∈ regionOne := O1_sub hp
  have hz : 1 / 6 < z.re := by linarith [hp.2.2]
  unfold Gf
  refine ⟨?_, ?_, ?_⟩
  · exact ((differentiableAt_const _).mul (H_xi h hr)).mul (Lt_at h hp.1)
  · exact (((differentiableAt_const _).mul (h.hΛd w)).mul (H_w h hr)).mul
      (differentiableAt_const _)
  · exact (((Zs6_at h hz).mul (differentiableAt_const _)).mul (H_z h hr)).mul
      (differentiableAt_const _)

lemma Gf_bound (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {ξ w z : ℂ} (hξ : s1 ≤ ξ.re)
    (hw1 : 3 / 1000 ≤ w.re) (hw2 : w.re ≤ 4) (hz : 2 / 5 ≤ z.re) :
    ‖Gf Zs Λ Lt H ξ w z‖ ≤ (BZ * BΛ * BH * BL) * (2 + |w.im|) ^ A := by
  unfold Gf
  have hp : (ξ, w, z) ∈ regionOne := ⟨by unfold s1 at hξ; linarith, by linarith, by linarith⟩
  have h1 := h.hZb (6 * z) (by simp; linarith)
  have h2 := h.hΛb w hw1 hw2
  have h3 := h.hHb _ hp
  have h4 := h.hLb ξ hξ
  rw [norm_mul, norm_mul, norm_mul]
  have := h.hBZ; have := h.hBΛ; have := h.hBH; have := h.hBL
  have hp2 : 0 ≤ (2 + |w.im|) ^ A := by positivity
  calc ‖Zs (6 * z)‖ * ‖Λ w‖ * ‖H ξ w z‖ * ‖(Lt ξ)⁻¹‖
      ≤ BZ * (BΛ * (2 + |w.im|) ^ A) * BH * BL := by gcongr
    _ = _ := by ring

end Reg

/-! ### The weights -/

/-- The hypotheses on the weights: `M` a Mellin weight, `Ŵ` entire with rapid decay on strips. -/
structure WeightHyp (M Wh : ℂ → ℂ) : Prop where
  hM : IsMellinWeight M
  hW : Differentiable ℂ Wh
  hWd : ∀ A' a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Wh s‖ ≤ C * (1 + |s.im|) ^ (-A')

lemma WeightHyp.M_nu {M Wh : ℂ → ℂ} (hw : WeightHyp M Wh) (N a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖M z‖ ≤ C * nu N z.im := by
  obtain ⟨C, hC⟩ := hw.hM.2 a b N ha
  exact ⟨max C 0, le_max_right _ _, fun z h1 h2 =>
    (hC z h1 h2).trans (by unfold nu; gcongr; exact le_max_left _ _)⟩

lemma WeightHyp.W_nu {M Wh : ℂ → ℂ} (hw : WeightHyp M Wh) (N a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖Wh w‖ ≤ C * nu N w.im := by
  obtain ⟨C, hC⟩ := hw.hWd N a b
  exact ⟨max C 0, le_max_right _ _, fun z h1 h2 =>
    (hC z h1 h2).trans (by unfold nu; gcongr; exact le_max_left _ _)⟩

/-! ### Powers of `Z` -/

lemma zpow3 {Z : ℝ} (hZ : 0 < Z) (α β γ : ℝ) :
    (Z ^ (9 / 10 : ℝ)) ^ α * Z ^ β * (Z ^ (133 / 1000 : ℝ)) ^ γ =
      Z ^ (9 / 10 * α + β + 133 / 1000 * γ) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ]

lemma one_le_rpow' {Z : ℝ} (hZ : 1 ≤ Z) {e : ℝ} (he : 0 ≤ e) : 1 ≤ Z ^ e :=
  Real.one_le_rpow hZ he

/-! ### The moves -/

variable {M Wh : ℂ → ℂ} {Zs Λ Lt : ℂ → ℂ} {H : ℂ → ℂ → ℂ → ℂ} {A BZ BΛ BH BL : ℝ}

lemma s1_gt : 1 < s1 := by unfold s1; norm_num

lemma box_sub_O1 {a a' b b' c c' : ℝ} (ha : 1 < a) (hb : 299 / 100000 < b) (hc : 39999 / 100000 < c)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ Bx a a' b b' c c') : p ∈ O1 :=
  ⟨by linarith [hp.1], by linarith [hp.2.2.1], by linarith [hp.2.2.2.2.1]⟩

theorem row_move (hw : WeightHyp M Wh) (h : RowHyp Zs Λ Lt H A BZ BΛ BH BL) {q : ℕ} (hq : 1 ≤ q)
    {Z : ℝ} (hZ : 1 ≤ Z) :
    I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) 4 4 2 =
        I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) s1
          (3 / 1000) (2 / 5) ∧
      I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) 4 4 2 =
        I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) 4 4 R0 := by
  have hX : 1 ≤ Z ^ (9 / 10 : ℝ) := one_le_rpow' hZ (by norm_num)
  have hY : 1 ≤ Z ^ (133 / 1000 : ℝ) := one_le_rpow' hZ (by norm_num)
  have hs1 := s1_gt
  have hB0 : 0 ≤ BZ * BΛ * BH * BL := by
    have := h.hBZ; have := h.hBΛ; have := h.hBH; have := h.hBL; positivity
  have hs4 : s1 ≤ 4 := by unfold s1; norm_num
  constructor
  · obtain ⟨CM, hCM, hMd⟩ := hw.M_nu 4 (2 / 5) 2 (by norm_num)
    obtain ⟨CW, hCW, hWd⟩ := hw.W_nu (A + 2) (3 / 1000) 4
    refine row_shift hX hY hZ hq (B := BZ * BΛ * BH * BL) (a := s1) (a' := 4) (b := 3 / 1000)
      (b' := 4) (c := 2 / 5) (c' := 2) hs4 (by norm_num)
      (by norm_num) (by norm_num) h.hA hB0 hCM hCW hw.hM.1 hMd hw.hW hWd
      ((Gf_cont h).mono fun p hp => box_sub_O1 hs1 (by norm_num) (by norm_num) hp)
      (fun p hp => Gf_diff h (box_sub_O1 hs1 (by norm_num) (by norm_num) hp)) fun p hp => ?_
    exact Gf_bound h hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
  · obtain ⟨CM, hCM, hMd⟩ := hw.M_nu 4 2 R0 (by norm_num)
    obtain ⟨CW, hCW, hWd⟩ := hw.W_nu (A + 2) 4 4
    refine (row_shift hX hY hZ hq (B := BZ * BΛ * BH * BL) (a := 4) (a' := 4) (b := 4) (b' := 4)
      (c := 2) (c' := R0) le_rfl le_rfl (by unfold R0; norm_num) (by norm_num) h.hA
      hB0 hCM hCW
      hw.hM.1 hMd hw.hW hWd
      ((Gf_cont h).mono fun p hp => box_sub_O1 (by norm_num) (by norm_num) (by norm_num) hp)
      (fun p hp => Gf_diff h (box_sub_O1 (by norm_num) (by norm_num) (by norm_num) hp))
      fun p hp => ?_).symm
    exact Gf_bound h (by unfold s1 at *; linarith [hp.1]) (by linarith [hp.2.2.1]) hp.2.2.2.1
      (by linarith [hp.2.2.2.2.1])

/-- (8.15): the bound on the lines `(σ₁, .003, .4)`. -/
theorem row_bound_small (hw : WeightHyp M Wh) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Zs Λ Lt : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) (BZ BΛ BH BL : ℝ),
      RowHyp Zs Λ Lt H A BZ BΛ BH BL → ∀ (q : ℕ), 1 ≤ q → ∀ Z : ℝ, 1 ≤ Z →
        ‖I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) s1
          (3 / 1000) (2 / 5)‖ ≤
          K * Z ^ (s1 - 642601 / 1000000) * (q : ℝ) ^ (-(2 / 5 : ℝ)) * (BZ * BΛ * BH * BL) := by
  obtain ⟨CM, hCM, hMd⟩ := hw.M_nu 4 (2 / 5) (2 / 5) (by norm_num)
  obtain ⟨CW, hCW, hWd⟩ := hw.W_nu (A + 2) (3 / 1000) (3 / 1000)
  refine ⟨Real.exp ((s1 + 2 / 5 - 1) ^ 2) * Real.exp 1 * CM * CW * 2 ^ A * (∫ t, nu 2 t) ^ 3,
    ?_, fun Zs Λ Lt H BZ BΛ BH BL h q hq Z hZ => ?_⟩
  · have := integral_nonneg (μ := volume) (f := nu 2) (fun t => nu_nonneg 2 t)
    positivity
  have hZ0 : 0 < Z := by linarith
  have hB0 : 0 ≤ BZ * BΛ * BH * BL := by
    have := h.hBZ; have := h.hBΛ; have := h.hBH; have := h.hBL; positivity
  have hMl : ∀ t : ℝ, ‖M (((2 / 5 : ℝ) : ℂ) + t * I)‖ ≤ CM * nu 4 t := fun t => by
    have := hMd (((2 / 5 : ℝ) : ℂ) + t * I) (by simp) (by simp)
    simpa using this
  have hWl : ∀ t : ℝ, ‖Wh (((3 / 1000 : ℝ) : ℂ) + t * I)‖ ≤ CW * nu (A + 2) t := fun t => by
    have := hWd (((3 / 1000 : ℝ) : ℂ) + t * I) (by simp) (by simp)
    simpa using this
  have hGl : ∀ t1 t2 t3 : ℝ, ‖Gf Zs Λ Lt H ((s1 : ℂ) + t1 * I) (((3 / 1000 : ℝ) : ℂ) + t2 * I)
      (((2 / 5 : ℝ) : ℂ) + t3 * I)‖ ≤ BZ * BΛ * BH * BL * (2 + |t2|) ^ A := fun t1 t2 t3 => by
    have := Gf_bound h (ξ := (s1 : ℂ) + t1 * I) (w := ((3 / 1000 : ℝ) : ℂ) + t2 * I)
      (z := ((2 / 5 : ℝ) : ℂ) + t3 * I) (by simp) (by simp) (by simp; norm_num) (by simp)
    simpa using this
  have hb := row_line_bound (Real.rpow_pos_of_pos hZ0 (9 / 10 : ℝ))
    (Real.rpow_pos_of_pos hZ0 (133 / 1000 : ℝ)) hZ0 hq (G := Gf Zs Λ Lt H) (a := s1)
    (b := 3 / 1000) (c := 2 / 5) (M := M) (Wh := Wh) (B := BZ * BΛ * BH * BL) h.hA
    hB0 hCM hCW hMl hWl hGl
  refine hb.trans_eq ?_
  have hz := zpow3 hZ0 (1 / 2 - 2 / 5) (s1 + 2 / 5 - 1) (3 / 1000 - 1)
  have he : 9 / 10 * (1 / 2 - 2 / 5) + (s1 + 2 / 5 - 1) + 133 / 1000 * (3 / 1000 - 1) =
      s1 - 642601 / 1000000 := by ring
  rw [he] at hz
  rw [hz]
  ring

/-- (8.20): the bound on the lines `(4, 4, R₀)`. -/
theorem row_bound_large (hw : WeightHyp M Wh) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Zs Λ Lt : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) (BZ BΛ BH BL : ℝ),
      RowHyp Zs Λ Lt H A BZ BΛ BH BL → ∀ (q : ℕ), 1 ≤ q → ∀ Z : ℝ, 1 ≤ Z →
        ‖I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) 4 4 R0‖ ≤
          K * Z ^ (3849 / 1000 + R0 / 10) * (q : ℝ) ^ (-R0) * (BZ * BΛ * BH * BL) := by
  obtain ⟨CM, hCM, hMd⟩ := hw.M_nu 4 R0 R0 (by unfold R0; norm_num)
  obtain ⟨CW, hCW, hWd⟩ := hw.W_nu (A + 2) 4 4
  refine ⟨Real.exp ((4 + R0 - 1) ^ 2) * Real.exp 1 * CM * CW * 2 ^ A * (∫ t, nu 2 t) ^ 3,
    ?_, fun Zs Λ Lt H BZ BΛ BH BL h q hq Z hZ => ?_⟩
  · have := integral_nonneg (μ := volume) (f := nu 2) (fun t => nu_nonneg 2 t)
    positivity
  have hZ0 : 0 < Z := by linarith
  have hB0 : 0 ≤ BZ * BΛ * BH * BL := by
    have := h.hBZ; have := h.hBΛ; have := h.hBH; have := h.hBL; positivity
  have hMl : ∀ t : ℝ, ‖M ((R0 : ℂ) + t * I)‖ ≤ CM * nu 4 t := fun t => by
    have := hMd ((R0 : ℂ) + t * I) (by simp) (by simp)
    simpa using this
  have hWl : ∀ t : ℝ, ‖Wh (((4 : ℝ) : ℂ) + t * I)‖ ≤ CW * nu (A + 2) t := fun t => by
    have := hWd (((4 : ℝ) : ℂ) + t * I) (by simp) (by simp)
    simpa using this
  have hGl : ∀ t1 t2 t3 : ℝ, ‖Gf Zs Λ Lt H (((4 : ℝ) : ℂ) + t1 * I) (((4 : ℝ) : ℂ) + t2 * I)
      ((R0 : ℂ) + t3 * I)‖ ≤ BZ * BΛ * BH * BL * (2 + |t2|) ^ A := fun t1 t2 t3 => by
    have h1 : s1 ≤ (((4 : ℝ) : ℂ) + t1 * I).re := by simp; unfold s1; norm_num
    have h2 : 3 / 1000 ≤ (((4 : ℝ) : ℂ) + t2 * I).re := by simp; norm_num
    have h3 : (((4 : ℝ) : ℂ) + t2 * I).re ≤ 4 := by simp
    have h4 : 2 / 5 ≤ ((R0 : ℂ) + t3 * I).re := by simp; unfold R0; norm_num
    have := Gf_bound h h1 h2 h3 h4
    simpa using this
  have hb := row_line_bound (Real.rpow_pos_of_pos hZ0 (9 / 10 : ℝ))
    (Real.rpow_pos_of_pos hZ0 (133 / 1000 : ℝ)) hZ0 hq (G := Gf Zs Λ Lt H) (a := 4)
    (b := 4) (c := R0) (M := M) (Wh := Wh) (B := BZ * BΛ * BH * BL) h.hA
    hB0 hCM hCW hMl hWl hGl
  refine hb.trans_eq ?_
  have hz := zpow3 hZ0 (1 / 2 - R0) (4 + R0 - 1) (4 - 1)
  have he : 9 / 10 * (1 / 2 - R0) + (4 + R0 - 1) + 133 / 1000 * (4 - 1) =
      3849 / 1000 + R0 / 10 := by ring
  rw [he] at hz
  rw [hz]
  ring

/-- (8.17)–(8.19): the truncated move of the `ξ`-line to `.998` for a good row, given a
continuation `D` of `1/L` to `Re ξ > .997, |Im ξ| < T₂` with `‖D‖ ≤ B_D` on the rectangle of
height `T < T₂`. `N ≥ 2` is the decay exponent in `Im ξ` used for the discarded tails. -/
theorem row_bound_good (hw : WeightHyp M Wh) (A N : ℝ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Zs Λ Lt : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) (BZ BΛ BH BL : ℝ),
      RowHyp Zs Λ Lt H A BZ BΛ BH BL → ∀ (q : ℕ), 1 ≤ q → ∀ (D : ℂ → ℂ) (T T2 BD : ℝ),
        0 ≤ T → T < T2 → 0 ≤ BD →
        DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < T2} →
        (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < T2 → D ξ * Lt ξ = 1) →
        (∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ T → ‖D ξ‖ ≤ BD) →
        ∀ Z : ℝ, 1 ≤ Z →
        ‖I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh q (Gf Zs Λ Lt H)) s1
          (3 / 1000) (2 / 5)‖ ≤
          K * (q : ℝ) ^ (-(2 / 5 : ℝ)) * (BZ * BΛ * BH) *
            (Z ^ (998 / 1000 - 642601 / 1000000 : ℝ) * BD +
              Z ^ (s1 - 642601 / 1000000) * (1 + T) ^ (-(N - 2)) * (BD + BL)) := by
  obtain ⟨CM, hCM, hMd⟩ := hw.M_nu (N + 2) (2 / 5) (2 / 5) (by norm_num)
  obtain ⟨CW, hCW, hWd⟩ := hw.W_nu (A + 2) (3 / 1000) (3 / 1000)
  have hI := integral_nonneg (μ := volume) (f := nu 2) (fun t => nu_nonneg 2 t)
  set J := ∫ t, nu 2 t
  set c0 := Real.exp 1 * Real.exp (N ^ 2 / 4) * CM * CW * 2 ^ A with hc0
  have hc0n : 0 ≤ c0 := by positivity
  refine ⟨c0 * J ^ 2 * (J + 2 * (s1 - 998 / 1000) + J), by
    have : 0 ≤ s1 - 998 / 1000 := by unfold s1; norm_num
    positivity, ?_⟩
  intro Zs Λ Lt H BZ BΛ BH BL h q hq D T T2 BD hT hTT hBD hDd hDL hDb Z hZ
  have hZ0 : 0 < Z := by linarith
  set X := Z ^ (9 / 10 : ℝ) with hXdef
  set Y := Z ^ (133 / 1000 : ℝ) with hYdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hZ0 _
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hZ0 _
  have hX1 : 1 ≤ X := one_le_rpow' hZ (by norm_num)
  have hBZ := h.hBZ; have hBΛ := h.hBΛ; have hBH := h.hBH; have hBL := h.hBL
  set G' : ℂ → ℂ → ℂ → ℂ := fun ξ w z => Zs (6 * z) * Λ w * H ξ w z * D ξ with hG'
  set Φ := Phi X Y Z M Wh q (Gf Zs Λ Lt H)
  set Φ' := Phi X Y Z M Wh q G'
  set P : ℝ → ℝ := fun x => X ^ (1 / 2 - (2 / 5 : ℝ)) * Z ^ (x + 2 / 5 - 1) *
    Y ^ ((3 / 1000 : ℝ) - 1) * (q : ℝ) ^ (-(2 / 5 : ℝ)) with hP
  have hPn : ∀ x, 0 ≤ P x := fun x => by positivity
  have hPZ : ∀ x : ℝ, P x = Z ^ (x - 642601 / 1000000) * (q : ℝ) ^ (-(2 / 5 : ℝ)) := by
    intro x
    have hz := zpow3 hZ0 (1 / 2 - 2 / 5) (x + 2 / 5 - 1) (3 / 1000 - 1)
    have he : 9 / 10 * (1 / 2 - 2 / 5) + (x + 2 / 5 - 1) + 133 / 1000 * (3 / 1000 - 1) =
        x - 642601 / 1000000 := by ring
    rw [he] at hz
    simp only [hP, hXdef, hYdef]
    rw [hz]
  -- the bound of `G'` on the rectangle
  have hG'b : ∀ ξ w z : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ T → 3 / 1000 ≤ w.re → w.re ≤ 4 →
      2 / 5 ≤ z.re → ‖G' ξ w z‖ ≤ (BZ * BΛ * BH * BD) * (2 + |w.im|) ^ A := by
    intro ξ w z h1 h2 h3 h4 h5
    have hp : (ξ, w, z) ∈ regionOne := ⟨by linarith, by linarith, by linarith⟩
    have e1 := h.hZb (6 * z) (by simp; linarith)
    have e2 := h.hΛb w h3 h4
    have e3 := h.hHb _ hp
    have e4 := hDb ξ h1 h2
    simp only [hG', norm_mul]
    have hp2 : 0 ≤ (2 + |w.im|) ^ A := by positivity
    calc ‖Zs (6 * z)‖ * ‖Λ w‖ * ‖H ξ w z‖ * ‖D ξ‖
        ≤ BZ * (BΛ * (2 + |w.im|) ^ A) * BH * BD := by gcongr
      _ = _ := by ring
  have hline : ∀ x t2 t3 : ℝ, ((x : ℂ) + t2 * I).re = x ∧ ((x : ℂ) + t3 * I).im = t3 := by
    intro x t2 t3; simp
  have hMl : ∀ t : ℝ, ‖M (((2 / 5 : ℝ) : ℂ) + t * I)‖ ≤ CM * nu (N + 2) t := fun t => by
    simpa using hMd (((2 / 5 : ℝ) : ℂ) + t * I) (by simp) (by simp)
  have hWl : ∀ t : ℝ, ‖Wh (((3 / 1000 : ℝ) : ℂ) + t * I)‖ ≤ CW * nu (A + 2) t := fun t => by
    simpa using hWd (((3 / 1000 : ℝ) : ℂ) + t * I) (by simp) (by simp)
  have hexp : ∀ x : ℝ, 998 / 1000 ≤ x → x ≤ s1 → Real.exp ((x + 2 / 5 - 1) ^ 2) ≤ Real.exp 1 := by
    intro x h1 h2
    apply Real.exp_le_exp.2
    unfold s1 at h2
    nlinarith
  have hs1 := s1_gt
  have hs1' : 998 / 1000 ≤ s1 := by unfold s1; norm_num
  -- apply `trunc_xi`
  have hmain := trunc_xi Φ Φ' (a0 := 998 / 1000) (a := s1) (b := 3 / 1000) (c := 2 / 5) (T := T)
    (N := N) hs1' hT hN (m2 := nu 2) (m3 := nu 2) (integrable_nu (by norm_num))
    (integrable_nu (by norm_num)) (nu_nonneg 2) (nu_nonneg 2)
    (K1 := P s1 * (c0 * (BZ * BΛ * BH * BL)))
    (Kl := P (998 / 1000) * (c0 * (BZ * BΛ * BH * BD)))
    (Kh := P s1 * (c0 * (BZ * BΛ * BH * BD)) * (1 + T) ^ (-N))
    (by have := hPn s1; positivity) (by have := hPn (998 / 1000); positivity)
    (by have h1 := hPn s1; have h2 : 0 ≤ (1 + T) ^ (-N) := Real.rpow_nonneg (by linarith) _; positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · refine hmain.trans ?_
    rw [hPZ, hPZ]
    have hT1 : (1 + T) ^ (-N) ≤ (1 + T) ^ (-(N - 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hJ := hI
    have hq0 : 0 ≤ (q : ℝ) ^ (-(2 / 5 : ℝ)) := by positivity
    have hz1 : 0 ≤ Z ^ (s1 - 642601 / 1000000) := by positivity
    have hz2 : 0 ≤ Z ^ (998 / 1000 - 642601 / 1000000 : ℝ) := by positivity
    have hT2 : 0 ≤ (1 + T) ^ (-(N - 2)) := by positivity
    have hss : 0 ≤ s1 - 998 / 1000 := by linarith
    set Q := (q : ℝ) ^ (-(2 / 5 : ℝ))
    set z1 := Z ^ (s1 - 642601 / 1000000)
    set z2 := Z ^ (998 / 1000 - 642601 / 1000000 : ℝ)
    set τ := (1 + T) ^ (-(N - 2))
    set B3 := BZ * BΛ * BH
    have hB3 : 0 ≤ B3 := by positivity
    calc (z2 * Q * (c0 * (B3 * BD)) * J + 2 * (s1 - 998 / 1000) * (z1 * Q * (c0 * (B3 * BD)) *
          (1 + T) ^ (-N)) + z1 * Q * (c0 * (B3 * BL)) * τ * J) * J * J
        ≤ (z2 * Q * (c0 * (B3 * BD)) * J + 2 * (s1 - 998 / 1000) * (z1 * Q * (c0 * (B3 * BD)) *
          τ) + z1 * Q * (c0 * (B3 * BL)) * τ * J) * J * J := by gcongr
      _ ≤ c0 * J ^ 2 * (J + 2 * (s1 - 998 / 1000) + J) * Q * B3 * (z2 * BD + z1 * τ * (BD + BL)) := by
          have h1 : 0 ≤ c0 * J ^ 2 * Q * B3 := by positivity
          have e : c0 * J ^ 2 * (J + 2 * (s1 - 998 / 1000) + J) * Q * B3 *
              (z2 * BD + z1 * τ * (BD + BL)) -
              (z2 * Q * (c0 * (B3 * BD)) * J + 2 * (s1 - 998 / 1000) *
                (z1 * Q * (c0 * (B3 * BD)) * τ) + z1 * Q * (c0 * (B3 * BL)) * τ * J) * J * J =
              c0 * J ^ 2 * Q * B3 * (z2 * BD * (2 * (s1 - 998 / 1000) + J) +
                z1 * τ * (BD * (J + J) + BL * (J + 2 * (s1 - 998 / 1000)))) := by ring
          have : 0 ≤ c0 * J ^ 2 * Q * B3 * (z2 * BD * (2 * (s1 - 998 / 1000) + J) +
              z1 * τ * (BD * (J + J) + BL * (J + 2 * (s1 - 998 / 1000)))) := by positivity
          linarith
      _ = _ := by ring
  · -- continuity on the right line
    exact cont_Phi hX0 hY0 hZ0 hq hw.hM.1 hw.hW (Gf_cont h)
      ((C3P.continuous_line s1).comp continuous_fst)
      ((C3P.continuous_line _).comp (continuous_fst.comp continuous_snd))
      ((C3P.continuous_line _).comp (continuous_snd.comp continuous_snd))
      (fun p => by simp) (fun p => ⟨by simpa using hs1, by simp; norm_num, by simp; norm_num⟩)
  · -- the bound on the right line
    intro t1 t2 t3
    have hb := norm_Phi_le hX0 hY0 hZ0 hq (M := M) (Wh := Wh) (G := Gf Zs Λ Lt H)
      (ξ := (s1 : ℂ) + t1 * I) (w := ((3 / 1000 : ℝ) : ℂ) + t2 * I)
      (z := ((2 / 5 : ℝ) : ℂ) + t3 * I) (N := N) (by linarith) h.hA hCM hCW
      (by positivity) (by simpa using hMl t3) (by simpa using hWl t2)
      (Gf_bound h (ξ := (s1 : ℂ) + t1 * I) (w := ((3 / 1000 : ℝ) : ℂ) + t2 * I)
        (z := ((2 / 5 : ℝ) : ℂ) + t3 * I) (by simp) (by simp) (by simp; norm_num) (by simp))
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hb
    refine hb.trans ?_
    have := hexp s1 hs1' le_rfl
    have hn : 0 ≤ nu N t1 * nu 2 t2 * nu 2 t3 := by
      have := nu_nonneg N t1; have := nu_nonneg 2 t2; have := nu_nonneg 2 t3; positivity
    calc X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ (s1 + 2 / 5 - 1) * Y ^ ((3 / 1000 : ℝ) - 1) *
          (q : ℝ) ^ (-(2 / 5 : ℝ)) * (Real.exp ((s1 + 2 / 5 - 1) ^ 2) * Real.exp (N ^ 2 / 4) * CM *
            CW * 2 ^ A * (BZ * BΛ * BH * BL)) * (nu N t1 * nu 2 t2 * nu 2 t3)
        ≤ X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ (s1 + 2 / 5 - 1) * Y ^ ((3 / 1000 : ℝ) - 1) *
          (q : ℝ) ^ (-(2 / 5 : ℝ)) * (Real.exp 1 * Real.exp (N ^ 2 / 4) * CM *
            CW * 2 ^ A * (BZ * BΛ * BH * BL)) * (nu N t1 * nu 2 t2 * nu 2 t3) := by gcongr
      _ = _ := by simp only [hP, hc0]; ring
  · -- agreement on the right edge
    intro t1 t2 t3 ht
    simp only [Φ, Φ', Phi, Gf, hG']
    have h1 : 1 < ((s1 : ℂ) + t1 * I).re := by simpa using hs1
    have h2 : |((s1 : ℂ) + t1 * I).im| < T2 := by simpa using ht.trans_lt hTT
    have hD := hDL _ h1 h2
    have hL := h.hL0 _ h1
    rw [show D ((s1 : ℂ) + t1 * I) = (Lt ((s1 : ℂ) + t1 * I))⁻¹ from
      eq_inv_of_mul_eq_one_left hD]
  · -- holomorphy on the rectangle
    intro t2 t3
    refine diff_Phi_xi hZ0 fun ξ hξ => ?_
    have hr : (ξ, ((3 / 1000 : ℝ) : ℂ) + t2 * I, ((2 / 5 : ℝ) : ℂ) + t3 * I) ∈ regionOne :=
      ⟨by linarith [hξ.1], by simp; norm_num, by simp; norm_num⟩
    have hO : IsOpen {ξ : ℂ | 997 / 1000 < ξ.re ∧ |ξ.im| < T2} :=
      (isOpen_re_gt _).inter (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        continuous_const)
    have h998 : (998 / 1000 : ℝ) ≤ ξ.re := hξ.1
    have hmem : ξ ∈ {ξ : ℂ | 997 / 1000 < ξ.re ∧ |ξ.im| < T2} :=
      ⟨by linarith, hξ.2.2.trans_lt hTT⟩
    have hDa : DifferentiableAt ℂ D ξ := hDd.differentiableAt (hO.mem_nhds hmem)
    exact ((differentiableAt_const _).mul (H_xi h hr)).mul hDa
  · -- the left edge
    intro t1 t2 t3 ht
    have hb := norm_Phi_le hX0 hY0 hZ0 hq (M := M) (Wh := Wh) (G := G')
      (ξ := ((998 / 1000 : ℝ) : ℂ) + t1 * I) (w := ((3 / 1000 : ℝ) : ℂ) + t2 * I)
      (z := ((2 / 5 : ℝ) : ℂ) + t3 * I) (N := N) (by linarith) h.hA hCM hCW
      (by positivity) (by simpa using hMl t3) (by simpa using hWl t2)
      (hG'b (((998 / 1000 : ℝ) : ℂ) + t1 * I) (((3 / 1000 : ℝ) : ℂ) + t2 * I)
        (((2 / 5 : ℝ) : ℂ) + t3 * I) (by simp) (by simpa using ht) (by simp) (by simp; norm_num)
        (by simp))
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hb
    refine hb.trans ?_
    have := hexp (998 / 1000) le_rfl hs1'
    have hnN := nu_anti hN t1
    have h0 : 0 ≤ X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ ((998 / 1000 : ℝ) + 2 / 5 - 1) *
        Y ^ ((3 / 1000 : ℝ) - 1) * (q : ℝ) ^ (-(2 / 5 : ℝ)) := by positivity
    have hn2 : 0 ≤ nu 2 t2 * nu 2 t3 := by
      have := nu_nonneg 2 t2; have := nu_nonneg 2 t3; positivity
    calc X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ ((998 / 1000 : ℝ) + 2 / 5 - 1) * Y ^ ((3 / 1000 : ℝ) - 1) *
          (q : ℝ) ^ (-(2 / 5 : ℝ)) * (Real.exp (((998 / 1000 : ℝ) + 2 / 5 - 1) ^ 2) *
            Real.exp (N ^ 2 / 4) * CM * CW * 2 ^ A * (BZ * BΛ * BH * BD)) *
          (nu N t1 * nu 2 t2 * nu 2 t3)
        ≤ X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ ((998 / 1000 : ℝ) + 2 / 5 - 1) * Y ^ ((3 / 1000 : ℝ) - 1) *
          (q : ℝ) ^ (-(2 / 5 : ℝ)) * (Real.exp 1 *
            Real.exp (N ^ 2 / 4) * CM * CW * 2 ^ A * (BZ * BΛ * BH * BD)) *
          (nu 2 t1 * nu 2 t2 * nu 2 t3) := by
          gcongr
          all_goals (try positivity)
          all_goals (try exact nu_nonneg _ _)
          all_goals (try exact mul_nonneg (mul_nonneg (nu_nonneg _ _) (nu_nonneg _ _)) (nu_nonneg _ _))
      _ = _ := by simp only [hP, hc0]; ring
  · -- the horizontal edges
    intro x t2 t3 hx1 hx2
    have hZx : Z ^ (x + 2 / 5 - 1) ≤ Z ^ (s1 + 2 / 5 - 1) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have key : ∀ s' : ℝ, |s'| = T → ‖Φ' ((x : ℂ) + s' * I) (((3 / 1000 : ℝ) : ℂ) + t2 * I)
        (((2 / 5 : ℝ) : ℂ) + t3 * I)‖ ≤ P s1 * (c0 * (BZ * BΛ * BH * BD)) * (1 + T) ^ (-N) *
          nu 2 t2 * nu 2 t3 := by
      intro s' hs'
      have hb := norm_Phi_le hX0 hY0 hZ0 hq (M := M) (Wh := Wh) (G := G')
        (ξ := (x : ℂ) + s' * I) (w := ((3 / 1000 : ℝ) : ℂ) + t2 * I)
        (z := ((2 / 5 : ℝ) : ℂ) + t3 * I) (N := N) (by linarith) h.hA hCM hCW
        (by positivity) (by simpa using hMl t3) (by simpa using hWl t2)
        (hG'b ((x : ℂ) + s' * I) (((3 / 1000 : ℝ) : ℂ) + t2 * I)
          (((2 / 5 : ℝ) : ℂ) + t3 * I) (by simpa using hx1) (by simp [hs']) (by simp)
          (by simp; norm_num) (by simp))
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at hb
      refine hb.trans ?_
      have := hexp x hx1 hx2
      have hnT : nu N s' = (1 + T) ^ (-N) := by unfold nu; rw [hs']
      rw [hnT]
      have hn2 : 0 ≤ (1 + T) ^ (-N) * nu 2 t2 * nu 2 t3 := by
        have := nu_nonneg 2 t2; have := nu_nonneg 2 t3; positivity
      calc X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ (x + 2 / 5 - 1) * Y ^ ((3 / 1000 : ℝ) - 1) *
            (q : ℝ) ^ (-(2 / 5 : ℝ)) * (Real.exp ((x + 2 / 5 - 1) ^ 2) *
              Real.exp (N ^ 2 / 4) * CM * CW * 2 ^ A * (BZ * BΛ * BH * BD)) *
            ((1 + T) ^ (-N) * nu 2 t2 * nu 2 t3)
          ≤ X ^ (1 / 2 - 2 / 5 : ℝ) * Z ^ (s1 + 2 / 5 - 1) * Y ^ ((3 / 1000 : ℝ) - 1) *
            (q : ℝ) ^ (-(2 / 5 : ℝ)) * (Real.exp 1 *
              Real.exp (N ^ 2 / 4) * CM * CW * 2 ^ A * (BZ * BΛ * BH * BD)) *
            ((1 + T) ^ (-N) * nu 2 t2 * nu 2 t3) := by gcongr
        _ = _ := by simp only [hP, hc0]; ring
    refine ⟨key T (abs_of_nonneg hT), ?_⟩
    have := key (-T) (by rw [abs_neg, abs_of_nonneg hT])
    simpa using this

end

end L2C

end ArtinPrimitiveRoots
end

section
/-! # L2C_Sum: summing the row bounds, (8.21)

Abstractly: rows `i : ι` with frequency norms `q_i ≥ 1` and `∑ q_i^{-σ} < ∞` (`σ > 1`), an
exceptional predicate whose members of norm `≤ V` lie in a finite set of size `≪ V^{1/2}`
(Proposition 8.2), and three per-row bounds:

* (8.15), every row: `‖J_i‖ ≤ c_I Z^{e₁} q_i^{.102}`;
* (8.20), every row: `‖J_i‖ ≤ c_III Z^{3.849 + R₀/10} q_i^{-R₀ + .502}`;
* (8.17)–(8.19), good rows with `q_i > Z^{.09}`:
  `‖J_i‖ ≤ c_II (Z^{e₂} q_i^{.103} + Z^{e₁} q_i^{-1.897})`.

Then `‖∑ J_i‖ ≪ Z^{7/15 − 1/2500}`. The ranges are `q ≤ Z^{.09}` (first bound),
`Z^{.09} < q ≤ Z^{.10001}` (exceptional: first bound, counted; good: third bound) and
`q > Z^{.10001}` (second bound), as on pp. 57–58. -/

open Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace L2C

noncomputable section

/-- `e₁ = E*(σ₁, .003, .4)`. -/
def e1 : ℝ := s1 - 642601 / 1000000

/-- `e₂ = E*(.998, .003, .4)`. -/
def e2 : ℝ := 998 / 1000 - 642601 / 1000000

/-- `E*(4, 4, R₀)`. -/
def e3 : ℝ := 3849 / 1000 + R0 / 10

/-- The target exponent `7/15 − 1/2500`. -/
def etarget : ℝ := 7 / 15 - 1 / 2500

lemma rpow_le_target {Z : ℝ} (hZ : 1 ≤ Z) {x : ℝ} (hx : x ≤ etarget) : Z ^ x ≤ Z ^ etarget :=
  Real.rpow_le_rpow_of_exponent_le hZ hx

/-- `q ≤ V ⇒ q^a ≤ V^{a+σ} q^{-σ}` for `a + σ ≥ 0`. -/
lemma rpow_le_of_le {q V a σ : ℝ} (hq : 0 < q) (hqV : q ≤ V) (haσ : 0 ≤ a + σ) :
    q ^ a ≤ V ^ (a + σ) * q ^ (-σ) := by
  have h1 : q ^ a = q ^ (a + σ) * q ^ (-σ) := by
    rw [← Real.rpow_add hq]; ring_nf
  rw [h1]
  gcongr

/-- `q > V > 0 ⇒ q^{-b} ≤ V^{-(b-σ)} q^{-σ}` for `b ≥ σ`. -/
lemma rpow_le_of_gt {q V b σ : ℝ} (hV : 0 < V) (hqV : V ≤ q) (hbσ : σ ≤ b) :
    q ^ (-b) ≤ V ^ (-(b - σ)) * q ^ (-σ) := by
  have hq : 0 < q := lt_of_lt_of_le hV hqV
  have h1 : q ^ (-b) = q ^ (-(b - σ)) * q ^ (-σ) := by
    rw [← Real.rpow_add hq]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hV hqV (by linarith))
    (by positivity)

lemma zz {Z : ℝ} (hZ : 0 < Z) (a b c : ℝ) : Z ^ a * (Z ^ b) ^ c = Z ^ (a + b * c) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]

theorem sum_bound {ι : Type*} (q : ι → ℕ) (hq : ∀ i, 1 ≤ q i)
    (hS : ∀ σ : ℝ, 1 < σ → Summable fun i => ((q i : ℕ) : ℝ) ^ (-σ))
    (exc : ι → Prop) (Fs : ℝ → Finset ι) (Cc : ℝ)
    (hFin : ∀ V : ℝ, ∀ i, exc i → ((q i : ℕ) : ℝ) ≤ V → i ∈ Fs V)
    (hFc : ∀ V : ℝ, 1 ≤ V → ((Fs V).card : ℝ) ≤ Cc * V ^ (1 / 2 : ℝ))
    (cI cII cIII : ℝ) :
    ∃ C : ℝ, ∀ Z : ℝ, 1 ≤ Z → ∀ J : ι → ℂ,
      (∀ i, ‖J i‖ ≤ cI * Z ^ e1 * ((q i : ℕ) : ℝ) ^ (51 / 500 : ℝ)) →
      (∀ i, ‖J i‖ ≤ cIII * Z ^ e3 * ((q i : ℕ) : ℝ) ^ (-R0 + 251 / 500)) →
      (∀ i, Z ^ (9 / 100 : ℝ) < ((q i : ℕ) : ℝ) → ¬ exc i →
        ‖J i‖ ≤ cII * (Z ^ e2 * ((q i : ℕ) : ℝ) ^ (103 / 1000 : ℝ) +
          Z ^ e1 * ((q i : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ))) →
      ‖∑' i, J i‖ ≤ C * Z ^ etarget := by
  classical
  set a1 := max cI 0
  set a2 := max cII 0
  set a3 := max cIII 0
  set Cc' := max Cc 0
  have ha1 : 0 ≤ a1 := le_max_right _ _
  have ha2 : 0 ≤ a2 := le_max_right _ _
  have ha3 : 0 ≤ a3 := le_max_right _ _
  have hS1 := hS (1001 / 1000) (by norm_num)
  have hS2 := hS 2 (by norm_num)
  have hS3 := hS (1897 / 1000) (by norm_num)
  set S1 := ∑' i, ((q i : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ))
  set S2 := ∑' i, ((q i : ℕ) : ℝ) ^ (-(2 : ℝ))
  set S3 := ∑' i, ((q i : ℕ) : ℝ) ^ (-(1897 / 1000 : ℝ))
  have hS1n : 0 ≤ S1 := tsum_nonneg fun _ => by positivity
  have hS2n : 0 ≤ S2 := tsum_nonneg fun _ => by positivity
  have hS3n : 0 ≤ S3 := tsum_nonneg fun _ => by positivity
  refine ⟨a1 * S1 + a1 * Cc' + a2 * (S1 + S3) + a3 * S2, fun Z hZ J hI hIII hII => ?_⟩
  have hZ0 : 0 < Z := by linarith
  set V1 := Z ^ (9 / 100 : ℝ)
  set V2 := Z ^ (10001 / 100000 : ℝ)
  have hV1 : 1 ≤ V1 := Real.one_le_rpow hZ (by norm_num)
  have hV2 : 1 ≤ V2 := Real.one_le_rpow hZ (by norm_num)
  have hV12 : V1 ≤ V2 := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  set Q : ι → ℝ := fun i => ((q i : ℕ) : ℝ)
  have hQ : ∀ i, 1 ≤ Q i := fun i => by simp only [Q]; exact_mod_cast hq i
  have hQ0 : ∀ i, 0 < Q i := fun i => by linarith [hQ i]
  -- the majorant
  set m : ι → ℝ := fun i =>
    a1 * Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ)) +
    a1 * Z ^ e1 * V2 ^ (51 / 500 : ℝ) * (if i ∈ Fs V2 then 1 else 0) +
    a2 * (Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ)) +
      Z ^ e1 * Q i ^ (-(1897 / 1000 : ℝ))) +
    a3 * Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2)) * Q i ^ (-(2 : ℝ)) with hm
  have hZe1 : 0 ≤ Z ^ e1 := by positivity
  have hZe2 : 0 ≤ Z ^ e2 := by positivity
  have hZe3 : 0 ≤ Z ^ e3 := by positivity
  have hmn : ∀ i, 0 ≤ (if i ∈ Fs V2 then (1 : ℝ) else 0) := fun i => by split_ifs <;> norm_num
  have hbound : ∀ i, ‖J i‖ ≤ m i := by
    intro i
    have t1 : 0 ≤ a1 * Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ)) := by
      have := hQ0 i; positivity
    have t2 : 0 ≤ a1 * Z ^ e1 * V2 ^ (51 / 500 : ℝ) * (if i ∈ Fs V2 then 1 else 0) := by
      have := hmn i; positivity
    have t3 : 0 ≤ a2 * (Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ)) +
        Z ^ e1 * Q i ^ (-(1897 / 1000 : ℝ))) := by
      have := hQ0 i; positivity
    have t4 : 0 ≤ a3 * Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2)) * Q i ^ (-(2 : ℝ)) := by
      have := hQ0 i; positivity
    have hIa : ‖J i‖ ≤ a1 * Z ^ e1 * Q i ^ (51 / 500 : ℝ) :=
      (hI i).trans (by gcongr; exact le_max_left _ _)
    by_cases h1 : Q i ≤ V1
    · -- small frequencies
      have := rpow_le_of_le (hQ0 i) h1 (a := 51 / 500) (σ := 1001 / 1000) (by norm_num)
      have : ‖J i‖ ≤ a1 * Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ) *
          Q i ^ (-(1001 / 1000 : ℝ)) := by
        refine hIa.trans ?_
        calc a1 * Z ^ e1 * Q i ^ (51 / 500 : ℝ) ≤ a1 * Z ^ e1 *
              (V1 ^ (51 / 500 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ))) := by gcongr
          _ = _ := by ring
      simp only [hm]; linarith
    push Not at h1
    by_cases h2 : Q i ≤ V2
    · by_cases he : exc i
      · -- exceptional rows
        have hmem : i ∈ Fs V2 := hFin V2 i he h2
        have : ‖J i‖ ≤ a1 * Z ^ e1 * V2 ^ (51 / 500 : ℝ) * (if i ∈ Fs V2 then 1 else 0) := by
          rw [if_pos hmem, mul_one]
          refine hIa.trans ?_
          gcongr
        simp only [hm]; linarith
      · -- good rows
        have hb := hII i h1 he
        have h3 := rpow_le_of_le (hQ0 i) h2 (a := 103 / 1000) (σ := 1001 / 1000) (by norm_num)
        have : ‖J i‖ ≤ a2 * (Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) *
            Q i ^ (-(1001 / 1000 : ℝ)) + Z ^ e1 * Q i ^ (-(1897 / 1000 : ℝ))) := by
          refine hb.trans ?_
          have hp : 0 ≤ Z ^ e2 * Q i ^ (103 / 1000 : ℝ) + Z ^ e1 * Q i ^ (-(1897 / 1000) : ℝ) := by
            have := hQ0 i; positivity
          calc cII * (Z ^ e2 * Q i ^ (103 / 1000 : ℝ) + Z ^ e1 * Q i ^ (-(1897 / 1000) : ℝ))
              ≤ a2 * (Z ^ e2 * Q i ^ (103 / 1000 : ℝ) + Z ^ e1 * Q i ^ (-(1897 / 1000) : ℝ)) := by
                gcongr; exact le_max_left _ _
            _ ≤ _ := by
                have hx : Z ^ e2 * Q i ^ (103 / 1000 : ℝ) ≤ Z ^ e2 *
                    V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ)) := by
                  calc Z ^ e2 * Q i ^ (103 / 1000 : ℝ) ≤ Z ^ e2 *
                      (V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) * Q i ^ (-(1001 / 1000 : ℝ))) := by
                        gcongr
                    _ = _ := by ring
                exact mul_le_mul_of_nonneg_left (add_le_add_left hx _) ha2
        simp only [hm]; linarith
    · -- large frequencies
      push Not at h2
      have h3 := rpow_le_of_gt (lt_of_lt_of_le zero_lt_one hV2) h2.le (b := R0 - 251 / 500)
        (σ := 2) (by unfold R0; norm_num)
      have : ‖J i‖ ≤ a3 * Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2)) * Q i ^ (-(2 : ℝ)) := by
        refine (hIII i).trans ?_
        have e : (-R0 + 251 / 500 : ℝ) = -(R0 - 251 / 500) := by ring
        rw [e]
        calc cIII * Z ^ e3 * Q i ^ (-(R0 - 251 / 500)) ≤ a3 * Z ^ e3 * Q i ^ (-(R0 - 251 / 500)) := by
              gcongr; exact le_max_left _ _
          _ ≤ a3 * Z ^ e3 * (V2 ^ (-(R0 - 251 / 500 - 2)) * Q i ^ (-(2 : ℝ))) := by gcongr
          _ = _ := by ring
      simp only [hm]; linarith
  -- summability of the majorant
  have hind : Summable fun i => (if i ∈ Fs V2 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := Fs V2) fun i hi => if_neg hi
  have hmS : Summable m := by
    simp only [hm]
    refine (((hS1.mul_left _).add (hind.mul_left _)).add ?_).add (hS2.mul_left _)
    exact ((hS1.mul_left _).add (hS3.mul_left _)).mul_left _
  refine (tsum_of_norm_bounded hmS.hasSum hbound).trans ?_
  -- the four sums
  have hcard : ∑' i, (if i ∈ Fs V2 then (1 : ℝ) else 0) = (Fs V2).card := by
    rw [tsum_eq_sum (s := Fs V2) fun i hi => if_neg hi]
    simp
  have hsum : ∑' i, m i = a1 * Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ) * S1 +
      a1 * Z ^ e1 * V2 ^ (51 / 500 : ℝ) * (Fs V2).card +
      a2 * (Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) * S1 + Z ^ e1 * S3) +
      a3 * Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2)) * S2 := by
    simp only [hm]
    rw [Summable.tsum_add (((hS1.mul_left _).add (hind.mul_left _)).add
        (((hS1.mul_left _).add (hS3.mul_left _)).mul_left _)) (hS2.mul_left _),
      Summable.tsum_add ((hS1.mul_left _).add (hind.mul_left _))
        (((hS1.mul_left _).add (hS3.mul_left _)).mul_left _),
      Summable.tsum_add (hS1.mul_left _) (hind.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_mul_left, Summable.tsum_add (hS1.mul_left _) (hS3.mul_left _), tsum_mul_left,
      tsum_mul_left, tsum_mul_left, hcard]
  rw [hsum]
  -- exponents
  have hV2p : 0 < V2 := by positivity
  have E1 : Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ) ≤ Z ^ etarget := by
    rw [zz hZ0]; apply rpow_le_target hZ; unfold e1 etarget s1; norm_num
  have E2 : Z ^ e1 * V2 ^ (51 / 500 : ℝ) * V2 ^ (1 / 2 : ℝ) ≤ Z ^ etarget := by
    rw [mul_assoc, ← Real.rpow_add hV2p, zz hZ0]; apply rpow_le_target hZ
    unfold e1 etarget s1; norm_num
  have E3 : Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) ≤ Z ^ etarget := by
    rw [zz hZ0]; apply rpow_le_target hZ; unfold e2 etarget; norm_num
  have E4 : Z ^ e1 ≤ Z ^ etarget := by
    apply rpow_le_target hZ; unfold e1 etarget s1; norm_num
  have E5 : Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2)) ≤ Z ^ etarget := by
    rw [zz hZ0]; apply rpow_le_target hZ; unfold e3 etarget R0; norm_num
  have hc : ((Fs V2).card : ℝ) ≤ Cc' * V2 ^ (1 / 2 : ℝ) :=
    (hFc V2 hV2).trans (by gcongr; exact le_max_left _ _)
  have hCc' : 0 ≤ Cc' := le_max_right _ _
  have k1 : a1 * Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ) * S1 ≤ a1 * S1 * Z ^ etarget := by
    calc _ = a1 * S1 * (Z ^ e1 * V1 ^ (51 / 500 + 1001 / 1000 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left E1 (by positivity)
  have k2 : a1 * Z ^ e1 * V2 ^ (51 / 500 : ℝ) * (Fs V2).card ≤ a1 * Cc' * Z ^ etarget := by
    calc _ ≤ a1 * Z ^ e1 * V2 ^ (51 / 500 : ℝ) * (Cc' * V2 ^ (1 / 2 : ℝ)) := by gcongr
      _ = a1 * Cc' * (Z ^ e1 * V2 ^ (51 / 500 : ℝ) * V2 ^ (1 / 2 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left E2 (by positivity)
  have k3 : a2 * (Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ) * S1 + Z ^ e1 * S3) ≤
      a2 * (S1 + S3) * Z ^ etarget := by
    calc _ = a2 * (S1 * (Z ^ e2 * V2 ^ (103 / 1000 + 1001 / 1000 : ℝ)) + S3 * Z ^ e1) := by ring
      _ ≤ a2 * (S1 * Z ^ etarget + S3 * Z ^ etarget) := by gcongr
      _ = _ := by ring
  have k4 : a3 * Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2)) * S2 ≤ a3 * S2 * Z ^ etarget := by
    calc _ = a3 * S2 * (Z ^ e3 * V2 ^ (-(R0 - 251 / 500 - 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left E5 (by positivity)
  calc _ ≤ a1 * S1 * Z ^ etarget + a1 * Cc' * Z ^ etarget + a2 * (S1 + S3) * Z ^ etarget +
        a3 * S2 * Z ^ etarget := by linarith
    _ = _ := by ring

end

end L2C

end ArtinPrimitiveRoots
end

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

theorem toFun_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

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

/-- The ideals not contained in any member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Ideal (𝓞 F)) := {I | ∀ P ∈ T, ¬ I ≤ P}

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) = ∑' I, (Cop T).indicator g I := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cop]
  | insert P T hPT ih =>
    have hP := hT P (Finset.mem_insert_self P T)
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.prod_insert hPT, mul_left_comm, mul_comm, ih']
    set h := (Cop T).indicator g with hh
    have hhs : Summable h := hg.indicator _
    have hPI : ∀ I, h (P * I) = g P * h I := by
      intro I
      by_cases hI : I ∈ Cop T
      · have hPI' : P * I ∈ Cop T := by
          intro Q hQ hle
          rcases (hT Q (Finset.mem_insert_of_mem hQ)).1.mul_le.1 hle with h1 | h1
          · have := (hP.1.isMaximal hP.2).eq_of_le (hT Q (Finset.mem_insert_of_mem hQ)).1.ne_top h1
            exact hPT (this ▸ hQ)
          · exact hI Q hQ h1
        rw [hh, Set.indicator_of_mem hPI', Set.indicator_of_mem hI, hmul]
      · have hPI' : P * I ∉ Cop T := by
          intro hc
          simp only [Cop, Set.mem_setOf_eq, not_forall, not_not] at hI
          obtain ⟨Q, hQ, hle⟩ := hI
          exact hc Q hQ (Ideal.mul_le_right.trans hle)
        rw [hh, Set.indicator_of_notMem hPI', Set.indicator_of_notMem hI, mul_zero]
    have hshift : g P * ∑' I, h I = ∑' J, {J | J ≤ P}.indicator h J := by
      rw [← hhs.tsum_mul_left]
      have hinj : Function.Injective (fun I : Ideal (𝓞 F) => P * I) := by
        intro a b hab
        have hP0 : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP.2
        exact mul_left_cancel₀ hP0 hab
      rw [← hinj.tsum_eq (f := {J | J ≤ P}.indicator h)]
      · congr 1
        funext I
        rw [Set.indicator_of_mem (show P * I ∈ {J | J ≤ P} from Ideal.mul_le_left), hPI]
      · intro J hJ
        have hle : J ≤ P := by
          by_contra hc
          exact hJ (Set.indicator_of_notMem hc _)
        obtain ⟨c, rfl⟩ := Ideal.dvd_iff_le.2 hle
        exact ⟨c, rfl⟩
    rw [mul_sub, mul_one, mul_comm, hshift, ← hhs.tsum_sub (hhs.indicator _)]
    congr 1
    funext J
    simp only [hh, Set.indicator, Cop, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : J ≤ P <;> by_cases h2 : ∀ Q ∈ T, ¬J ≤ Q <;> simp [h1, h2]

/-- For each `I ∈ S` with `I ≠ ⊥, ⊤`, a chosen maximal ideal containing it. -/
noncomputable def primesOf (S : Finset (Ideal (𝓞 F))) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (S.filter (fun I => I ≠ ⊤ ∧ I ≠ ⊥)).image
    (fun I => if h : I ≠ ⊤ then (Ideal.exists_le_maximal I h).choose else ⊤)

theorem primesOf_spec (S : Finset (Ideal (𝓞 F))) :
    (∀ P ∈ primesOf S, P.IsPrime ∧ P ≠ ⊥) ∧
      ∀ I ∈ S, I ≠ ⊤ → I ≠ ⊥ → ∃ P ∈ primesOf S, I ≤ P := by
  classical
  constructor
  · intro P hP
    simp only [primesOf, Finset.mem_image, Finset.mem_filter] at hP
    obtain ⟨I, ⟨-, hI, hI0⟩, rfl⟩ := hP
    rw [dif_pos hI]
    obtain ⟨hM, hle⟩ := (Ideal.exists_le_maximal I hI).choose_spec
    refine ⟨hM.isPrime, fun hb => hI0 ?_⟩
    rw [hb] at hle
    exact le_bot_iff.1 hle
  · intro I hI hIt hIb
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hI, hIt, hIb⟩), ?_⟩
    simp only [dif_pos hIt]
    exact (Ideal.exists_le_maximal I hIt).choose_spec.2

theorem sieve_bound (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J)
    (h0 : g ⊥ = 0) (h1 : g ⊤ = 1) (f : Ideal (𝓞 F) → ℝ) (hf : Summable f)
    (hgf : ∀ I, ‖g I‖ ≤ f I) (S : Finset (Ideal (𝓞 F))) :
    ‖(∑' I, g I) * ∏ P ∈ primesOf S, (1 - g P) - 1‖ ≤ ∑' I : {I // I ∉ S}, f I := by
  classical
  have hg : Summable g := Summable.of_norm_bounded hf hgf
  obtain ⟨hT, hcov⟩ := primesOf_spec S
  rw [sieve g hmul hg _ hT]
  have hite : Summable (fun I : Ideal (𝓞 F) => if I = ⊤ then (1 : ℂ) else 0) :=
    (hasSum_ite_eq ⊤ (1 : ℂ)).summable
  have hf0 : ∀ I, 0 ≤ f I := fun I => (norm_nonneg _).trans (hgf I)
  have hpt : ∀ I, ‖(Cop (primesOf S)).indicator g I - (if I = ⊤ then (1 : ℂ) else 0)‖ ≤
      ({I | I ∉ S} : Set (Ideal (𝓞 F))).indicator f I := by
    intro I
    by_cases hIt : I = ⊤
    · subst hIt
      have : (⊤ : Ideal (𝓞 F)) ∈ Cop (primesOf S) := fun P hP hle =>
        (hT P hP).1.ne_top (top_le_iff.1 hle)
      rw [Set.indicator_of_mem this, h1, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun I _ => hf0 I) _
    rw [if_neg hIt, sub_zero]
    by_cases hS : I ∈ S
    · rw [Set.indicator_of_notMem (show I ∉ {I | I ∉ S} from fun h => h hS)]
      by_cases hIb : I = ⊥
      · subst hIb
        rw [norm_le_zero_iff]
        simp [Set.indicator, h0]
      · obtain ⟨P, hP, hle⟩ := hcov I hS hIt hIb
        have hn : I ∉ Cop (primesOf S) := by
          intro h
          simp only [Cop, Set.mem_setOf_eq] at h
          exact h P hP hle
        rw [Set.indicator_of_notMem hn, norm_zero]
    · rw [Set.indicator_of_mem (show I ∈ {I | I ∉ S} from hS)]
      exact (norm_indicator_le_norm_self _ _).trans (hgf I)
  rw [← tsum_ite_eq (⊤ : Ideal (𝓞 F)) (fun _ => (1 : ℂ)), ← (hg.indicator _).tsum_sub hite]
  have hsn : Summable (fun I => ‖(Cop (primesOf S)).indicator g I -
      (if I = ⊤ then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hf.indicator _)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (hsn.tsum_le_tsum hpt (hf.indicator _)).trans_eq ?_
  exact (tsum_subtype {I | I ∉ S} f).symm

/-- A finite set outside of which the tail of `f` is small. -/
theorem exists_tail_lt (f : Ideal (𝓞 F) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Ideal (𝓞 F)), ∑' I : {I // I ∉ S}, f I < ε :=
  ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds hε)).exists

end T12B

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

end T12B

end ArtinPrimitiveRoots
end

section
/-! # C3P_Zeta: the incomplete Dedekind zeta function `ζ^S`

`ζ^S(s) = ∏_{P ⊇ 𝔪}(1 − N P^{-s}) ζ_F(s) = R(s)/(s − 1)` with `R` entire, `R(1) = R_S`
(`sZetaResidue`), and `‖R(s)‖ ≤ C (2 + |Im s|)^k` on `9/10 ≤ Re s ≤ 12`. From 8087d96f
(`(s − 1) ζ_K` entire), 4f76b464 (convexity bound for `(s − 1) ζ_{K,T}`, here with `T = ∅`), the
Euler product 4d2ff9db, and Mathlib's class number formula; a field in an arbitrary universe is
replaced by a `Type` model. -/

set_option maxHeartbeats 1000000

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P


/-- `ζ^S`: the Dedekind zeta function with the Euler factors at the primes containing `𝔪`
removed. -/
noncomputable def zetaS {F : Type*} [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}, (1 - (Ideal.absNorm P : ℂ) ^ (-s))) *
    dedekindZeta F s

theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

theorem card_absNorm_eq_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K₁) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 K₂) // Ideal.absNorm I = n} := by
  set f : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K₁), Ideal.absNorm (I.map f) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm
  have h1 : ∀ I : Ideal (𝓞 K₁), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 K₂), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map f, by rw [hnorm]; exact I.2⟩
      invFun := fun J => ⟨J.1.map f.symm, by rw [← hnorm, h2]; exact J.2⟩
      left_inv := fun I => Subtype.ext (h1 I.1)
      right_inv := fun J => Subtype.ext (h2 J.1) }

theorem dedekindZeta_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) : dedekindZeta K₁ = dedekindZeta K₂ := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [card_absNorm_eq_congr e n]

/-- `(s − 1) ζ_F` continued: entire, with value the residue at 1 and polynomial growth on
`−1/2 ≤ Re s ≤ 5/2`. -/
theorem exists_R0 (F : Type u) [Field F] [NumberField F] :
    ∃ R0 : ℂ → ℂ, Differentiable ℂ R0 ∧ (∀ s : ℂ, 1 < s.re → R0 s = (s - 1) * dedekindZeta F s) ∧
      R0 1 = (dedekindZeta_residue F : ℂ) ∧
      ∃ C A : ℝ, 0 < A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖R0 s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨F₀, _, _, ⟨e⟩⟩ := exists_small_model F
  have hζ : dedekindZeta F₀ = dedekindZeta F := dedekindZeta_congr e
  obtain ⟨R0, hR0, -, hR0eq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
      F₀
  refine ⟨R0, hR0, fun s hs => by rw [hR0eq s hs, hζ], ?_, ?_⟩
  · -- the residue, by uniqueness of limits along real `s → 1⁺`
    have h1 : Tendsto (fun s : ℝ => R0 s) (𝓝[>] 1) (𝓝 (R0 1)) := by
      have := ((hR0 1).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1)))
      convert this using 2
      simp
    have h2 := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hR0eq s (by simpa using hs), hζ]
  · obtain ⟨C, A, -, hA, hb⟩ :=
      NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
        F₀ ∅
    refine ⟨C, A, hA, hb R0 hR0 fun s hs => ?_⟩
    rw [hR0eq s hs]
    congr 1
    have hp := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F₀ s hs
    rw [← hp.tprod_eq]
    exact ((Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)).tprod_eq
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀) =>
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).symm

/-- `‖ζ_F(s)‖` is bounded on `Re s ≥ 5/2`. -/
theorem exists_dedekindZeta_bound (F : Type*) [Field F] [NumberField F] :
    ∃ B : ℝ, ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := by
  set f : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)
  have hs0 : LSeriesSummable f ((5 / 2 : ℝ) : ℂ) := T12B.lseriesSummable_card (by norm_num)
  refine ⟨∑' n, ‖LSeries.term f ((5 / 2 : ℝ) : ℂ) n‖, fun s hs => ?_⟩
  have hre : ((5 / 2 : ℝ) : ℂ).re ≤ s.re := by simpa using hs
  have hss : LSeriesSummable f s := hs0.of_re_le_re hre
  unfold dedekindZeta
  refine (norm_tsum_le_tsum_norm hss.norm).trans ?_
  exact hss.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f hre n) hs0.norm

lemma finite_primes_ge {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪)).subset ?_
  intro P ⟨_, _, hle'⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
    (Ideal.absNorm_dvd_absNorm_of_le hle')

/-- The package for `ζ^S`. -/
theorem zetaS_package {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ (∀ s : ℂ, 1 < s.re → zetaS 𝔪 s = R s / (s - 1)) ∧
      R 1 = (sZetaResidue 𝔪 : ℂ) ∧
      ∃ C k : ℝ, 0 ≤ k ∧ ∀ s : ℂ, 9 / 10 ≤ s.re → s.re ≤ 12 → ‖R s‖ ≤ C * (2 + |s.im|) ^ k := by
  classical
  obtain ⟨R0, hR0, hR0eq, hR01, C, A, hA, hC⟩ := exists_R0 F
  obtain ⟨B₀, hB₀⟩ := exists_dedekindZeta_bound F
  set B := max B₀ 0
  have hB : ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := fun s hs =>
    (hB₀ s hs).trans (le_max_left _ _)
  have hfin := finite_primes_ge h𝔪
  set T := hfin.toFinset with hT
  have hTmem : ∀ P, P ∈ T ↔ P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P := fun P => by simp [hT]
  have hN0 : ∀ P ∈ T, (Ideal.absNorm P : ℂ) ≠ 0 := fun P hP => by
    have := ((hTmem P).1 hP).2.1
    exact_mod_cast (by rwa [Ne, Ideal.absNorm_eq_zero_iff] : Ideal.absNorm P ≠ 0)
  have hN1 : ∀ P ∈ T, (1 : ℝ) ≤ Ideal.absNorm P := fun P hP => by
    have := ((hTmem P).1 hP).2.1
    have : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  set E : ℂ → ℂ := fun s => ∏ P ∈ T, (1 - (Ideal.absNorm P : ℂ) ^ (-s))
  have hE : ∀ s, (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
      (1 - (Ideal.absNorm P : ℂ) ^ (-s))) = E s := fun s =>
    finprod_mem_eq_finite_toFinset_prod _ hfin
  have hEd : Differentiable ℂ E := by
    intro s
    refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    exact (differentiableAt_const _).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl (hN0 P hP)))
  have hEb : ∀ s : ℂ, 0 ≤ s.re → ‖E s‖ ≤ 2 ^ T.card := by
    intro s hs
    refine (Finset.norm_prod_le _ _).trans ?_
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
    refine (norm_sub_le _ _).trans ?_
    have hP1 := hN1 P hP
    have : ‖(Ideal.absNorm P : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [show ((Ideal.absNorm P : ℕ) : ℂ) = ((Ideal.absNorm P : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp; linarith)
    rw [norm_one]; linarith
  refine ⟨fun s => E s * R0 s, hEd.mul hR0, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : s - 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    rw [zetaS, hE]
    show E s * dedekindZeta F s = E s * R0 s / (s - 1)
    rw [hR0eq s hs]
    field_simp
  · simp only
    rw [hR01, sZetaResidue, finprod_mem_eq_finite_toFinset_prod _ hfin]
    push_cast
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [Complex.cpow_neg_one]
  · refine ⟨2 ^ T.card * max (max C 0) (11 * B), max A 1, by positivity, fun s h1 h2 => ?_⟩
    have hb1 : (1 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    rw [norm_mul]
    have hEs := hEb s (by linarith)
    have hRs : ‖R0 s‖ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 := by
      rcases le_total s.re (5 / 2) with h3 | h3
      · refine (hC s (by linarith) h3).trans ?_
        have : (2 + |s.im|) ^ A ≤ (2 + |s.im|) ^ max A 1 :=
          Real.rpow_le_rpow_of_exponent_le hb1 (le_max_left _ _)
        calc C * (2 + |s.im|) ^ A ≤ max C 0 * (2 + |s.im|) ^ A := by
              gcongr; exact le_max_left _ _
          _ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 :=
              mul_le_mul (le_max_left _ _) this (by positivity)
                (le_trans (by positivity) (le_max_left _ _))
      · have hs1 : 1 < s.re := by linarith
        rw [hR0eq s hs1, norm_mul]
        have hz := hB s h3
        have hB0 : 0 ≤ B := (norm_nonneg _).trans hz
        have hsn : ‖s - 1‖ ≤ 11 * (2 + |s.im|) := by
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          simp only [sub_re, one_re, sub_im, one_im, sub_zero]
          rw [abs_of_nonneg (by linarith)]
          linarith [abs_nonneg s.im]
        have hp : (2 + |s.im|) ≤ (2 + |s.im|) ^ max A 1 := by
          conv_lhs => rw [← Real.rpow_one (2 + |s.im|)]
          exact Real.rpow_le_rpow_of_exponent_le hb1 (le_max_right _ _)
        calc ‖s - 1‖ * ‖dedekindZeta F s‖ ≤ (11 * (2 + |s.im|)) * B := by gcongr
          _ = (11 * B) * (2 + |s.im|) := by ring
          _ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 := by
              gcongr
              · exact le_max_right _ _
    calc ‖E s‖ * ‖R0 s‖ ≤ 2 ^ T.card * (max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1) := by
          gcongr
      _ = _ := by ring

end C3P

end ArtinPrimitiveRoots
end

section
/-! # L2C_Arith: the arithmetic inputs of the row accounting

* `twistedL`: holomorphic and nonzero on `Re ξ > 1`, with `‖L^S(ξ, ηχ•(u))⁻¹‖ ≤ B` on
  `Re ξ ≥ σ₀ > 1`, `B` independent of `u` (the display on p. 57);
* `zetaSF`: holomorphic on `Re s > 1` and bounded on `Re s ≥ 12/5`;
* `SClass 𝔪` is finite (S-unit theorem, library stub), so `∑_u q_u^{-σ} < ∞` for `σ > 1`. -/

open NumberField Complex Filter Topology IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L2C

variable {F : Type*} [Field F] [NumberField F]

/-! ### Residue symbols -/

lemma residueSymbol_mul_ideal {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

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

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]
  simp

/-! ### The twisted coefficient and its `L`-series -/

/-- `a(𝔞) = η(𝔞) conj(χ_𝔞(u))`. -/
noncomputable def twCoeff (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (u : SInt 𝔪)
    (I : Ideal (𝓞 F)) : ℂ :=
  χ.toFun I * starRingEnd ℂ (residueSymbol ι 𝔪 I u)

lemma twCoeff_mul (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (u : SInt 𝔪)
    (I J : Ideal (𝓞 F)) : twCoeff ι χ u (I * J) = twCoeff ι χ u I * twCoeff ι χ u J := by
  unfold twCoeff
  by_cases hI : I = ⊥
  · subst hI; simp [T12B.toFun_bot]
  by_cases hJ : J = ⊥
  · subst hJ; simp [T12B.toFun_bot]
  rw [χ.map_mul', residueSymbol_mul_ideal I J hI hJ, map_mul]
  ring

lemma twCoeff_bot (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (u : SInt 𝔪) :
    twCoeff ι χ u ⊥ = 0 := by
  simp [twCoeff, T12B.toFun_bot]

lemma twCoeff_top (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (u : SInt 𝔪) :
    twCoeff ι χ u ⊤ = 1 := by
  simp [twCoeff, T12B.toFun_top, residueSymbol_top]

lemma norm_twCoeff_le (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪)
    (u : SInt 𝔪) (I : Ideal (𝓞 F)) : ‖twCoeff ι χ u I‖ ≤ 1 := by
  unfold twCoeff
  rw [norm_mul]
  rw [Complex.norm_conj]
  exact mul_le_one₀ (T12B.norm_le_one h𝔪 χ I) (norm_nonneg _) (norm_residueSymbol_le ι 𝔪 I u)

lemma twistedL_eq_tsum (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (u : SInt 𝔪)
    (ξ : ℂ) :
    twistedL ι χ u ξ = ∑' I : Ideal (𝓞 F), twCoeff ι χ u I * (Ideal.absNorm I : ℂ) ^ (-ξ) := by
  unfold twistedL twCoeff
  refine tsum_subtype_eq_of_support_subset (s := {I | IsExterior 𝔪 I})
    (f := fun I : Ideal (𝓞 F) => χ.toFun I * starRingEnd ℂ (residueSymbol ι 𝔪 I u) *
      (Ideal.absNorm I : ℂ) ^ (-ξ)) ?_
  intro I hI
  by_contra hne
  apply hI
  have : χ.toFun I = 0 := by
    rw [χ.eq_zero_iff']
    by_contra h
    push Not at h
    exact hne ⟨h.1, h.2⟩
  simp [this]

/-- Generic summand bound: `‖a(I) N(I)^{-s}‖ ≤ N(I)^{-σ}`. -/
lemma norm_term_le {a : Ideal (𝓞 F) → ℂ} (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} {σ : ℝ}
    (hσ : σ ≤ s.re) (I : Ideal (𝓞 F)) :
    ‖a I * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  by_cases hI : Ideal.absNorm I = 0
  · rw [Ideal.absNorm_eq_zero_iff.1 hI, ha0, zero_mul, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hI), Complex.neg_re]
  calc ‖a I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re)
      ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-σ) :=
        mul_le_mul (ha I) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = _ := one_mul _

/-- The uniform reciprocal bound for completely multiplicative coefficients of modulus `≤ 1`. -/
theorem inv_bound_gen {σ₀ : ℝ} (hσ : 1 < σ₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : Ideal (𝓞 F) → ℂ, (∀ I J, a (I * J) = a I * a J) → a ⊥ = 0 →
      a ⊤ = 1 → (∀ I, ‖a I‖ ≤ 1) → ∀ s : ℂ, σ₀ ≤ s.re →
        (∑' I, a I * (Ideal.absNorm I : ℂ) ^ (-s)) ≠ 0 ∧
        ‖(∑' I, a I * (Ideal.absNorm I : ℂ) ^ (-s))⁻¹‖ ≤ B := by
  obtain ⟨S, hS⟩ := T12B.exists_tail_lt
    (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ₀)) (by norm_num : (0 : ℝ) < 1 / 2)
  set f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ₀)
  have hf0 : ∀ I, 0 ≤ f I := fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set C := ∏ P ∈ T12B.primesOf S, (1 + f P) with hC
  have hCpos : 0 < C := Finset.prod_pos fun P _ => by linarith [hf0 P]
  refine ⟨2 * C, by positivity, fun a hmul ha0 ha1 ha s hs => ?_⟩
  set g : Ideal (𝓞 F) → ℂ := fun I => a I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hgmul : ∀ I J, g (I * J) = g I * g J := fun I J => by
    simp only [g, hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hg0 : g ⊥ = 0 := by simp [g, ha0]
  have hg1 : g ⊤ = 1 := by simp [g, ha1]
  have hgf : ∀ I, ‖g I‖ ≤ f I := fun I => norm_term_le ha0 ha hs I
  have hb := T12B.sieve_bound g hgmul hg0 hg1 f (T12B.summable_absNorm_rpow hσ) hgf S
  have hprod : ‖∏ P ∈ T12B.primesOf S, (1 - g P)‖ ≤ C := by
    refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      fun P _ => ?_)
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hgf P])
  set L := ∑' I, g I
  have hlow : 1 / 2 ≤ ‖L‖ * C := by
    have h1 : (1 : ℝ) ≤ ‖L * ∏ P ∈ T12B.primesOf S, (1 - g P)‖ + 1 / 2 := by
      have := norm_sub_norm_le (1 : ℂ) (L * ∏ P ∈ T12B.primesOf S, (1 - g P))
      rw [norm_one, norm_sub_rev] at this
      linarith
    rw [norm_mul] at h1
    nlinarith [norm_nonneg L]
  have hL : 0 < ‖L‖ := by
    by_contra h
    have : ‖L‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [this, zero_mul] at hlow
    linarith
  refine ⟨norm_pos_iff.1 hL, ?_⟩
  rw [norm_inv, inv_le_comm₀ hL (by positivity)]
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The twisted `L`-series: nonvanishing and the uniform reciprocal bound. -/
theorem twistedL_inv_bound {σ₀ : ℝ} (hσ : 1 < σ₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ → ∀ (χ : HeckeChar F 𝔪)
      (u : SInt 𝔪) (s : ℂ), σ₀ ≤ s.re → twistedL ι χ u s ≠ 0 ∧ ‖(twistedL ι χ u s)⁻¹‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := inv_bound_gen (F := F) hσ
  refine ⟨B, hB0, fun ι 𝔪 h𝔪 χ u s hs => ?_⟩
  rw [twistedL_eq_tsum]
  exact hB (twCoeff ι χ u) (twCoeff_mul ι χ u) (twCoeff_bot ι χ u) (twCoeff_top ι χ u)
    (norm_twCoeff_le ι h𝔪 χ u) s hs

/-- `L^S(ξ, ηχ•(u))` is holomorphic on `Re ξ > 1`. -/
theorem differentiableOn_twistedL (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (χ : HeckeChar F 𝔪) (u : SInt 𝔪) :
    DifferentiableOn ℂ (twistedL ι χ u) {s | 1 < s.re} := by
  intro s hs
  obtain ⟨σ, h1, h2⟩ := exists_between (show (1 : ℝ) < s.re from hs)
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun s => ∑' I : Ideal (𝓞 F),
      twCoeff ι χ u I * (Ideal.absNorm I : ℂ) ^ (-s)) {s : ℂ | σ < s.re} := by
    refine differentiableOn_tsum_of_summable_norm (T12B.summable_absNorm_rpow h1) ?_ hU ?_
    · intro I
      by_cases hI : Ideal.absNorm I = 0
      · rw [Ideal.absNorm_eq_zero_iff.1 hI]
        simp only [twCoeff_bot, zero_mul]
        exact differentiableOn_const _
      · have hI' : (Ideal.absNorm I : ℂ) ≠ 0 := by exact_mod_cast hI
        exact (differentiableOn_const _).mul
          (fun w _ => (differentiableAt_id.neg.const_cpow (Or.inl hI')).differentiableWithinAt)
    · intro I w hw
      exact norm_term_le (twCoeff_bot ι χ u) (norm_twCoeff_le ι h𝔪 χ u) (le_of_lt hw) I
  have := (hd s h2).differentiableAt (hU.mem_nhds h2)
  have heq : twistedL ι χ u = fun s => ∑' I : Ideal (𝓞 F),
      twCoeff ι χ u I * (Ideal.absNorm I : ℂ) ^ (-s) := funext (twistedL_eq_tsum ι χ u)
  rw [heq]
  exact this.differentiableWithinAt

/-! ### `ζ^S` -/

theorem differentiableOn_zetaSF {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    DifferentiableOn ℂ (zetaSF 𝔪) {s | 1 < s.re} := by
  obtain ⟨R, hR, hRz, -, -⟩ := C3P.zetaS_package h𝔪
  intro s hs
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith [show (1 : ℝ) < s.re from hs]
  have hd : DifferentiableAt ℂ (fun s => R s / (s - 1)) s :=
    (hR s).div (differentiableAt_id.sub_const 1) h1
  have heq : zetaSF 𝔪 =ᶠ[𝓝 s] fun s => R s / (s - 1) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    exact hRz t ht
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

theorem exists_zetaSF_bound {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 12 / 5 ≤ s.re → ‖zetaSF 𝔪 s‖ ≤ B := by
  classical
  set f : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)
  have hs0 : LSeriesSummable f ((12 / 5 : ℝ) : ℂ) := T12B.lseriesSummable_card (by norm_num)
  set B₀ := ∑' n, ‖LSeries.term f ((12 / 5 : ℝ) : ℂ) n‖
  have hB₀ : ∀ s : ℂ, 12 / 5 ≤ s.re → ‖dedekindZeta F s‖ ≤ B₀ := by
    intro s hs
    have hre : ((12 / 5 : ℝ) : ℂ).re ≤ s.re := by simpa using hs
    have hss : LSeriesSummable f s := hs0.of_re_le_re hre
    unfold dedekindZeta
    refine (norm_tsum_le_tsum_norm hss.norm).trans ?_
    exact hss.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f hre n) hs0.norm
  have hB0 : 0 ≤ B₀ := tsum_nonneg fun _ => norm_nonneg _
  have hfin := C3P.finite_primes_ge h𝔪
  set T := hfin.toFinset with hT
  refine ⟨2 ^ T.card * B₀, by positivity, fun s hs => ?_⟩
  unfold zetaSF
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, norm_mul]
  have hE : ‖∏ P ∈ T, (1 - (Ideal.absNorm P : ℂ) ^ (-s))‖ ≤ 2 ^ T.card := by
    refine (Finset.norm_prod_le _ _).trans ?_
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
    refine (norm_sub_le _ _).trans ?_
    have hPm : P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P := by simpa [hT] using hP
    have hN : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hPm.2.1
    have hP1 : (1 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
    have : ‖(Ideal.absNorm P : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp; linarith)
    rw [norm_one]; linarith
  exact mul_le_mul hE (hB₀ s hs) (norm_nonneg _) (by positivity)

/-! ### Finiteness of `U_S / U_S^6` and the frequency sums -/

lemma finite_placesOf {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  have hfin := C3P.finite_primes_ge h𝔪
  refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) ?_
    (fun v _ w _ h => HeightOneSpectrum.ext h)
  refine hfin.subset ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v.isPrime, v.ne_bot, hv⟩

theorem finite_sClass (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  haveI : Finite (placesOf 𝔪) := (finite_placesOf h𝔪).to_subtype
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) ℚ F
    (Set.mem_singleton n) hn0.ne'
  have h6 : (6 : ℕ) ∣ n := (show (6 : ℕ) ∣ 12 by norm_num).trans hn
  have hζ6 : IsPrimitiveRoot (ζ ^ (n / 6)) 6 := by
    have := hζ.pow_of_dvd (p := n / 6) (Nat.div_pos (Nat.le_of_dvd hn0 h6) (by norm_num)).ne'
      (Nat.div_dvd_of_dvd h6)
    rwa [Nat.div_div_self h6 hn0.ne'] at this
  have hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨ζ ^ (n / 6), (mem_primitiveRoots (by norm_num)).2 hζ6⟩
  have hc := NumberField.natCard_sUnit_quotient_range_powMonoidHom F (placesOf 𝔪) hμ
  apply Nat.finite_of_card_ne_zero
  show Nat.card (↥((placesOf 𝔪).unit F) ⧸
    (powMonoidHom 6 : ↥((placesOf 𝔪).unit F) →* ↥((placesOf 𝔪).unit F)).range) ≠ 0
  rw [hc]
  positivity

lemma one_le_absNorm_of_exterior {𝔪 I : Ideal (𝓞 F)} (h : IsExterior 𝔪 I) :
    1 ≤ Ideal.absNorm I :=
  Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h.1)

/-- `∑_u q_u^{-σ} < ∞` for `σ > 1`. -/
theorem summable_freq (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun r : FreqClass 𝔪 => ((Ideal.absNorm r.1.1 : ℕ) : ℝ) ^ (-σ) := by
  haveI := finite_sClass n hn0 hn h𝔪
  have h1 : Summable fun 𝔲 : {𝔲 : Ideal (𝓞 F) // IsExterior 𝔪 𝔲 ∧ IsSixthPowerFree 𝔲} =>
      ((Ideal.absNorm 𝔲.1 : ℕ) : ℝ) ^ (-σ) :=
    (T12B.summable_absNorm_rpow hσ).subtype _
  have h2 : Summable fun _ : SClass 𝔪 => (1 : ℝ) := Summable.of_finite
  have := h1.mul_of_nonneg h2 (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => zero_le_one)
  simpa using this

end L2C

end ArtinPrimitiveRoots
end

section
/-! # L92M_Basic: Mellin transforms of smooth functions supported in `[a, b] ⊂ (0, ∞)`

For `g : ℝ → ℝ` continuous with `tsupport g ⊆ Icc a b`, `0 < a`, the Mellin transform of
`(g · : ℂ)` is entire and bounded on vertical strips; for smooth `g`, integration by parts
(`D g t = t g'(t)`, `mellin (D g) s = -s mellin g s`) gives decay faster than any power of `|Im s|`.
-/

namespace ArtinPrimitiveRoots.L92M

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval ContDiff

section General

variable {g : ℝ → ℝ} {a b : ℝ}

lemma vanish_of_tsupport (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (t : ℝ)
    (ht : t ∉ Ioo (a / 2) (max a b + 1)) : g t = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ht ?_
  have := hs h
  exact ⟨by linarith [this.1], by linarith [this.2, le_max_right a b]⟩

lemma lt_bounds (ha : 0 < a) : 0 < a / 2 ∧ a / 2 < max a b + 1 :=
  ⟨by linarith, by linarith [le_max_left a b]⟩

lemma cpow_continuousOn (s : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (Ioi 0) :=
  fun _ ht => (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).continuousWithinAt

lemma hasCompactSupport_of_tsupport (hs : tsupport g ⊆ Icc a b) : HasCompactSupport g :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hs

lemma mellin_eq_intervalIntegral (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (s : ℂ) :
    mellin (fun t => (g t : ℂ)) s =
      ∫ t in (a / 2)..(max a b + 1), (t : ℂ) ^ (s - 1) * (g t : ℂ) := by
  rw [mellin, intervalIntegral.integral_of_le (lt_bounds (b := b) ha).2.le]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · intro t ht
    exact lt_trans (lt_bounds (b := b) ha).1 ht.1
  · intro t ht
    have : t ∉ Ioo (a / 2) (max a b + 1) := fun h' => ht.2 ⟨h'.1, h'.2.le⟩
    simp [vanish_of_tsupport ha hs t this]

lemma mellin_differentiable_of_tsupport (hc : Continuous g) (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) : Differentiable ℂ (mellin (fun t => (g t : ℂ))) := by
  intro s
  have hF : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0) :=
    (continuous_ofReal.comp hc).locallyIntegrable.locallyIntegrableOn _
  have htop : (fun t => (g t : ℂ)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (max a b + 1)] with t ht
    simp [vanish_of_tsupport ha hs t fun h => absurd h.2 (not_lt.mpr ht.le)]
  have hbot : (fun t => (g t : ℂ)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a / 2 by linarith)] with t ht
    simp [vanish_of_tsupport ha hs t fun h => absurd h.1 (not_lt.mpr ht.2.le)]
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hF
    ((isBigO_zero _ _).congr' htop.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hbot.symm EventuallyEq.rfl) (by linarith)

/-- Boundedness of the Mellin transform on vertical strips. -/
lemma mellin_bounded_strip (hc : Continuous g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (σ₁ σ₂ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C := by
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_of_tsupport hs)
  have hcomp : IsCompact (Icc σ₁ σ₂ ×ˢ Icc α β) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ (p.1 - 1)) (Icc σ₁ σ₂ ×ˢ Icc α β) := by
    intro p hp
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.rpow continuousAt_snd (continuousAt_fst.sub continuousAt_const) ?_
    left
    have := hp.2.1
    exact ne_of_gt (lt_of_lt_of_le hαβ.1 this)
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max (B * max M 0 * (β - α)) 0, le_max_right _ _, fun s h1 h2 => ?_⟩
  rw [mellin_eq_intervalIntegral ha hs]
  refine le_trans ?_ (le_max_left _ _)
  have : ∀ t ∈ Ι α β, ‖(t : ℂ) ^ (s - 1) * (g t : ℂ)‖ ≤ B * max M 0 := by
    intro t ht
    have ht2 : t ∈ Ioc α β := by rwa [uIoc_of_le hαβ.2.le] at ht
    have ht' : t ∈ Icc α β := ⟨ht2.1.le, ht2.2⟩
    have htpos : 0 < t := lt_of_lt_of_le hαβ.1 ht'.1
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos, norm_real]
    have hb := hB (s.re, t) ⟨⟨h1, h2⟩, ht'⟩
    simp only [Real.norm_eq_abs] at hb
    rw [abs_of_nonneg (Real.rpow_nonneg htpos.le _)] at hb
    have hgt : ‖g t‖ ≤ max M 0 := le_trans (hM t) (le_max_left _ _)
    exact mul_le_mul hb hgt (norm_nonneg _) (le_trans (Real.rpow_nonneg htpos.le _) hb)
  have := intervalIntegral.norm_integral_le_of_norm_le_const this
  rwa [abs_of_pos (sub_pos.mpr hαβ.2)] at this

end General

section IBP

variable {g : ℝ → ℝ} {a b : ℝ}

/-- `D g t = t g'(t)`. -/
noncomputable def Dop (g : ℝ → ℝ) : ℝ → ℝ := fun t => t * deriv g t

lemma tsupport_Dop_subset (g : ℝ → ℝ) : tsupport (Dop g) ⊆ tsupport g :=
  (tsupport_mul_subset_right (f := fun t => t)).trans tsupport_deriv_subset

lemma contDiff_Dop (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (Dop g) :=
  contDiff_id.mul (contDiff_infty_iff_deriv.mp hg).2

lemma hasDerivAt_ofReal_cpow (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t := by
  have h1 : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have := ((hasDerivAt_id (t : ℂ)).cpow_const (c := s) h1).comp_ofReal
  simpa using this

/-- Integration by parts: `mellin (t g'(t)) s = -s mellin g s`. -/
lemma mellin_Dop (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (s : ℂ) :
    mellin (fun t => (Dop g t : ℂ)) s = -s * mellin (fun t => (g t : ℂ)) s := by
  have hs' : tsupport (Dop g) ⊆ Icc a b := (tsupport_Dop_subset g).trans hs
  rw [mellin_eq_intervalIntegral ha hs', mellin_eq_intervalIntegral ha hs]
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcd : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hpos : ∀ t ∈ uIcc α β, 0 < t := by
    intro t ht
    rw [uIcc_of_le hαβ.2.le] at ht
    exact lt_of_lt_of_le hαβ.1 ht.1
  have h1 : ∫ t in α..β, (t : ℂ) ^ (s - 1) * ((Dop g t : ℝ) : ℂ) =
      ∫ t in α..β, (t : ℂ) ^ s * ((deriv g t : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos t ht).ne'
    simp only [Dop, ofReal_mul]
    rw [← mul_assoc]
    congr 1
    conv_rhs => rw [show s = (s - 1) + 1 by ring, cpow_add _ _ htc, cpow_one]
  rw [h1]
  have hu : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t :=
    fun t ht => hasDerivAt_ofReal_cpow s (hpos t ht)
  have hv : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (g y : ℂ)) ((deriv g t : ℝ) : ℂ) t :=
    fun t _ => (hdiff t).hasDerivAt.ofReal_comp
  have hu' : IntervalIntegrable (fun t : ℝ => s * (t : ℂ) ^ (s - 1)) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul ((cpow_continuousOn (s - 1)).mono fun t ht => hpos t ht)
  have hv' : IntervalIntegrable (fun t : ℝ => ((deriv g t : ℝ) : ℂ)) volume α β :=
    (continuous_ofReal.comp hcd).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hgα : g α = 0 := vanish_of_tsupport ha hs α (fun h => lt_irrefl _ h.1)
  have hgβ : g β = 0 := vanish_of_tsupport ha hs β (fun h => lt_irrefl _ h.2)
  rw [hgα, hgβ]
  simp only [ofReal_zero, mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

lemma mellin_Dop_iterate (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (N : ℕ) : ContDiff ℝ ∞ (Dop^[N] g) ∧ tsupport (Dop^[N] g) ⊆ Icc a b ∧
      ∀ s : ℂ, mellin (fun t => (Dop^[N] g t : ℂ)) s = (-s) ^ N * mellin (fun t => (g t : ℂ)) s := by
  induction N with
  | zero => exact ⟨hg, hs, fun s => by simp⟩
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨contDiff_Dop h1, (tsupport_Dop_subset _).trans h2, fun s => ?_⟩
    rw [mellin_Dop h1 ha h2, h3, pow_succ]
    ring

lemma one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + u ^ N) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg hu N])
  · calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * u ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + u ^ N) := by gcongr; linarith

/-- Rapid decay on vertical strips, with a nonnegative constant. -/
lemma mellin_decay_aux (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (N : ℕ) (σ₁ σ₂ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C / (1 + |s.im|) ^ N := by
  obtain ⟨h1, h2, h3⟩ := mellin_Dop_iterate hg ha hs N
  obtain ⟨C₀, hC₀, hb₀⟩ := mellin_bounded_strip hg.continuous ha hs σ₁ σ₂
  obtain ⟨C₁, hC₁, hb₁⟩ := mellin_bounded_strip h1.continuous ha h2 σ₁ σ₂
  refine ⟨2 ^ N * (C₀ + C₁), by positivity, fun s hs1 hs2 => ?_⟩
  have hpos : 0 < (1 + |s.im|) ^ N := by positivity
  rw [le_div_iff₀ hpos]
  have e1 : ‖s‖ ^ N * ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C₁ := by
    have := hb₁ s hs1 hs2
    rw [h3 s, norm_mul, norm_pow, norm_neg] at this
    exact this
  have e0 := hb₀ s hs1 hs2
  have him : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  calc ‖mellin (fun t => (g t : ℂ)) s‖ * (1 + |s.im|) ^ N
      ≤ ‖mellin (fun t => (g t : ℂ)) s‖ * (2 ^ N * (1 + |s.im| ^ N)) := by
        gcongr; exact one_add_pow_le _ (abs_nonneg _) N
    _ ≤ ‖mellin (fun t => (g t : ℂ)) s‖ * (2 ^ N * (1 + ‖s‖ ^ N)) := by
        gcongr
    _ = 2 ^ N * (‖mellin (fun t => (g t : ℂ)) s‖ + ‖s‖ ^ N * ‖mellin (fun t => (g t : ℂ)) s‖) := by
        ring
    _ ≤ 2 ^ N * (C₀ + C₁) := by gcongr

end IBP

section Main

variable (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
  (hab : tsupport f ⊆ Set.Icc a b)

include hf ha hab

omit hf ha hab in
/-- M0 -/
theorem exists_tsupport_subset_Icc (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Set.Ioi 0) : ∃ a b : ℝ, 0 < a ∧ tsupport f ⊆ Set.Icc a b := by
  rcases (tsupport f).eq_empty_or_nonempty with he | hne
  · exact ⟨1, 1, one_pos, by simp [he]⟩
  · obtain ⟨m, hm, hmin⟩ := hfc.isCompact.exists_isMinOn hne continuousOn_id
    obtain ⟨M, hM⟩ := hfc.isCompact.bddAbove
    exact ⟨m, M, hfs hm, fun t ht => ⟨hmin ht, hM ht⟩⟩

/-- M3a -/
theorem mellin_differentiable : Differentiable ℂ (mellin (fun u : ℝ => (f u : ℂ))) :=
  mellin_differentiable_of_tsupport hf.continuous ha hab

/-- M3b' -/
theorem mellin_decay_rpow (A σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun u : ℝ => (f u : ℂ)) s‖ ≤ C * (1 + |s.im|) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := mellin_decay_aux hf ha hab ⌈A⌉₊ σ₁ σ₂
  refine ⟨C, fun s h1 h2 => le_trans (hC s h1 h2) ?_⟩
  have hb : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hb (by linarith [Nat.le_ceil A])) hC0

end Main

end ArtinPrimitiveRoots.L92M
end

section
/-! # L2C_Main: C4 = (8.21) from the three cuts

`chk_exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le_of_cuts` proves the statement of C4
(acc3edd1) verbatim from `RowFactorization` (Prop 7.3, u ≠ 1), `KummerConvexity` ((8.14)) and
`ZeroDetector` (Prop 8.2, (8.4)). -/

open NumberField Complex MeasureTheory Filter Topology

namespace ArtinPrimitiveRoots

namespace L2C

variable {F : Type*} [Field F] [NumberField F]

lemma smallPrimesDvd_mono' {N N' : ℕ} (h : N ≤ N') {𝔪 : Ideal (𝓞 F)}
    (h𝔪 : SmallPrimesDvd N' 𝔪) : SmallPrimesDvd N 𝔪 :=
  fun P hP hP0 hPN => h𝔪 P hP hP0 (hPN.trans h)

/-- The row integral as a triple line integral of `Phi`. -/
lemma rowIntegral_eq {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪)
    (W₁ : ℝ → ℝ) (M : ℂ → ℂ) (r : FreqClass 𝔪) (Z : ℝ) (G : ℂ → ℂ → ℂ → ℂ)
    (hG : ∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
      χ.freqSeries g (freqElt g r) ξ w z = G ξ w z) :
    χ.rowIntegral g W₁ M r (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z =
      ((2 * Real.pi) ^ 3 : ℂ)⁻¹ * I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M
        (mellin fun t => (W₁ t : ℂ)) (Ideal.absNorm r.1.1) G) 4 4 2 := by
  unfold HeckeChar.rowIntegral I3 Phi C3P.Ef
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t1 => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t2 => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t3 => ?_)
  simp only [Complex.ofReal_ofNat]
  rw [hG _ _ _ (by simp; norm_num) (by simp; norm_num) (by simp)]

lemma rpow_mul_rpow {q : ℝ} (hq : 0 < q) (a b : ℝ) : q ^ a * q ^ b = q ^ (a + b) :=
  (Real.rpow_add hq a b).symm

/-- One row: the hypotheses `RowHyp` and the identification of `ℱ_u` with `Gf`. -/
lemma row_data {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪)
    (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪) {A A0 κ CΛ CH BZ BL : ℝ} (hA : A0 ≤ A)
    (hA0 : 0 ≤ A) (hBZ0 : 0 ≤ BZ) (hBZ : ∀ s : ℂ, 12 / 5 ≤ s.re → ‖zetaSF 𝔪 s‖ ≤ BZ)
    (hBL0 : 0 ≤ BL) (hBL : ∀ s : ℂ, s1 ≤ s.re →
      twistedL ι χ (freqElt g r) s ≠ 0 ∧ ‖(twistedL ι χ (freqElt g r) s)⁻¹‖ ≤ BL)
    (Λ : ℂ → ℂ) (hΛd : Differentiable ℂ Λ)
    (hΛeq : ∀ w : ℂ, 1 < w.re → Λ w = kummerL ι 𝔪 (freqElt g r) w)
    (hΛb : ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
      ‖Λ w‖ ≤ CΛ * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + κ) * (2 + |w.im|) ^ A0)
    (H : ℂ → ℂ → ℂ → ℂ)
    (hHd : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) regionOne)
    (hHb : ∀ p ∈ regionOne, ‖H p.1 p.2.1 p.2.2‖ ≤ CH * (Ideal.absNorm r.1.1 : ℝ) ^ κ)
    (hid : ∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
      χ.freqSeries g (freqElt g r) ξ w z * twistedL ι χ (freqElt g r) ξ =
        zetaSF 𝔪 (6 * z) * kummerL ι 𝔪 (freqElt g r) w * H ξ w z) :
    RowHyp (zetaSF 𝔪) Λ (twistedL ι χ (freqElt g r)) H A BZ
        (max CΛ 0 * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + κ))
        (max CH 0 * (Ideal.absNorm r.1.1 : ℝ) ^ κ) BL ∧
      ∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
        χ.freqSeries g (freqElt g r) ξ w z =
          Gf (zetaSF 𝔪) Λ (twistedL ι χ (freqElt g r)) H ξ w z := by
  have hL0 : ∀ s : ℂ, 1 < s.re → twistedL ι χ (freqElt g r) s ≠ 0 := by
    intro s hs
    obtain ⟨B, -, hB⟩ := twistedL_inv_bound (F := F) (σ₀ := s.re) hs
    exact (hB ι 𝔪 h𝔪 χ (freqElt g r) s le_rfl).1
  have hq0 : 0 ≤ (Ideal.absNorm r.1.1 : ℝ) := Nat.cast_nonneg _
  refine ⟨⟨differentiableOn_zetaSF h𝔪, hBZ, hΛd, fun w h1 h2 => ?_, hHd, fun p hp => ?_,
    differentiableOn_twistedL ι h𝔪 χ _, hL0, fun s hs => (hBL s hs).2, hA0, hBZ0,
    by positivity, by positivity, hBL0⟩, fun ξ w z h1 h2 h3 => ?_⟩
  · refine (hΛb w h1 h2).trans ?_
    have hb1 : (1 : ℝ) ≤ 2 + |w.im| := by linarith [abs_nonneg w.im]
    have e1 : (2 + |w.im|) ^ A0 ≤ (2 + |w.im|) ^ A := Real.rpow_le_rpow_of_exponent_le hb1 hA
    have e2 : CΛ ≤ max CΛ 0 := le_max_left _ _
    have : 0 ≤ (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + κ) := by positivity
    have : 0 ≤ (2 + |w.im|) ^ A0 := by positivity
    calc CΛ * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + κ) * (2 + |w.im|) ^ A0
        ≤ max CΛ 0 * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + κ) * (2 + |w.im|) ^ A0 := by gcongr
      _ ≤ _ := by gcongr
  · refine (hHb p hp).trans ?_
    gcongr
    exact le_max_left _ _
  · have hL := hL0 ξ (by linarith)
    have := hid ξ w z h1 h2 h3
    rw [← hΛeq w (by linarith)] at this
    unfold Gf
    field_simp
    linear_combination this

/-- `(2^k)^{1/2} = (2^{1/2})^k`. -/
lemma two_pow_half (k : ℕ) : ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) = ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast
    ((2 : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul (by norm_num), mul_comm]

/-- `∑_{k ≤ K} (2^k)^{1/2} ≤ 4 (2^K)^{1/2}`. -/
lemma sum_sqrt_two_pow_le (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) ≤ 4 * ((2 : ℝ) ^ K) ^ (1 / 2 : ℝ) := by
  have hx2' : ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  set x : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ)
  have hx2 : x ^ 2 = 2 := hx2'
  have hx0 : 0 < x := by positivity
  have hx1 : 4 / 3 ≤ x := by nlinarith
  simp_rw [two_pow_half]
  rw [geom_sum_eq (ne_of_gt (by linarith))]
  have hxm : 0 < x - 1 := by linarith
  rw [div_le_iff₀ hxm, pow_succ]
  have hxK : 0 ≤ x ^ K := by positivity
  nlinarith

set_option maxHeartbeats 2000000 in
theorem chk_exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le_of_cuts (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) (hA : RowFactorization F ι) (hB : KummerConvexity F ι)
    (hC : ZeroDetector F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖∑' r : {r : FreqClass 𝔪 // r ≠ principalFreq 𝔪},
                χ.rowIntegral g W₁ M r.1 (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2500) := by
  classical
  obtain ⟨NA, hA⟩ := hA
  obtain ⟨NB, hB⟩ := hB
  obtain ⟨NC, hC⟩ := hC
  refine ⟨max NA (max NB NC), fun 𝔪 h𝔪 hS χ g W₁ M hW hM => ?_⟩
  have hSA : SmallPrimesDvd NA 𝔪 := smallPrimesDvd_mono' (le_max_left _ _) hS
  have hSB : SmallPrimesDvd NB 𝔪 :=
    smallPrimesDvd_mono' ((le_max_left _ _).trans (le_max_right _ _)) hS
  have hSC : SmallPrimesDvd NC 𝔪 :=
    smallPrimesDvd_mono' ((le_max_right _ _).trans (le_max_right _ _)) hS
  set κ : ℝ := 1 / 1000 with hκ
  obtain ⟨A0, hBk⟩ := hB 𝔪 h𝔪 hSB g
  set A := max A0 0
  obtain ⟨CΛ, hΛ⟩ := hBk κ (by norm_num)
  obtain ⟨CH, hH⟩ := hA 𝔪 h𝔪 hSA χ g κ (by norm_num)
  obtain ⟨ρ, hρ, C₀, U₀, E, hEc, hD⟩ := hC 𝔪 h𝔪 hSC χ g
  obtain ⟨CD, hDk⟩ := hD κ (by norm_num)
  obtain ⟨BL, hBL0, hBL⟩ := twistedL_inv_bound (F := F) (σ₀ := s1) s1_gt
  obtain ⟨BZ, hBZ0, hBZ⟩ := exists_zetaSF_bound h𝔪
  -- the weights
  obtain ⟨a, b, ha, hab⟩ := L92M.exists_tsupport_subset_Icc W₁ hW.2.1 hW.2.2
  set Wh := mellin (fun t : ℝ => (W₁ t : ℂ)) with hWh
  have hwt : WeightHyp M Wh := ⟨hM, L92M.mellin_differentiable W₁ hW.1 a b ha hab,
    fun A' σa σb => L92M.mellin_decay_rpow W₁ hW.1 a b ha hab A' σa σb⟩
  set N : ℝ := 2 + 2 / ρ with hNdef
  have hN : 2 ≤ N := by have : 0 ≤ 2 / ρ := by positivity
                        linarith
  obtain ⟨KI, hKI0, hKI⟩ := row_bound_small hwt A
  obtain ⟨KIII, hKIII0, hKIII⟩ := row_bound_large hwt A
  obtain ⟨KII, hKII0, hKII⟩ := row_bound_good hwt A N hN
  -- the rows
  choose! Hf hHd hHb hHid using hH
  choose! Λf hΛd hΛeq hΛb using hΛ
  set ι' := {r : FreqClass 𝔪 // r ≠ principalFreq 𝔪}
  set q : ι' → ℕ := fun r => Ideal.absNorm r.1.1.1 with hqdef
  have hq1 : ∀ r : ι', 1 ≤ q r := fun r => one_le_absNorm_of_exterior r.1.1.2.1
  have hrow : ∀ r : ι', RowHyp (zetaSF 𝔪) (Λf r.1) (twistedL ι χ (freqElt g r.1)) (Hf r.1) A BZ
        (max CΛ 0 * (q r : ℝ) ^ (1 / 2 + κ)) (max CH 0 * (q r : ℝ) ^ κ) BL ∧
      ∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
        χ.freqSeries g (freqElt g r.1) ξ w z =
          Gf (zetaSF 𝔪) (Λf r.1) (twistedL ι χ (freqElt g r.1)) (Hf r.1) ξ w z := fun r =>
    row_data h𝔪 χ g r.1 (le_max_left _ _) (le_max_right _ _) hBZ0 hBZ hBL0
      (fun s hs => hBL ι 𝔪 h𝔪 χ _ s hs) (Λf r.1) (hΛd r.1 r.2) (hΛeq r.1 r.2) (hΛb r.1 r.2)
      (Hf r.1) (hHd r.1 r.2) (hHb r.1 r.2) (hHid r.1 r.2)
  -- the exceptional rows and their count
  set U1 : ℝ := max U₀ 1
  set exc : ι' → Prop := fun r => 2 * U1 ≤ (q r : ℝ) ∧ r.1 ∈ E ((2 : ℝ) ^ Nat.log 2 (q r))
  set Fs : ℝ → Finset ι' := fun V => Finset.subtype (fun r => r ≠ principalFreq 𝔪)
    (((Finset.range (Nat.log 2 ⌊V⌋₊ + 1)).filter fun k => U₀ ≤ (2 : ℝ) ^ k).biUnion
      fun k => E ((2 : ℝ) ^ k))
  have hpow : ∀ r : ι', (2 : ℝ) ^ Nat.log 2 (q r) ≤ q r ∧ (q r : ℝ) < 2 * 2 ^ Nat.log 2 (q r) := by
    intro r
    have h1 := Nat.pow_log_le_self 2 (show q r ≠ 0 by have := hq1 r; omega)
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (q r)
    refine ⟨by exact_mod_cast h1, ?_⟩
    rw [pow_succ] at h2
    have : (q r : ℝ) < (2 ^ Nat.log 2 (q r) * 2 : ℕ) := by exact_mod_cast h2
    push_cast at this
    linarith
  have hFin : ∀ V : ℝ, ∀ r : ι', exc r → ((q r : ℕ) : ℝ) ≤ V → r ∈ Fs V := by
    intro V r hr hrV
    obtain ⟨h1, h2⟩ := hpow r
    rw [Finset.mem_subtype, Finset.mem_biUnion]
    refine ⟨Nat.log 2 (q r), Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.log_mono_right (Nat.le_floor hrV))), ?_⟩, hr.2⟩
    have : U₀ ≤ U1 := le_max_left _ _
    linarith [hr.1]
  have hFc : ∀ V : ℝ, 1 ≤ V → ((Fs V).card : ℝ) ≤ (4 * max C₀ 0) * V ^ (1 / 2 : ℝ) := by
    intro V hV
    set K := Nat.log 2 ⌊V⌋₊
    have hcard : (Fs V).card ≤ ∑ k ∈ (Finset.range (K + 1)).filter (fun k => U₀ ≤ (2 : ℝ) ^ k),
        (E ((2 : ℝ) ^ k)).card :=
      (Finset.card_subtype _ _).le.trans ((Finset.card_filter_le _ _).trans Finset.card_biUnion_le)
    have h1 : ((Fs V).card : ℝ) ≤ ∑ k ∈ (Finset.range (K + 1)).filter
        (fun k => U₀ ≤ (2 : ℝ) ^ k), ((E ((2 : ℝ) ^ k)).card : ℝ) := by exact_mod_cast hcard
    refine h1.trans ?_
    have h2 : ∑ k ∈ (Finset.range (K + 1)).filter (fun k => U₀ ≤ (2 : ℝ) ^ k),
        ((E ((2 : ℝ) ^ k)).card : ℝ) ≤ ∑ k ∈ Finset.range (K + 1),
          max C₀ 0 * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) := by
      refine (Finset.sum_le_sum fun k hk => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => by
          positivity)
      refine (hEc _ (Finset.mem_filter.1 hk).2).trans ?_
      gcongr; exact le_max_left _ _
    refine h2.trans ?_
    rw [← Finset.mul_sum]
    have h3 := sum_sqrt_two_pow_le K
    have h4 : ((2 : ℝ) ^ K) ^ (1 / 2 : ℝ) ≤ V ^ (1 / 2 : ℝ) := by
      have h5 : ((2 : ℕ) ^ K : ℕ) ≤ ⌊V⌋₊ := Nat.pow_log_le_self 2 (by
        have := Nat.floor_pos.2 hV; omega)
      have h6 : (2 : ℝ) ^ K ≤ V := by
        have : ((2 ^ K : ℕ) : ℝ) ≤ (⌊V⌋₊ : ℝ) := by exact_mod_cast h5
        push_cast at this
        exact this.trans (Nat.floor_le (by linarith))
      exact Real.rpow_le_rpow (by positivity) h6 (by norm_num)
    have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
    calc max C₀ 0 * ∑ k ∈ Finset.range (K + 1), ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)
        ≤ max C₀ 0 * (4 * ((2 : ℝ) ^ K) ^ (1 / 2 : ℝ)) := by gcongr
      _ ≤ max C₀ 0 * (4 * V ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by ring
  -- summability of the frequency norms
  have hS' : ∀ σ : ℝ, 1 < σ → Summable fun r : ι' => ((q r : ℕ) : ℝ) ^ (-σ) := fun σ hσ =>
    (summable_freq n hn0 hn h𝔪 hσ).subtype _
  -- constants
  set c0 : ℝ := ‖((2 * Real.pi) ^ 3 : ℂ)⁻¹‖ with hc0
  set CΛ' := max CΛ 0
  set CH' := max CH 0
  set CD' := max CD 0
  obtain ⟨C, hCsum⟩ := sum_bound q hq1 hS' exc Fs (4 * max C₀ 0) hFin hFc
    (c0 * KI * (BZ * CΛ' * CH' * BL)) (c0 * KII * (BZ * CΛ' * CH') * (CD' + 4 * (CD' + BL)))
    (c0 * KIII * (BZ * CΛ' * CH' * BL))
  refine ⟨C, max 1 ((2 * U1) ^ (100 / 9 : ℝ)), fun Z hZ => ?_⟩
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZ0 : 0 < Z := by linarith
  have hU1 : 1 ≤ U1 := le_max_right _ _
  have hV1 : 2 * U1 ≤ Z ^ (9 / 100 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hZ)
      (show (0 : ℝ) ≤ 9 / 100 by norm_num)
    rwa [← Real.rpow_mul (by positivity), show (100 / 9 : ℝ) * (9 / 100) = 1 by norm_num,
      Real.rpow_one] at h
  have hc0n : 0 ≤ c0 := norm_nonneg _
  have hCΛ' : 0 ≤ CΛ' := le_max_right _ _
  have hCH' : 0 ≤ CH' := le_max_right _ _
  have hCD' : 0 ≤ CD' := le_max_right _ _
  -- the row integrals as triple integrals
  set J : ι' → ℂ := fun r =>
    χ.rowIntegral g W₁ M r.1 (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z with hJ
  have hJeq : ∀ r : ι', J r = ((2 * Real.pi) ^ 3 : ℂ)⁻¹ *
      I3 (Phi (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh (q r)
        (Gf (zetaSF 𝔪) (Λf r.1) (twistedL ι χ (freqElt g r.1)) (Hf r.1))) 4 4 2 := fun r =>
    rowIntegral_eq χ g W₁ M r.1 Z _ (hrow r).2
  have hqpow : ∀ r : ι', ∀ x y : ℝ, ((q r : ℕ) : ℝ) ^ x * ((q r : ℕ) : ℝ) ^ y =
      ((q r : ℕ) : ℝ) ^ (x + y) := fun r x y =>
    rpow_mul_rpow (by have := hq1 r; positivity) x y
  -- (8.15) for every row
  have hI : ∀ r : ι', ‖J r‖ ≤ c0 * KI * (BZ * CΛ' * CH' * BL) * Z ^ e1 *
      ((q r : ℕ) : ℝ) ^ (51 / 500 : ℝ) := by
    intro r
    rw [hJeq, (row_move hwt (hrow r).1 (hq1 r) hZ1).1, norm_mul]
    have hb := hKI _ _ _ _ _ _ _ _ (hrow r).1 (q r) (hq1 r) Z hZ1
    calc c0 * ‖I3 _ s1 (3 / 1000) (2 / 5)‖ ≤ c0 * (KI * Z ^ (s1 - 642601 / 1000000) *
          ((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) * (BZ * (CΛ' * ((q r : ℕ) : ℝ) ^ (1 / 2 + κ)) *
            (CH' * ((q r : ℕ) : ℝ) ^ κ) * BL)) := by gcongr
      _ = c0 * KI * (BZ * CΛ' * CH' * BL) * Z ^ e1 * (((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
            ((q r : ℕ) : ℝ) ^ (1 / 2 + κ) * ((q r : ℕ) : ℝ) ^ κ) := by unfold e1; ring
      _ = _ := by
        have ex : (-(2 / 5 : ℝ)) + (1 / 2 + κ) + κ = 51 / 500 := by rw [hκ]; norm_num
        simp only [hqpow]; rw [ex]
  -- (8.20) for every row
  have hIII : ∀ r : ι', ‖J r‖ ≤ c0 * KIII * (BZ * CΛ' * CH' * BL) * Z ^ e3 *
      ((q r : ℕ) : ℝ) ^ (-R0 + 251 / 500) := by
    intro r
    rw [hJeq, (row_move hwt (hrow r).1 (hq1 r) hZ1).2, norm_mul]
    have hb := hKIII _ _ _ _ _ _ _ _ (hrow r).1 (q r) (hq1 r) Z hZ1
    calc c0 * ‖I3 _ 4 4 R0‖ ≤ c0 * (KIII * Z ^ (3849 / 1000 + R0 / 10) *
          ((q r : ℕ) : ℝ) ^ (-R0) * (BZ * (CΛ' * ((q r : ℕ) : ℝ) ^ (1 / 2 + κ)) *
            (CH' * ((q r : ℕ) : ℝ) ^ κ) * BL)) := by gcongr
      _ = c0 * KIII * (BZ * CΛ' * CH' * BL) * Z ^ e3 * (((q r : ℕ) : ℝ) ^ (-R0) *
            ((q r : ℕ) : ℝ) ^ (1 / 2 + κ) * ((q r : ℕ) : ℝ) ^ κ) := by unfold e3; ring
      _ = _ := by
        have ex : -R0 + (1 / 2 + κ) + κ = -R0 + 251 / 500 := by rw [hκ]; ring
        simp only [hqpow]; rw [ex]
  -- (8.17)–(8.19) for the good rows of the intermediate range
  have hII : ∀ r : ι', Z ^ (9 / 100 : ℝ) < ((q r : ℕ) : ℝ) → ¬ exc r →
      ‖J r‖ ≤ c0 * KII * (BZ * CΛ' * CH') * (CD' + 4 * (CD' + BL)) *
        (Z ^ e2 * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ) +
          Z ^ e1 * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ)) := by
    intro r hr hne
    obtain ⟨hU1q, hU2q⟩ := hpow r
    set k := Nat.log 2 (q r)
    set U : ℝ := (2 : ℝ) ^ k with hUdef
    have hqr : 2 * U1 ≤ (q r : ℝ) := hV1.trans hr.le
    have hUE : r.1 ∉ E U := fun h => hne ⟨hqr, h⟩
    have hU1' : U1 ≤ U := by linarith
    have hU0 : U₀ ≤ U := (le_max_left _ _).trans hU1'
    have hUpos : 0 < U := by positivity
    have hU1'' : 1 ≤ U := hU1.trans hU1'
    obtain ⟨D, hDd, hDL, hDb⟩ := hDk U hU0 r.1 r.2 hU1q hU2q hUE
    have hT : 0 < U ^ ρ := Real.rpow_pos_of_pos hUpos _
    have hb := hKII _ _ _ _ _ _ _ _ (hrow r).1 (q r) (hq1 r) D (U ^ ρ) (3 * U ^ ρ)
      (CD' * U ^ κ) hT.le (by linarith) (by positivity) hDd hDL
      (fun ξ h1 h2 => (hDb ξ h1 (by linarith)).trans (by gcongr; exact le_max_left _ _)) Z hZ1
    rw [hJeq, (row_move hwt (hrow r).1 (hq1 r) hZ1).1, norm_mul]
    have hQ : 1 ≤ ((q r : ℕ) : ℝ) := by exact_mod_cast hq1 r
    have hQ0 : 0 < ((q r : ℕ) : ℝ) := by linarith
    -- `U^κ ≤ q^κ`
    have hUk : U ^ κ ≤ ((q r : ℕ) : ℝ) ^ κ := Real.rpow_le_rpow hUpos.le hU1q (by norm_num)
    -- `(1 + U^ρ)^{-(N-2)} ≤ 4 q^{-2}`
    have hτ : (1 + U ^ ρ) ^ (-(N - 2)) ≤ 4 * ((q r : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
      have e1' : (1 + U ^ ρ) ^ (-(N - 2)) ≤ (U ^ ρ) ^ (-(N - 2)) :=
        Real.rpow_le_rpow_of_nonpos hT (by linarith) (by linarith)
      have e2' : (U ^ ρ) ^ (-(N - 2)) = U ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_mul hUpos.le]
        congr 1
        rw [hNdef]; field_simp; ring
      have e3' : U ^ (-(2 : ℝ)) ≤ (((q r : ℕ) : ℝ) / 2) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have e4' : (((q r : ℕ) : ℝ) / 2) ^ (-(2 : ℝ)) = 4 * ((q r : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.div_rpow hQ0.le (by norm_num)]
        rw [show (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 by
          rw [Real.rpow_neg (by norm_num)]; norm_num]
        ring
      linarith
    have hqk : 0 ≤ ((q r : ℕ) : ℝ) ^ κ := by positivity
    have hq2 : 0 ≤ ((q r : ℕ) : ℝ) ^ (-(2 : ℝ)) := by positivity
    have hP0 : 0 ≤ c0 * KII * ((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
        (BZ * (CΛ' * ((q r : ℕ) : ℝ) ^ (1 / 2 + κ)) * (CH' * ((q r : ℕ) : ℝ) ^ κ)) := by
      positivity
    have hZe2 : 0 ≤ Z ^ (998 / 1000 - 642601 / 1000000 : ℝ) := by positivity
    have hZe1 : 0 ≤ Z ^ (s1 - 642601 / 1000000) := by positivity
    calc c0 * ‖I3 _ s1 (3 / 1000) (2 / 5)‖
        ≤ c0 * (KII * ((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
          (BZ * (CΛ' * ((q r : ℕ) : ℝ) ^ (1 / 2 + κ)) * (CH' * ((q r : ℕ) : ℝ) ^ κ)) *
          (Z ^ (998 / 1000 - 642601 / 1000000 : ℝ) * (CD' * U ^ κ) +
            Z ^ (s1 - 642601 / 1000000) * (1 + U ^ ρ) ^ (-(N - 2)) * (CD' * U ^ κ + BL))) := by
          gcongr
      _ = c0 * KII * ((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
          (BZ * (CΛ' * ((q r : ℕ) : ℝ) ^ (1 / 2 + κ)) * (CH' * ((q r : ℕ) : ℝ) ^ κ)) *
          (Z ^ (998 / 1000 - 642601 / 1000000 : ℝ) * (CD' * U ^ κ) +
            Z ^ (s1 - 642601 / 1000000) * (1 + U ^ ρ) ^ (-(N - 2)) * (CD' * U ^ κ + BL)) := by
          ring
      _ ≤ c0 * KII * ((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
          (BZ * (CΛ' * ((q r : ℕ) : ℝ) ^ (1 / 2 + κ)) * (CH' * ((q r : ℕ) : ℝ) ^ κ)) *
          (Z ^ (998 / 1000 - 642601 / 1000000 : ℝ) * (CD' * ((q r : ℕ) : ℝ) ^ κ) +
            Z ^ (s1 - 642601 / 1000000) * (4 * ((q r : ℕ) : ℝ) ^ (-(2 : ℝ))) *
              (CD' * ((q r : ℕ) : ℝ) ^ κ + BL * ((q r : ℕ) : ℝ) ^ κ)) := by
          have hk1 : BL ≤ BL * ((q r : ℕ) : ℝ) ^ κ := by
            have : 1 ≤ ((q r : ℕ) : ℝ) ^ κ := Real.one_le_rpow hQ (by norm_num)
            nlinarith
          gcongr
      _ = c0 * KII * (BZ * CΛ' * CH') * (Z ^ e2 * (CD' * (((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
            ((q r : ℕ) : ℝ) ^ (1 / 2 + κ) * ((q r : ℕ) : ℝ) ^ κ * ((q r : ℕ) : ℝ) ^ κ)) +
          Z ^ e1 * (4 * (CD' + BL)) * (((q r : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) *
            ((q r : ℕ) : ℝ) ^ (1 / 2 + κ) * ((q r : ℕ) : ℝ) ^ κ * ((q r : ℕ) : ℝ) ^ κ *
            ((q r : ℕ) : ℝ) ^ (-(2 : ℝ)))) := by unfold e1 e2; ring
      _ = c0 * KII * (BZ * CΛ' * CH') * (Z ^ e2 * (CD' * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ)) +
          Z ^ e1 * (4 * (CD' + BL)) * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ)) := by
          have ex1 : (-(2 / 5 : ℝ)) + (1 / 2 + κ) + κ + κ = 103 / 1000 := by rw [hκ]; norm_num
          have ex2 : (103 / 1000 : ℝ) + (-(2 : ℝ)) = -(1897 / 1000) := by norm_num
          simp only [hqpow]
          rw [ex1, ex2]
      _ ≤ _ := by
          have hb1 : 0 ≤ c0 * KII * (BZ * CΛ' * CH') := by positivity
          have hz1 : 0 ≤ Z ^ e2 * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ) := by
            unfold e2; positivity
          have hz2 : 0 ≤ Z ^ e1 * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ) := by
            unfold e1; positivity
          have : Z ^ e2 * (CD' * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ)) +
              Z ^ e1 * (4 * (CD' + BL)) * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ) ≤
              (CD' + 4 * (CD' + BL)) * (Z ^ e2 * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ) +
                Z ^ e1 * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ)) := by
            set a' := Z ^ e2 * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ)
            set b' := Z ^ e1 * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ)
            have h4 : 0 ≤ 4 * (CD' + BL) * a' + CD' * b' := by positivity
            calc Z ^ e2 * (CD' * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ)) +
                Z ^ e1 * (4 * (CD' + BL)) * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ)
                = CD' * a' + 4 * (CD' + BL) * b' := by simp only [a', b']; ring
              _ ≤ CD' * a' + 4 * (CD' + BL) * b' + (4 * (CD' + BL) * a' + CD' * b') :=
                le_add_of_nonneg_right h4
              _ = _ := by ring
          calc c0 * KII * (BZ * CΛ' * CH') * (Z ^ e2 * (CD' * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ)) +
                Z ^ e1 * (4 * (CD' + BL)) * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ))
              ≤ c0 * KII * (BZ * CΛ' * CH') * ((CD' + 4 * (CD' + BL)) *
                (Z ^ e2 * ((q r : ℕ) : ℝ) ^ (103 / 1000 : ℝ) +
                  Z ^ e1 * ((q r : ℕ) : ℝ) ^ (-(1897 / 1000) : ℝ))) :=
                mul_le_mul_of_nonneg_left this hb1
            _ = _ := by ring
  have := hCsum Z hZ1 J hI hIII hII
  simpa [etarget, J] using this

end L2C

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots

end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖∑' r : {r : FreqClass 𝔪 // r ≠ principalFreq 𝔪},
                χ.rowIntegral g W₁ M r.1 (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2500) :=
  L2C.chk_exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le_of_cuts n hn0 hn F ι
    (exists_cutoff_exists_freqSeries_mul_twistedL_eq n hn0 hn F ι)
    (exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le n hn0 hn F ι)
    (exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one n hn0 hn F ι)
end
