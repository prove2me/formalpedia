-- Prove2me | Definitions.Def_RPLib_S3_HypParF
-- name    : RPLib_S3_HypParF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:24:59.189265+00:00
-- url     : https://prove2.me/theorems/a2552088-148c-45c1-b93f-d61c96e00752
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part F: the parabolic top-edge sums
-- statement:
--   For $g = \begin{pmatrix} s & b \\ 0 & s \end{pmatrix}$, the weighted top-edge integrals summed over $b$ converge, as the height tends to infinity, to an explicit constant: the sum is an offset Riemann sum of a bounded rational function, evaluated by a partial-fraction recursion.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_HypParEB

/-!
# S3-HypParTerms, part F (O7): the `c = 0` parabolic top-edge sums

For `g = ut s b s` (`s ≠ 0`, `b ∈ ℤ`), `topI g m Y = -(1/m) Y⁻¹ Hp (2s) m (b/Y)` with
`Hp β m v = ((v - β i)^m v)⁻¹`. The weights are even in `b` and `M`-periodic on `b ≠ 0`, so the sum
pairs into `Fp = Hp(v) + Hp(-v)` (bounded, `O(1/(1+v²))`) and splits into residue classes mod `M`;
each class is an offset Riemann sum (`tendsto_riemann`, dominated convergence on a step function).
`∫ Fp` is computed by the partial-fraction recursion `Fp_succ` and `HypEA`.
Main result: `tendsto_par`.
-/

open Complex MeasureTheory Set Filter
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-! ### Part 1: Riemann sums with an offset -/

/-- The sample point `ε (⌈v/ε⌉ - 1 + θ)`. -/
def samp (θ ε v : ℝ) : ℝ := ε * (((⌈v / ε⌉ : ℤ) : ℝ) - 1 + θ)

lemma samp_close {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 < ε) (v : ℝ) :
    |samp θ ε v - v| ≤ ε := by
  have hv : v = ε * (v / ε) := by rw [mul_div_assoc', eq_div_iff hε.ne', mul_comm]
  have h1 : v / ε ≤ ((⌈v / ε⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h2 : ((⌈v / ε⌉ : ℤ) : ℝ) < v / ε + 1 := Int.ceil_lt_add_one _
  unfold samp
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hε.le, mul_nonneg hε.le hθ0]
  · nlinarith [mul_lt_mul_of_pos_left h2 hε, mul_le_mul_of_nonneg_left hθ1 hε.le]

lemma one_add_sq_le {v w : ℝ} (h : |w - v| ≤ 1) : 1 + v ^ 2 ≤ 3 * (1 + w ^ 2) := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  nlinarith [sq_nonneg (v - 2 * w), mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ w - v + 1)]

/-- Offset Riemann sums of a bounded-by-`C/(1+v²)` function converge to its integral. -/
theorem tendsto_riemann {F : ℝ → ℂ} (hFm : Measurable F)
    (hFc : ∀ v : ℝ, v ≠ 0 → ContinuousAt F v) {C : ℝ}
    (hFb : ∀ v : ℝ, ‖F v‖ ≤ C * (1 + v ^ 2)⁻¹) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Tendsto (fun ε : ℝ => ∑' j : ℤ, (ε : ℂ) * F (ε * (j + θ))) (𝓝[>] 0) (𝓝 (∫ v, F v)) := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg (F 0)).trans (hFb 0)
    norm_num at this
    exact this
  have hmeas : ∀ ε : ℝ, Measurable (fun v : ℝ => F (samp θ ε v)) := fun ε => by
    have hc : Measurable (fun v : ℝ => (((⌈v / ε⌉ : ℤ) : ℝ))) :=
      (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (Int.measurable_ceil.comp (measurable_id.div_const ε))
    exact hFm.comp (measurable_const.mul ((hc.sub_const 1).add_const θ))
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ v : ℝ,
      ‖F (samp θ ε v)‖ ≤ 3 * C * (1 + v ^ 2)⁻¹ := by
    intro ε hε hε1 v
    have h1 := one_add_sq_le ((samp_close hθ0 hθ1 hε v).trans hε1)
    have hp : 0 < 1 + v ^ 2 := by positivity
    have hq : 0 < 1 + (samp θ ε v) ^ 2 := by positivity
    have h2 : (1 + (samp θ ε v) ^ 2)⁻¹ ≤ 3 * (1 + v ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp, inv_mul_le_iff₀ hq]
      linarith
    calc ‖F (samp θ ε v)‖ ≤ C * (1 + (samp θ ε v) ^ 2)⁻¹ := hFb _
      _ ≤ C * (3 * (1 + v ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 hC
      _ = 3 * C * (1 + v ^ 2)⁻¹ := by ring
  have hsum : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      HasSum (fun j : ℤ => (ε : ℂ) * F (ε * (j + θ))) (∫ v, F (samp θ ε v)) := by
    intro ε hε hε1
    have hint : Integrable (fun v : ℝ => F (samp θ ε v)) :=
      Integrable.mono' (integrable_inv_one_add_sq.const_mul (3 * C)) (hmeas ε).aestronglyMeasurable
        (Eventually.of_forall (hbound ε hε hε1))
    have hGi : Integrable (fun t : ℝ => F (samp θ ε (ε * t))) := hint.comp_mul_left' hε.ne'
    have hGv : ∀ t : ℝ, F (samp θ ε (ε * t)) = F (ε * (((⌈t⌉ : ℤ) : ℝ) - 1 + θ)) := by
      intro t; unfold samp; rw [mul_div_cancel_left₀ t hε.ne']
    have hint_eq : ∫ t, F (samp θ ε (ε * t)) = ((ε⁻¹ : ℝ) : ℂ) * ∫ v, F (samp θ ε v) := by
      calc ∫ t, F (samp θ ε (ε * t)) = |ε⁻¹| • ∫ v, F (samp θ ε v) :=
            Measure.integral_comp_mul_left (fun v => F (samp θ ε v)) ε
        _ = _ := by rw [abs_of_pos (inv_pos.2 hε), Complex.real_smul]
    have h1 := hGi.hasSum_intervalIntegral 0
    have hpiece : ∀ j : ℤ, ∫ x in (0 : ℝ) + j..(0 : ℝ) + j + 1, F (samp θ ε (ε * x)) =
        F (ε * (j + θ)) := by
      intro j
      have hle : (0 : ℝ) + j ≤ 0 + j + 1 := by linarith
      rw [intervalIntegral.integral_congr_ae (g := fun _ => F (ε * (j + θ))) ?_]
      · simp
      · refine Eventually.of_forall (fun x hx => ?_)
        rw [uIoc_of_le hle] at hx
        rw [hGv]
        have hc : ⌈x⌉ = j + 1 := by
          rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith [hx.1, hx.2]
        rw [hc]
        congr 1
        push_cast
        ring
    have h2 : HasSum (fun j : ℤ => F (ε * (j + θ))) (((ε⁻¹ : ℝ) : ℂ) * ∫ v, F (samp θ ε v)) := by
      rw [← hint_eq]
      have hfe : (fun j : ℤ => F (ε * (j + θ))) =
          fun j : ℤ => ∫ x in (0 : ℝ) + j..(0 : ℝ) + j + 1, F (samp θ ε (ε * x)) :=
        funext fun j => (hpiece j).symm
      rw [hfe]
      exact h1
    have h3 := h2.mul_left (ε : ℂ)
    have e : (ε : ℂ) * (((ε⁻¹ : ℝ) : ℂ) * ∫ v, F (samp θ ε v)) = ∫ v, F (samp θ ε v) := by
      rw [← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hε.ne', ofReal_one, one_mul]
    rw [e] at h3
    exact h3
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 := nhdsWithin_le_nhds (Iic_mem_nhds zero_lt_one)
  have hev := hev1.and hev2
  have hsamp : ∀ v : ℝ, Tendsto (fun ε => samp θ ε v) (𝓝[>] 0) (𝓝 v) := by
    intro v
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _)
      (hev1.mono fun ε hε => ?_) (tendsto_id.mono_left nhdsWithin_le_nhds)
    rw [Real.norm_eq_abs]
    exact samp_close hθ0 hθ1 hε v
  have hlim : Tendsto (fun ε => ∫ v, F (samp θ ε v)) (𝓝[>] 0) (𝓝 (∫ v, F v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => 3 * C * (1 + v ^ 2)⁻¹)
      (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable)
      (hev.mono fun ε hε => Eventually.of_forall (hbound ε hε.1 hε.2))
      (integrable_inv_one_add_sq.const_mul _) ?_
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with v hv
    exact (hFc v hv).tendsto.comp (hsamp v)
  refine hlim.congr' ?_
  filter_upwards [hev] with ε hε
  exact (hsum ε hε.1 hε.2).tsum_eq.symm

/-! ### Part 2: the parabolic integrand -/

/-- `Hp β m v = ((v - β i)^m v)⁻¹`. -/
def Hp (β : ℝ) (m : ℕ) (v : ℝ) : ℂ := ((HypEA.u β v) ^ m * HypEA.u 0 v)⁻¹

/-- The even part `Hp(v) + Hp(-v)`. -/
def Fp (β : ℝ) (m : ℕ) (v : ℝ) : ℂ := Hp β m v + Hp β m (-v)

/-- The partial-fraction correction `u(v)^{-j} + u(-v)^{-j}`. -/
def Pp (β : ℝ) (j : ℕ) (v : ℝ) : ℂ := ((HypEA.u β v) ^ j)⁻¹ + ((HypEA.u β (-v)) ^ j)⁻¹

/-- `cP β = u_β - u_0 = -β i`. -/
def cP (β : ℝ) : ℂ := -((β : ℂ) * I)

lemma cP_ne_zero {β : ℝ} (hβ : β ≠ 0) : cP β ≠ 0 :=
  neg_ne_zero.2 (mul_ne_zero (ofReal_ne_zero.2 hβ) I_ne_zero)

lemma u_zero_eq (v : ℝ) : HypEA.u 0 v = v := by simp [HypEA.u]

lemma u_neg_eq (β v : ℝ) : HypEA.u β (-v) = -HypEA.u (-β) v := by
  unfold HypEA.u; push_cast; ring

lemma Hp_zero (β : ℝ) (m : ℕ) : Hp β m 0 = 0 := by simp [Hp, u_zero_eq]

lemma Fp_at_zero (β : ℝ) (m : ℕ) : Fp β m 0 = 0 := by simp [Fp, Hp_zero]

lemma Fp_zero' (β v : ℝ) : Fp β 0 v = 0 := by
  simp [Fp, Hp, u_zero_eq, inv_neg]

lemma Hp_succ {β : ℝ} (hβ : β ≠ 0) {w : ℝ} (hw : w ≠ 0) (m : ℕ) :
    Hp β (m + 1) w = (cP β)⁻¹ * (Hp β m w - ((HypEA.u β w) ^ (m + 1))⁻¹) := by
  have hA := HypEA.u_ne_zero hβ w
  have hB : HypEA.u 0 w ≠ 0 := by rw [u_zero_eq]; exact_mod_cast hw
  have hc : cP β = HypEA.u β w - HypEA.u 0 w := by unfold cP HypEA.u; push_cast; ring
  have hd : HypEA.u β w - HypEA.u 0 w ≠ 0 := by rw [← hc]; exact cP_ne_zero hβ
  unfold Hp
  rw [hc]
  field_simp
  ring

lemma Fp_succ {β : ℝ} (hβ : β ≠ 0) {v : ℝ} (hv : v ≠ 0) (m : ℕ) :
    Fp β (m + 1) v = (cP β)⁻¹ * (Fp β m v - Pp β (m + 1) v) := by
  unfold Fp Pp
  rw [Hp_succ hβ hv m, Hp_succ hβ (neg_ne_zero.2 hv) m]
  ring

lemma Pp_one (β v : ℝ) : Pp β 1 v = (HypEA.u β v)⁻¹ - (HypEA.u (-β) v)⁻¹ := by
  unfold Pp; rw [pow_one, pow_one, u_neg_eq, inv_neg, sub_eq_add_neg]

/-! Bounds (copied from the proofs in `HypPar_EA`). -/

lemma norm_inv_pow_le' {A : ℝ} (hA : A ≠ 0) (i : ℕ) (s : ℝ) :
    ‖((HypEA.u A s) ^ (i + 2))⁻¹‖ ≤ ((|A| ^ i)⁻¹ * (min 1 (A ^ 2))⁻¹) * (1 + s ^ 2)⁻¹ := by
  have hAi : 0 < |A| ^ i := pow_pos (abs_pos.2 hA) i
  have h1 : |A| ^ i ≤ ‖HypEA.u A s‖ ^ i :=
    pow_le_pow_left₀ (abs_nonneg A) (HypEA.abs_le_norm_u A s) i
  rw [norm_inv, norm_pow, pow_add, HypEA.sq_norm_u, mul_inv]
  have h2 := HypEA.inv_sq_le hA s
  have h3 : (‖HypEA.u A s‖ ^ i)⁻¹ ≤ (|A| ^ i)⁻¹ := inv_anti₀ hAi h1
  have hm : 0 < min 1 (A ^ 2) := lt_min one_pos (by positivity)
  calc (‖HypEA.u A s‖ ^ i)⁻¹ * (s ^ 2 + A ^ 2)⁻¹
      ≤ (|A| ^ i)⁻¹ * ((min 1 (A ^ 2))⁻¹ * (1 + s ^ 2)⁻¹) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = _ := by ring

lemma norm_inv_sub_inv_le' {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    ‖(HypEA.u A s)⁻¹ - (HypEA.u B s)⁻¹‖ ≤
      (|A - B| * ((min 1 (A ^ 2))⁻¹ + (min 1 (B ^ 2))⁻¹)) * (1 + s ^ 2)⁻¹ := by
  rw [HypEA.inv_sub_inv_u hA hB]
  simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 := HypEA.norm_inv_u_sq_le hA s
  have h2 := HypEA.norm_inv_u_sq_le hB s
  have h3 := two_mul_le_add_sq ‖(HypEA.u A s)⁻¹‖ ‖(HypEA.u B s)⁻¹‖
  have h4 : 0 ≤ ‖(HypEA.u A s)⁻¹‖ * ‖(HypEA.u B s)⁻¹‖ := by positivity
  have h6 : ‖(HypEA.u A s)⁻¹‖ * ‖(HypEA.u B s)⁻¹‖ ≤
      ((min 1 (A ^ 2))⁻¹ + (min 1 (B ^ 2))⁻¹) * (1 + s ^ 2)⁻¹ := by
    nlinarith [sq_nonneg ‖(HypEA.u A s)⁻¹‖, sq_nonneg ‖(HypEA.u B s)⁻¹‖]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h6 (abs_nonneg _)

lemma norm_Pp_le {β : ℝ} (hβ : β ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, ‖Pp β j v‖ ≤ K * (1 + v ^ 2)⁻¹ := by
  rcases Nat.lt_or_ge j 2 with h | h
  · obtain rfl : j = 1 := by omega
    refine ⟨|β - -β| * ((min 1 (β ^ 2))⁻¹ + (min 1 ((-β) ^ 2))⁻¹), by positivity, fun v => ?_⟩
    rw [Pp_one]
    exact norm_inv_sub_inv_le' hβ (neg_ne_zero.2 hβ) v
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h
    refine ⟨2 * ((|β| ^ i)⁻¹ * (min 1 (β ^ 2))⁻¹), by positivity, fun v => ?_⟩
    have h1 := norm_inv_pow_le' hβ i v
    have h2 := norm_inv_pow_le' hβ i (-v)
    rw [neg_sq] at h2
    unfold Pp
    calc _ ≤ ‖((HypEA.u β v) ^ (i + 2))⁻¹‖ + ‖((HypEA.u β (-v)) ^ (i + 2))⁻¹‖ := norm_add_le _ _
      _ ≤ _ := by linarith

lemma norm_Fp_le {β : ℝ} (hβ : β ≠ 0) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, ‖Fp β m v‖ ≤ K * (1 + v ^ 2)⁻¹ := by
  induction m with
  | zero => exact ⟨0, le_rfl, fun v => by rw [Fp_zero']; simp⟩
  | succ m ih =>
    obtain ⟨K, hK, hb⟩ := ih
    obtain ⟨K', hK', hb'⟩ := norm_Pp_le hβ (j := m + 1) (by omega)
    refine ⟨‖(cP β)⁻¹‖ * (K + K'), by positivity, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · rw [Fp_at_zero, norm_zero]; positivity
    · rw [Fp_succ hβ hv]
      calc ‖(cP β)⁻¹ * (Fp β m v - Pp β (m + 1) v)‖
          ≤ ‖(cP β)⁻¹‖ * (‖Fp β m v‖ + ‖Pp β (m + 1) v‖) := by
            rw [norm_mul]; gcongr; exact norm_sub_le _ _
        _ ≤ ‖(cP β)⁻¹‖ * (K * (1 + v ^ 2)⁻¹ + K' * (1 + v ^ 2)⁻¹) := by
            gcongr
            · exact hb v
            · exact hb' v
        _ = ‖(cP β)⁻¹‖ * (K + K') * (1 + v ^ 2)⁻¹ := by ring

lemma measurable_Hp (β : ℝ) (m : ℕ) : Measurable (Hp β m) := by
  unfold Hp
  exact (((HypEA.continuous_u β).pow m).mul (HypEA.continuous_u 0)).measurable.inv

lemma measurable_Fp (β : ℝ) (m : ℕ) : Measurable (Fp β m) := by
  unfold Fp
  exact (measurable_Hp β m).add ((measurable_Hp β m).comp measurable_neg)

lemma measurable_Pp (β : ℝ) (j : ℕ) : Measurable (Pp β j) := by
  unfold Pp
  have h : Measurable (fun v : ℝ => ((HypEA.u β v) ^ j)⁻¹) :=
    ((HypEA.continuous_u β).pow j).measurable.inv
  exact h.add (h.comp measurable_neg)

lemma continuousAt_Fp {β : ℝ} (hβ : β ≠ 0) (m : ℕ) {v : ℝ} (hv : v ≠ 0) :
    ContinuousAt (Fp β m) v := by
  have hH : ∀ w : ℝ, w ≠ 0 → ContinuousAt (Hp β m) w := fun w hw => by
    have hB : HypEA.u 0 w ≠ 0 := by rw [u_zero_eq]; exact_mod_cast hw
    unfold Hp
    exact ((((HypEA.continuous_u β).pow m).mul (HypEA.continuous_u 0)).continuousAt).inv₀
      (mul_ne_zero (pow_ne_zero _ (HypEA.u_ne_zero hβ w)) hB)
  unfold Fp
  exact (hH v hv).add ((hH (-v) (neg_ne_zero.2 hv)).comp continuous_neg.continuousAt)

lemma integrable_of_bound {f : ℝ → ℂ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ v, ‖f v‖ ≤ K * (1 + v ^ 2)⁻¹) : Integrable f :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hf.aestronglyMeasurable
    (Eventually.of_forall hb)

lemma integral_Pp_one {β : ℝ} (hβ : β ≠ 0) :
    ∫ v, Pp β 1 v = ((π * (Real.sign β - Real.sign (-β)) : ℝ) : ℂ) * I := by
  rw [show Pp β 1 = fun v => (HypEA.u β v)⁻¹ - (HypEA.u (-β) v)⁻¹ from funext (Pp_one β)]
  exact HypEA.integral_inv_sub_inv hβ (neg_ne_zero.2 hβ)

lemma integral_Pp {β : ℝ} (hβ : β ≠ 0) {j : ℕ} (hj : 2 ≤ j) : ∫ v, Pp β j v = 0 := by
  have hn := integral_neg_eq_self (fun v : ℝ => ((HypEA.u β v) ^ j)⁻¹) volume
  unfold Pp
  rw [integral_add (HypEA.integrable_inv_pow hβ hj) (HypEA.integrable_inv_pow hβ hj).comp_neg, hn,
    HypEA.integral_inv_pow hβ hj, add_zero]

/-- `∫ Fp β (m+1) = -(cP β)^{-(m+1)} π (sign β - sign(-β)) i`. -/
lemma integral_Fp {β : ℝ} (hβ : β ≠ 0) (m : ℕ) :
    ∫ v, Fp β (m + 1) v =
      -((cP β) ^ (m + 1))⁻¹ * (((π * (Real.sign β - Real.sign (-β)) : ℝ) : ℂ) * I) := by
  induction m with
  | zero =>
    have hae : Fp β (0 + 1) =ᵐ[volume] fun v => -(cP β)⁻¹ * Pp β (0 + 1) v := by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with v hv
      rw [Fp_succ hβ hv 0, Fp_zero']
      ring
    rw [integral_congr_ae hae, integral_const_mul, zero_add, integral_Pp_one hβ, pow_one]
  | succ m ih =>
    obtain ⟨K, -, hK⟩ := norm_Fp_le hβ (m + 1)
    obtain ⟨K', -, hK'⟩ := norm_Pp_le hβ (j := m + 1 + 1) (by omega)
    have hae : Fp β (m + 1 + 1) =ᵐ[volume]
        fun v => (cP β)⁻¹ * (Fp β (m + 1) v - Pp β (m + 1 + 1) v) := by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with v hv
      exact Fp_succ hβ hv (m + 1)
    rw [integral_congr_ae hae, integral_const_mul,
      integral_sub (integrable_of_bound (measurable_Fp β _) hK)
        (integrable_of_bound (measurable_Pp β _) hK'),
      ih, integral_Pp hβ (by omega), sub_zero, pow_succ (cP β) (m + 1), mul_inv]
    ring

/-! ### Part 3: weights of the parabolic matrices `ut s b s` -/

variable {M : ℕ} [NeZero M]

lemma isRest_ut_par (s b : ℤ) : IsRest (ut s b s) ↔ b ≠ 0 := by
  simp only [IsRest, ut_10, ut_01, ut_00, ut_11, det_ut]
  have hns : ¬ ((s + s) ^ 2 < 4 * (s * s)) := by nlinarith
  constructor
  · intro h hb
    exact h (Or.inl (by simp [hb]))
  · intro hb h
    rcases h with h | h
    · exact hb (by simp_all)
    · exact hns h

lemma levelCount_ut_mod (δ' : ZMod M) (a d : ℤ) {b b' : ℤ} (h : (b : ZMod M) = (b' : ZMod M)) :
    S3.levelCount M δ' (ut a b d) = S3.levelCount M δ' (ut a b' d) := by
  have hm : (ut a b d).map (Int.castRingHom (ZMod M)) = (ut a b' d).map (Int.castRingHom (ZMod M)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ut, h]
  unfold S3.levelCount; rw [hm]

/-- `v ↦ (v₀, -v₁)`. -/
def flip1 (v : Fin 2 → ZMod M) : Fin 2 → ZMod M := ![v 0, -v 1]

lemma flip1_flip1 (v : Fin 2 → ZMod M) : flip1 (flip1 v) = v := by
  ext i; fin_cases i <;> simp [flip1]

lemma smul_flip1_eq_zero (d : ℕ) (v : Fin 2 → ZMod M) : d • flip1 v = 0 ↔ d • v = 0 := by
  simp [flip1, funext_iff, Fin.forall_fin_two]

lemma eig_ut_iff (δ' : ZMod M) (a b d : ℤ) (v : Fin 2 → ZMod M) :
    ((ut a b d).map (Int.castRingHom (ZMod M))).mulVec v = δ' • v ↔
      (a : ZMod M) * v 0 + (b : ZMod M) * v 1 = δ' * v 0 ∧ (d : ZMod M) * v 1 = δ' * v 1 := by
  simp [funext_iff, Fin.forall_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ut]

lemma levelCount_ut_neg (δ' : ZMod M) (s b : ℤ) :
    S3.levelCount M δ' (ut s (-b) s) = S3.levelCount M δ' (ut s b s) := by
  have key : ∀ c : ℤ, ∀ v : Fin 2 → ZMod M,
      ((∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0) ∧
        ((ut s c s).map (Int.castRingHom (ZMod M))).mulVec v = δ' • v) →
      ((∀ d ∈ Finset.range M, 0 < d → d • flip1 v ≠ 0) ∧
        ((ut s (-c) s).map (Int.castRingHom (ZMod M))).mulVec (flip1 v) = δ' • flip1 v) := by
    intro c v ⟨hx, he⟩
    refine ⟨fun d hd hd0 => by rw [Ne, smul_flip1_eq_zero]; exact hx d hd hd0, ?_⟩
    rw [eig_ut_iff] at he ⊢
    simp only [flip1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_neg]
    constructor
    · linear_combination he.1
    · linear_combination -he.2
  unfold S3.levelCount
  apply Finset.card_nbij' flip1 flip1
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    simpa using key (-b) v hv
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    exact key b v hv
  · intro v _; exact flip1_flip1 v
  · intro v _; exact flip1_flip1 v

lemma wt_ut_par_neg (n : ℤ) (δ' : ZMod M) (s b : ℤ) :
    wt M n δ' (ut s (-b) s) = wt M n δ' (ut s b s) := by
  have h : ((ut s (-b) s).det = n ∧ IsRest (ut s (-b) s)) ↔ ((ut s b s).det = n ∧ IsRest (ut s b s)) := by
    rw [det_ut, det_ut, isRest_ut_par, isRest_ut_par, neg_ne_zero]
  unfold wt
  rw [levelCount_ut_neg]
  by_cases hc : (ut s b s).det = n ∧ IsRest (ut s b s)
  · rw [if_pos hc, if_pos (h.2 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (h.1 h'))]

lemma wt_ut_par_mod (n : ℤ) (δ' : ZMod M) (s : ℤ) {b b' : ℤ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : (b : ZMod M) = (b' : ZMod M)) : wt M n δ' (ut s b s) = wt M n δ' (ut s b' s) := by
  have h' : ((ut s b s).det = n ∧ IsRest (ut s b s)) ↔ ((ut s b' s).det = n ∧ IsRest (ut s b' s)) := by
    rw [det_ut, det_ut, isRest_ut_par, isRest_ut_par]; simp [hb, hb']
  unfold wt
  rw [levelCount_ut_mod δ' s s h]
  by_cases hc : (ut s b' s).det = n ∧ IsRest (ut s b' s)
  · rw [if_pos hc, if_pos (h'.2 hc)]
  · rw [if_neg hc, if_neg (fun h'' => hc (h'.1 h''))]

lemma cast_rep (x : ZMod M) : (((x.val : ℤ) + M : ℤ) : ZMod M) = x := by
  push_cast; simp

/-! ### Part 4: the parabolic top edge and its sums -/

lemma u_scale (A : ℝ) {Y : ℝ} (hY : 0 < Y) (b : ℝ) :
    HypEA.u (A * Y) b = (Y : ℂ) * HypEA.u A (b / Y) := by
  have hYi : (Y : ℂ) * (Y : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (ofReal_ne_zero.2 hY.ne')
  unfold HypEA.u; push_cast
  linear_combination (-(b : ℂ)) * hYi

lemma scale_inv_aux (Y X Z : ℂ) (hY : Y ≠ 0) (m : ℕ) :
    Y ^ m * ((Y * X) ^ m * (Y * Z))⁻¹ = Y⁻¹ * (X ^ m * Z)⁻¹ := by
  rw [mul_pow, show Y ^ m * X ^ m * (Y * Z) = (Y ^ m * Y) * (X ^ m * Z) by ring,
    mul_inv (Y ^ m * Y) (X ^ m * Z), mul_inv (Y ^ m) Y, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero m hY), one_mul]

lemma topI_par (s b : ℤ) (m : ℕ) {Y : ℝ} (hY : 0 < Y) :
    topI (ut s b s) m Y = -(1 / (m : ℂ)) * ((Y : ℂ)⁻¹ * Hp (2 * s) m (b / Y)) := by
  have hY' : (Y : ℂ) ≠ 0 := ofReal_ne_zero.2 hY.ne'
  rw [topI_ut]
  have hc : ∀ x : ℝ, fR s s m Y (((s : ℝ) - s) * x + b) = fR s s m Y b := fun x => by
    rw [sub_self, zero_mul, zero_add]
  simp only [hc, intervalIntegral.integral_const]
  rw [show (1 / 2 : ℝ) - -(1 / 2) = 1 by norm_num, one_smul]
  unfold fR Hp
  have e1 : HypEA.u (((s : ℝ) + s) * Y) b = (Y : ℂ) * HypEA.u (2 * s) (b / Y) := by
    rw [show ((s : ℝ) + s) * Y = (2 * s) * Y by ring]; exact u_scale _ hY _
  have e2 : HypEA.u (((s : ℝ) - s) * Y) b = (Y : ℂ) * HypEA.u 0 (b / Y) := by
    rw [sub_self, zero_mul]; simpa using u_scale 0 hY (b : ℝ)
  rw [e1, e2, ← scale_inv_aux (Y : ℂ) _ _ hY' m]
  ring

lemma norm_Hp_le {β : ℝ} (m : ℕ) (v : ℝ) : ‖Hp β m v‖ ≤ (|v| ^ (m + 1))⁻¹ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [Hp_zero]
  · have hp : 0 < |v| := abs_pos.2 hv
    unfold Hp
    rw [norm_inv, norm_mul, norm_pow, u_zero_eq, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg v) (HypEA.abs_s_le_norm_u β v) m) hp.le)

lemma norm_Hp_int_le (β : ℝ) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ} (hY : 0 < Y) (b : ℤ) :
    ‖Hp β m (b / Y)‖ ≤ Y ^ (m + 1) * ((b : ℝ) ^ 2)⁻¹ := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [Hp_zero]
  · have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hb
    calc ‖Hp β m (b / Y)‖ ≤ (|(b : ℝ) / Y| ^ (m + 1))⁻¹ := norm_Hp_le m _
      _ = Y ^ (m + 1) * (|(b : ℝ)| ^ (m + 1))⁻¹ := by
        rw [abs_div, abs_of_pos hY, div_pow, inv_div, div_eq_mul_inv]
      _ ≤ Y ^ (m + 1) * ((b : ℝ) ^ 2)⁻¹ := by
        have h2 : (b : ℝ) ^ 2 ≤ |(b : ℝ)| ^ (m + 1) := by
          rw [← sq_abs]; exact pow_le_pow_right₀ hb1 (by omega)
        have hb2 : 0 < (b : ℝ) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hb2 h2) (by positivity)

lemma summable_int_inv_sq : Summable (fun b : ℤ => ((b : ℝ) ^ 2)⁻¹) := by
  have := (Real.summable_one_div_int_pow (p := 2)).mpr one_lt_two
  simpa [one_div] using this

lemma summable_Hp (β : ℝ) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun b : ℤ => Hp β m (b / Y)) :=
  Summable.of_norm_bounded (summable_int_inv_sq.mul_left (Y ^ (m + 1))) (norm_Hp_int_le β hm hY)

lemma summable_Hp_neg (β : ℝ) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun b : ℤ => Hp β m (-(b / Y))) := by
  have h := (Equiv.neg ℤ).summable_iff.mpr (summable_Hp β hm hY)
  convert h using 1
  funext b
  simp [neg_div]

lemma tsum_pair {w : ℤ → ℂ} (hw : ∀ b, w (-b) = w b) {H : ℝ → ℂ} {Y : ℝ}
    (hs : Summable (fun b : ℤ => w b * H (b / Y))) :
    ∑' b : ℤ, w b * H (b / Y) = (1 / 2) * ∑' b : ℤ, w b * (H (b / Y) + H (-(b / Y))) := by
  have hfun : (fun b : ℤ => w b * H (-(b / Y))) = (fun b : ℤ => w b * H (b / Y)) ∘ (Equiv.neg ℤ) := by
    funext b; simp [hw, neg_div]
  have hs' : Summable (fun b : ℤ => w b * H (-(b / Y))) := by
    rw [hfun]; exact (Equiv.neg ℤ).summable_iff.mpr hs
  have he : ∑' b : ℤ, w b * H (-(b / Y)) = ∑' b : ℤ, w b * H (b / Y) := by
    rw [hfun]; exact (Equiv.neg ℤ).tsum_eq (fun b : ℤ => w b * H (b / Y))
  simp_rw [mul_add]
  rw [hs.tsum_add hs', he]
  ring

lemma tsum_classes {c : ZMod M → ℂ} {G : ℤ → ℂ} (hG : Summable G) :
    ∑' b : ℤ, c (b : ZMod M) * G b = ∑ x : ZMod M, c x * ∑' j : ℤ, G ((x.val : ℤ) + M * j) := by
  have hpt : ∀ b : ℤ, c (b : ZMod M) * G b =
      ∑ x : ZMod M, ({b' : ℤ | (b' : ZMod M) = x}.indicator (fun b' => c x * G b') b) := by
    intro b
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hsum : ∀ x : ZMod M,
      Summable ({b' : ℤ | (b' : ZMod M) = x}.indicator (fun b' => c x * G b')) :=
    fun x => (hG.mul_left (c x)).indicator _
  rw [tsum_congr hpt, Summable.tsum_finsetSum (fun x _ => hsum x)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hinj : Function.Injective (fun j : ℤ => (x.val : ℤ) + M * j) := by
    intro j1 j2 h
    simp only at h
    exact mul_left_cancel₀ hM (by linarith)
  have hsupp : Function.support ({b' : ℤ | (b' : ZMod M) = x}.indicator (fun b' => c x * G b')) ⊆
      Set.range (fun j : ℤ => (x.val : ℤ) + M * j) := by
    intro b hb
    rw [Function.mem_support] at hb
    have hb' : (b : ZMod M) = x := by
      by_contra hne
      exact hb (by simp [Set.indicator_apply, hne])
    have h1 : (((x.val : ℕ) : ℤ) : ZMod M) = (b : ZMod M) := by rw [hb']; simp
    obtain ⟨k, hk⟩ := ((ZMod.intCast_eq_intCast_iff _ _ _).1 h1).dvd
    exact ⟨k, by show (x.val : ℤ) + M * k = b; linarith⟩
  refine (hinj.tsum_eq hsupp).symm.trans ?_
  rw [← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  have hj : ((x.val : ℤ) + M * j) ∈ {b' : ℤ | (b' : ZMod M) = x} := by
    show ((((x.val : ℤ) + M * j : ℤ)) : ZMod M) = x
    push_cast; simp
  exact Set.indicator_of_mem hj (fun b' => c x * G b')

lemma summable_wHp (n : ℤ) (δ' : ZMod M) (s : ℤ) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun b : ℤ => wt M n δ' (ut s b s) * Hp (2 * s) m (b / Y)) := by
  refine Summable.of_norm_bounded
    ((summable_Hp (2 * s) hm hY).norm.mul_left (Fintype.card (Fin 2 → ZMod M) : ℝ)) (fun b => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_wt_le n δ' _) (norm_nonneg _)

/-- Summability of the parabolic top-edge terms (for splitting the full sum). -/
lemma summable_par (n : ℤ) (δ' : ZMod M) (s : ℤ) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun b : ℤ => wt M n δ' (ut s b s) * topI (ut s b s) m Y) := by
  have h := (summable_wHp n δ' s hm hY).mul_left (-(1 / (m : ℂ)) * (Y : ℂ)⁻¹)
  refine h.congr (fun b => ?_)
  rw [topI_par s b m hY]
  ring

/-- Exact formula for the parabolic top-edge sum at height `Y`. -/
lemma par_sum_eq (n : ℤ) (δ' : ZMod M) {s : ℤ} (hs : s ≠ 0) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 0 < Y) :
    ∑' b : ℤ, wt M n δ' (ut s b s) * topI (ut s b s) m Y =
      -(1 / (2 * (m : ℂ) * M)) * ∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s) *
        ∑' j : ℤ, (((M : ℝ) / Y : ℝ) : ℂ) * Fp (2 * s) m ((M / Y) * (j + x.val / M)) := by
  have hY' : (Y : ℂ) ≠ 0 := ofReal_ne_zero.2 hY.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hMpos : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : ∑' b : ℤ, wt M n δ' (ut s b s) * topI (ut s b s) m Y =
      (-(1 / (m : ℂ)) * (Y : ℂ)⁻¹) * ∑' b : ℤ, wt M n δ' (ut s b s) * Hp (2 * s) m (b / Y) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun b => ?_)
    rw [topI_par s b m hY]
    ring
  have h2 := tsum_pair (w := fun b : ℤ => wt M n δ' (ut s b s)) (fun b => wt_ut_par_neg n δ' s b)
    (summable_wHp n δ' s hm hY)
  have hsF : Summable (fun b : ℤ => Fp (2 * s) m (b / Y)) :=
    (summable_Hp (2 * s) hm hY).add (summable_Hp_neg (2 * s) hm hY)
  have h3 : ∑' b : ℤ, wt M n δ' (ut s b s) * (Hp (2 * s) m (b / Y) + Hp (2 * s) m (-(b / Y))) =
      ∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s) *
        ∑' j : ℤ, Fp (2 * s) m ((((x.val : ℤ) + M * j : ℤ) : ℝ) / Y) := by
    refine (tsum_congr (fun b => ?_)).trans
      (tsum_classes (c := fun x : ZMod M => wt M n δ' (ut s ((x.val : ℤ) + M) s))
        (G := fun b : ℤ => Fp (2 * s) m (b / Y)) hsF)
    show wt M n δ' (ut s b s) * Fp (2 * s) m (b / Y) =
      wt M n δ' (ut s (((b : ZMod M).val : ℤ) + M) s) * Fp (2 * s) m (b / Y)
    rcases eq_or_ne b 0 with rfl | hb
    · simp [Fp_at_zero]
    · rw [wt_ut_par_mod n δ' s hb (by omega) (cast_rep _).symm]
  have h4 : ∀ x : ZMod M,
      ∑' j : ℤ, (((M : ℝ) / Y : ℝ) : ℂ) * Fp (2 * s) m ((M / Y) * (j + x.val / M)) =
        (((M : ℝ) / Y : ℝ) : ℂ) * ∑' j : ℤ, Fp (2 * s) m ((((x.val : ℤ) + M * j : ℤ) : ℝ) / Y) := by
    intro x
    rw [tsum_mul_left]
    congr 1
    refine tsum_congr (fun j => ?_)
    have hMinv : (M : ℝ) * (M : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hMR
    congr 1
    push_cast
    linear_combination ((x.val : ℝ) * Y⁻¹) * hMinv
  simp_rw [h4]
  rw [h1, h2, h3]
  have h5 : ∀ (T : ZMod M → ℂ) (k : ℂ),
      ∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s) * (k * T x) =
        k * ∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s) * T x := by
    intro T k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [h5]
  push_cast
  field_simp

/-- The `Y → ∞` value of one parabolic `(s, s)` class, per unit of weight. -/
def parC (M : ℕ) (s : ℤ) (m : ℕ) : ℂ :=
  (1 / (2 * (m : ℂ) * M)) * ((cP (2 * s)) ^ m)⁻¹ *
    (((π * (Real.sign (2 * (s : ℝ)) - Real.sign (-(2 * (s : ℝ)))) : ℝ) : ℂ) * I)

/-- **O7**: the parabolic `c = 0`, `a = d = s` top-edge sum converges as `Y → ∞`. -/
theorem tendsto_par (n : ℤ) (δ' : ZMod M) {s : ℤ} (hs : s ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun Y : ℝ => ∑' b : ℤ, wt M n δ' (ut s b s) * topI (ut s b s) m Y) atTop
      (𝓝 ((∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s)) * parC M s m)) := by
  have hβ : (2 * (s : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast hs)
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨K, -, hK⟩ := norm_Fp_le hβ m
  have hε : Tendsto (fun Y : ℝ => (M : ℝ) / Y) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with Y hY
    exact div_pos hMR hY
  have hR : ∀ x : ZMod M, Tendsto (fun Y : ℝ => ∑' j : ℤ, (((M : ℝ) / Y : ℝ) : ℂ) *
      Fp (2 * s) m ((M / Y) * (j + x.val / M))) atTop (𝓝 (∫ v, Fp (2 * s) m v)) := by
    intro x
    have hθ0 : (0 : ℝ) ≤ x.val / M := by positivity
    have hθ1 : (x.val : ℝ) / M ≤ 1 := by
      rw [div_le_one hMR]; exact_mod_cast (ZMod.val_lt x).le
    exact (tendsto_riemann (measurable_Fp _ m) (fun v hv => continuousAt_Fp hβ m hv) hK
      hθ0 hθ1).comp hε
  have hlim := (tendsto_finsetSum Finset.univ (fun x _ =>
    (hR x).const_mul (wt M n δ' (ut s ((x.val : ℤ) + M) s)))).const_mul
      (-(1 / (2 * (m : ℂ) * M)))
  have hval : -(1 / (2 * (m : ℂ) * M)) * ∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s) *
      ∫ v, Fp (2 * s) m v = (∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s)) * parC M s m := by
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [integral_Fp hβ m', ← Finset.sum_mul]
    unfold parC
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Y hY
  exact (par_sum_eq n δ' hs hm hY).symm

end RamanujanPetersson.HypPar


