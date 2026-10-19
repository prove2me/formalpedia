-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:23:25.779992+00:00
-- url     : https://prove2.me/submissions/a43c0b4c-7474-400a-aaac-0046c8e00e9e

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le
import Mathlib


section
section
/-! # L3Z_Cuts: candidate cuts beneath ZeroDetector (Proposition 8.2)

All statements are about the row `L`-series `twistedL ι χ u = L^S(ξ, ηχ•(u))` itself, whose
coefficient on an exterior ideal `𝔞` is `η(𝔞) conj(χ_𝔞(u))`.

* `TwistedConvexity` — (8.3) for the twisted rows: apart from a fixed finite set of rows (those
  for which `ηχ•(u)` is principal; at most one), `L^S(ξ, ηχ•(u))` continues to an entire function
  with `≪_ε q_u^{1/2+ε} (2 + |Im ξ|)^A` on `.003 ≤ Re ξ ≤ 4`.
* `RowLargeSieve` — Lemma 8.1 (8.2) for the family of rows of conductor `≪ U`: on exterior ideals
  the row coefficient is the primitive `ω_u` of p. 51 (it vanishes at the exterior primes dividing
  `u`, where `ω_u` ramifies), and distinct rows give distinct `ω_u`.
* `RowZeroFree` — the first half of Proposition 8.2: outside `E(U)`, `|E(U)| ≪ U^{1/2}`, the
  continuation has no zero in `Re ξ ≥ .996`, `|Im ξ| ≤ 4U^ρ`. -/

open NumberField

namespace ArtinPrimitiveRoots

namespace L3Z

/-- **(8.3) for the rows `ηχ•(u)`**, p. 52. -/
def TwistedConvexity (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ P : Finset (FreqClass 𝔪), ∃ A : ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → r ∉ P →
        ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
          (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ (freqElt g r) ξ) ∧
          ∀ ξ : ℂ, 3 / 1000 ≤ ξ.re → ξ.re ≤ 4 →
            ‖Λ ξ‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + ε) * (2 + |ξ.im|) ^ A

/-- **Lemma 8.1, (8.2)**, p. 51, for the rows of conductor `q_u < 2U`. -/
def RowLargeSieve (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
      ∀ U N : ℝ, 2 ≤ U → 2 ≤ N → ∀ T : Finset (FreqClass 𝔪),
        (∀ r ∈ T, (Ideal.absNorm r.1.1 : ℝ) < 2 * U) → ∀ B : Finset (Ideal (𝓞 F)),
        (∀ I ∈ B, IsExterior 𝔪 I ∧ (Ideal.absNorm I : ℝ) ≤ N) → ∀ b : Ideal (𝓞 F) → ℂ,
          ∑ r ∈ T, ‖∑ I ∈ B, b I * (χ.toFun I *
              starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r)))‖ ^ 2 ≤
            C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2

/-- **Proposition 8.2, first half**, p. 53: the zero-free rectangles. -/
def RowZeroFree (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
      ∃ E : ℝ → Finset (FreqClass 𝔪),
        (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
        ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 →
          U ≤ (Ideal.absNorm r.1.1 : ℝ) → (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
          ∀ Λ : ℂ → ℂ, Differentiable ℂ Λ →
            (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ (freqElt g r) ξ) →
            ∀ ξ : ℂ, 996 / 1000 ≤ ξ.re → |ξ.im| ≤ 4 * U ^ ρ → Λ ξ ≠ 0

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_BC: the reciprocal bound of p. 55 (Borel–Carathéodory and three circles)

Generic complex analysis, for the last step of Proposition 8.2:

* `exists_holo_log`: a nonvanishing holomorphic function on a disk has a holomorphic logarithm
  (continuous branch from `Complex.exists_continuousOn_eqOn_exp_comp`, then local `Complex.log`);
* `inv_bound_disk`: with the radii `R₂ = 1.0035 > r₂ = 1.003 > r₁ = 1.002 > r₀' = .9995 > r₀ = .999`
  of p. 55, if `f` is holomorphic and nonvanishing on `B(c, R₂)`, `‖f‖ ≤ M` there and
  `K⁻¹ ≤ ‖f‖ ≤ K` on `B(c, r₀')`, then `‖f⁻¹‖ ≤ exp (a (log M + 1)^θ)` on `‖z − c‖ ≤ r₁`, with
  `a` depending only on `K` and `θ = log(r₁/r₀)/log(r₂/r₀) < 1`. -/

open Complex Metric Set Filter Topology

namespace ArtinPrimitiveRoots

namespace L3Z

lemma isSimplyConnected_ball (c : ℂ) {R : ℝ} (hR : 0 < R) : IsSimplyConnected (ball c R) := by
  have := contractibleSpace_ball (x := c) hR
  show SimplyConnectedSpace (ball c R)
  infer_instance

/-- A holomorphic logarithm on a disk, normalized by `ℓ c = log (f c)`. -/
theorem exists_holo_log {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ (ball c R) ∧ (∀ z ∈ ball c R, exp (ℓ z) = f z) ∧
      ℓ c = log (f c) := by
  have h0 : (0 : ℂ) ∉ f '' ball c R := by
    rintro ⟨z, hz, hz0⟩
    exact hf0 z hz hz0
  obtain ⟨ℓ₀, hℓc, hℓe⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (isSimplyConnected_ball c hR) isOpen_ball hf.continuousOn h0
  have hcR : c ∈ ball c R := mem_ball_self hR
  set ℓ : ℂ → ℂ := fun z => ℓ₀ z - ℓ₀ c + log (f c) with hℓdef
  have hexp : ∀ z ∈ ball c R, exp (ℓ z) = f z := by
    intro z hz
    have h1 : exp (ℓ₀ z) = f z := hℓe hz
    have h2 : exp (ℓ₀ c) = f c := hℓe hcR
    simp only [hℓdef, exp_add, exp_sub, h1, h2, exp_log (hf0 c hcR)]
    field_simp [hf0 c hcR]
  have hcont : ContinuousOn ℓ (ball c R) :=
    (hℓc.sub continuousOn_const).add continuousOn_const
  refine ⟨ℓ, ?_, hexp, by simp [hℓdef]⟩
  intro z₀ hz₀
  have hnhds : ball c R ∈ 𝓝 z₀ := isOpen_ball.mem_nhds hz₀
  have hca : ContinuousAt ℓ z₀ := hcont.continuousAt hnhds
  have hfz₀ := hf0 z₀ hz₀
  have hev : ∀ᶠ z in 𝓝 z₀, ℓ z = ℓ z₀ + log (f z / f z₀) := by
    have hsmall : ∀ᶠ z in 𝓝 z₀, ‖ℓ z - ℓ z₀‖ < 1 := by
      exact (hca.eventually (Metric.ball_mem_nhds (ℓ z₀) one_pos)).mono
        fun z hz => by rwa [dist_eq_norm] at hz
    filter_upwards [hsmall, hnhds] with z hz hzR
    have him : |(ℓ z - ℓ z₀).im| < 1 := (abs_im_le_norm _).trans_lt hz
    have hq : f z / f z₀ = exp (ℓ z - ℓ z₀) := by
      rw [exp_sub, hexp z hzR, hexp z₀ hz₀]
    rw [hq, log_exp]
    · ring
    · have := neg_abs_le (ℓ z - ℓ z₀).im
      linarith [Real.pi_gt_three]
    · have := le_abs_self (ℓ z - ℓ z₀).im
      linarith [Real.pi_gt_three]
  have hfd : DifferentiableAt ℂ f z₀ := (hf z₀ hz₀).differentiableAt hnhds
  have hslit : f z₀ / f z₀ ∈ slitPlane := by rw [div_self hfz₀]; exact one_mem_slitPlane
  have hd : DifferentiableAt ℂ (fun z => ℓ z₀ + log (f z / f z₀)) z₀ :=
    (differentiableAt_const _).add ((hfd.div_const _).clog hslit)
  exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt

lemma re_eq_log_norm {ℓ f : ℂ → ℂ} {z : ℂ} (h : exp (ℓ z) = f z) : (ℓ z).re = Real.log ‖f z‖ := by
  rw [← h, norm_exp, Real.log_exp]

/-- The Borel–Carathéodory bound on a sub-disk, recentred. -/
lemma bc_centered {ℓ : ℂ → ℂ} {c : ℂ} {R r m : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hm : 0 ≤ m)
    (hd : DifferentiableOn ℂ ℓ (ball c R)) (hre : ∀ z ∈ ball c R, (ℓ z).re ≤ m) {z : ℂ}
    (hz : ‖z - c‖ ≤ r) :
    ‖ℓ z‖ ≤ (2 * (m + 1) * r + ‖ℓ c‖ * (R + r)) / (R - r) := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  set g : ℂ → ℂ := fun w => ℓ (w + c)
  have hgd : DifferentiableOn ℂ g (ball 0 R) := by
    refine hd.comp (differentiableOn_id.add_const c) fun w hw => ?_
    simpa [mem_ball, dist_eq_norm] using hw
  have hgm : MapsTo g (ball 0 R) {w | w.re ≤ m + 1} := by
    intro w hw
    have : w + c ∈ ball c R := by simpa [mem_ball, dist_eq_norm] using hw
    show (ℓ (w + c)).re ≤ m + 1
    linarith [hre _ this]
  have hw : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]; linarith
  have h := Complex.borelCaratheodory (by linarith : (0 : ℝ) < m + 1) hgd hgm hR hw
  simp only [g, sub_add_cancel, zero_add] at h
  have hpos : 0 < R - ‖z - c‖ := by linarith
  have hpos' : 0 < R - r := by linarith
  calc ‖ℓ z‖ ≤ 2 * (m + 1) * ‖z - c‖ / (R - ‖z - c‖) + ‖ℓ c‖ * (R + ‖z - c‖) / (R - ‖z - c‖) := h
    _ = (2 * (m + 1) * ‖z - c‖ + ‖ℓ c‖ * (R + ‖z - c‖)) / (R - ‖z - c‖) := by ring
    _ ≤ (2 * (m + 1) * r + ‖ℓ c‖ * (R + r)) / (R - r) := by
      apply div_le_div₀ (by positivity) (by gcongr) hpos' (by linarith)

/-- The exponent `θ = log(r₁/r₀)/log(r₂/r₀)` of p. 55. -/
noncomputable def theta : ℝ :=
  (Real.log (1002 / 1000) - Real.log (999 / 1000)) / (Real.log (1003 / 1000) - Real.log (999 / 1000))

lemma theta_pos : 0 < theta := by
  unfold theta
  apply div_pos
  · linarith [Real.log_lt_log (by norm_num : (0 : ℝ) < 999 / 1000) (by norm_num : (999 / 1000 : ℝ) < 1002 / 1000)]
  · linarith [Real.log_lt_log (by norm_num : (0 : ℝ) < 999 / 1000) (by norm_num : (999 / 1000 : ℝ) < 1003 / 1000)]

lemma theta_lt_one : theta < 1 := by
  unfold theta
  have h2 : Real.log (999 / 1000) < Real.log (1003 / 1000) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [div_lt_one (by linarith)]
  linarith [Real.log_lt_log (by norm_num : (0 : ℝ) < 1002 / 1000) (by norm_num : (1002 / 1000 : ℝ) < 1003 / 1000)]

/-- **The reciprocal bound on one disk**, p. 55. -/
theorem inv_bound_disk (K : ℝ) (hK : 1 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ ∀ (f : ℂ → ℂ) (c : ℂ) (M : ℝ), 1 ≤ M →
      DifferentiableOn ℂ f (ball c (10035 / 10000)) →
      (∀ z ∈ ball c (10035 / 10000), f z ≠ 0) →
      (∀ z ∈ ball c (10035 / 10000), ‖f z‖ ≤ M) →
      (∀ z ∈ ball c (9995 / 10000), ‖f z‖ ≤ K ∧ ‖(f z)⁻¹‖ ≤ K) →
      ∀ z : ℂ, ‖z - c‖ ≤ 1002 / 1000 →
        ‖(f z)⁻¹‖ ≤ Real.exp (a * (Real.log M + 1) ^ theta) := by
  set k := Real.log K with hk
  have hk0 : 0 ≤ k := Real.log_nonneg hK
  -- the constants
  set A0 : ℝ := (2 * (k + 1) * (999 / 1000) + (k + Real.pi) * (9995 / 10000 + 999 / 1000)) /
    (9995 / 10000 - 999 / 1000) with hA0
  have hA0pos : 0 < A0 := by rw [hA0]; positivity
  set b : ℝ := (2 * 1 * (1003 / 1000) + (k + Real.pi) * (10035 / 10000 + 1003 / 1000)) /
    (10035 / 10000 - 1003 / 1000) + A0 with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  refine ⟨A0 ^ (1 - theta) * b ^ theta + A0, by positivity, ?_⟩
  intro f c M hM hfd hf0 hfM hfK z hz
  have hR : (0 : ℝ) < 10035 / 10000 := by norm_num
  obtain ⟨ℓ, hℓd, hℓe, hℓc⟩ := exists_holo_log hR hfd hf0
  have hcR : c ∈ ball c (10035 / 10000) := mem_ball_self hR
  have hc0 : c ∈ ball c (9995 / 10000) := mem_ball_self (by norm_num)
  -- `‖ℓ c‖ ≤ k + π`
  have hℓc_le : ‖ℓ c‖ ≤ k + Real.pi := by
    rw [hℓc]
    have hfc := hfK c hc0
    have hfc0 := hf0 c hcR
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |(log (f c)).re| ≤ k := by
      rw [log_re, abs_le]
      have hn : 0 < ‖f c‖ := norm_pos_iff.2 hfc0
      constructor
      · have h1 : ‖f c‖⁻¹ ≤ K := by rw [← norm_inv]; exact hfc.2
        have : Real.log (‖f c‖⁻¹) ≤ Real.log K := Real.log_le_log (by positivity) h1
        rw [Real.log_inv] at this
        linarith
      · exact Real.log_le_log hn hfc.1
    have him : |(log (f c)).im| ≤ Real.pi := by
      rw [log_im, abs_le]
      exact ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩
    linarith
  -- inner disk bound
  have hinner : ∀ w : ℂ, ‖w - c‖ ≤ 999 / 1000 → ‖ℓ w‖ ≤ A0 := by
    intro w hw
    have hd' : DifferentiableOn ℂ ℓ (ball c (9995 / 10000)) :=
      hℓd.mono (ball_subset_ball (by norm_num))
    have hre : ∀ z ∈ ball c (9995 / 10000), (ℓ z).re ≤ k := by
      intro z hz'
      have hzR : z ∈ ball c (10035 / 10000) := ball_subset_ball (by norm_num) hz'
      rw [re_eq_log_norm (hℓe z hzR)]
      exact Real.log_le_log (norm_pos_iff.2 (hf0 z hzR)) (hfK z hz').1
    have := bc_centered (by norm_num) (by norm_num) hk0 hd' hre hw
    refine this.trans ?_
    rw [hA0]
    gcongr
  -- outer disk bound
  set m := Real.log M with hm
  have hm0 : 0 ≤ m := Real.log_nonneg hM
  set A2 : ℝ := (m + 1) * b with hA2
  have hA0A2 : A0 ≤ A2 := by
    rw [hA2, hb]
    nlinarith [show 0 ≤ (2 * 1 * (1003 / 1000) + (k + Real.pi) * (10035 / 10000 + 1003 / 1000)) /
      (10035 / 10000 - 1003 / 1000) by positivity]
  have houter : ∀ w : ℂ, ‖w - c‖ ≤ 1003 / 1000 → ‖ℓ w‖ ≤ A2 := by
    intro w hw
    have hre : ∀ z ∈ ball c (10035 / 10000), (ℓ z).re ≤ m := by
      intro z hz'
      rw [re_eq_log_norm (hℓe z hz')]
      exact Real.log_le_log (norm_pos_iff.2 (hf0 z hz')) (hfM z hz')
    have := bc_centered (by norm_num) (by norm_num) hm0 hℓd hre hw
    refine this.trans ?_
    rw [hA2, hb]
    have hp : 0 ≤ (k + Real.pi) * (10035 / 10000 + 1003 / 1000) / (10035 / 10000 - 1003 / 1000) := by
      positivity
    have e1 : (2 * (m + 1) * (1003 / 1000) + ‖ℓ c‖ * (10035 / 10000 + 1003 / 1000)) /
        (10035 / 10000 - 1003 / 1000) ≤
        (2 * (m + 1) * (1003 / 1000) + (k + Real.pi) * (10035 / 10000 + 1003 / 1000)) /
        (10035 / 10000 - 1003 / 1000) := by gcongr
    refine e1.trans ?_
    have : (2 * (m + 1) * (1003 / 1000) + (k + Real.pi) * (10035 / 10000 + 1003 / 1000)) /
        (10035 / 10000 - 1003 / 1000) = (m + 1) * (2 * 1 * (1003 / 1000) / (10035 / 10000 - 1003 / 1000))
          + (k + Real.pi) * (10035 / 10000 + 1003 / 1000) / (10035 / 10000 - 1003 / 1000) := by ring
    rw [this]
    have h1 : (k + Real.pi) * (10035 / 10000 + 1003 / 1000) / (10035 / 10000 - 1003 / 1000) ≤
        (m + 1) * ((k + Real.pi) * (10035 / 10000 + 1003 / 1000) / (10035 / 10000 - 1003 / 1000)) := by
      nlinarith
    have : (m + 1) * ((2 * 1 * (1003 / 1000) + (k + Real.pi) * (10035 / 10000 + 1003 / 1000)) /
        (10035 / 10000 - 1003 / 1000) + A0) =
        (m + 1) * (2 * 1 * (1003 / 1000) / (10035 / 10000 - 1003 / 1000)) +
        (m + 1) * ((k + Real.pi) * (10035 / 10000 + 1003 / 1000) / (10035 / 10000 - 1003 / 1000)) +
        (m + 1) * A0 := by ring
    rw [this]
    nlinarith
  -- three circles at `z`
  have hthree : ‖ℓ z‖ ≤ A0 ^ (1 - theta) * A2 ^ theta := by
    by_cases hz0 : ‖z - c‖ ≤ 999 / 1000
    · calc ‖ℓ z‖ ≤ A0 := hinner z hz0
        _ = A0 ^ (1 - theta) * A0 ^ theta := by
          rw [← Real.rpow_add hA0pos]; simp
        _ ≤ A0 ^ (1 - theta) * A2 ^ theta := by
          gcongr
          exact theta_pos.le
    push Not at hz0
    have hwpos : 0 < ‖z - c‖ := by linarith
    set l := Real.log (999 / 1000)
    set u := Real.log (1003 / 1000)
    have hlu : l < u := Real.log_lt_log (by norm_num) (by norm_num)
    set h : ℂ → ℂ := fun s => ℓ (c + exp s)
    have hmemR : ∀ s : ℂ, s.re ≤ u → c + exp s ∈ ball c (10035 / 10000) := by
      intro s hs
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_exp]
      calc Real.exp s.re ≤ Real.exp u := Real.exp_le_exp.2 hs
        _ = 1003 / 1000 := Real.exp_log (by norm_num)
        _ < 10035 / 10000 := by norm_num
    have hhd : DifferentiableOn ℂ h {s | s.re ≤ u} := by
      intro s hs
      have h1 : DifferentiableAt ℂ ℓ (c + exp s) :=
        (hℓd _ (hmemR s hs)).differentiableAt (isOpen_ball.mem_nhds (hmemR s hs))
      exact (h1.comp s ((differentiableAt_const c).add (differentiableAt_exp))).differentiableWithinAt
    have hDC : DiffContOnCl ℂ h (Complex.HadamardThreeLines.verticalStrip l u) := by
      apply DifferentiableOn.diffContOnCl
      refine hhd.mono ?_
      have hcl : IsClosed {s : ℂ | s.re ≤ u} := isClosed_le continuous_re continuous_const
      refine closure_minimal ?_ hcl
      intro s hs
      exact le_of_lt hs.2
    have hnormexp : ∀ s : ℂ, ‖c + exp s - c‖ = Real.exp s.re := by
      intro s; rw [add_sub_cancel_left, norm_exp]
    have hB : BddAbove ((norm ∘ h) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
      refine ⟨A2, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      apply houter
      rw [hnormexp]
      calc Real.exp s.re ≤ Real.exp u := Real.exp_le_exp.2 hs.2
        _ = 1003 / 1000 := Real.exp_log (by norm_num)
    have ha : ∀ s ∈ re ⁻¹' {l}, ‖h s‖ ≤ A0 := by
      intro s hs
      apply hinner
      rw [hnormexp, show s.re = l from hs]
      exact (Real.exp_log (by norm_num)).le
    have hb' : ∀ s ∈ re ⁻¹' {u}, ‖h s‖ ≤ A2 := by
      intro s hs
      apply houter
      rw [hnormexp, show s.re = u from hs]
      exact (Real.exp_log (by norm_num)).le
    set s := log (z - c)
    have hzc0 : z - c ≠ 0 := norm_pos_iff.1 hwpos
    have hs_re : s.re = Real.log ‖z - c‖ := log_re _
    have hes : exp s = z - c := exp_log hzc0
    have hsl : l ≤ s.re := by
      rw [hs_re]; exact Real.log_le_log (by norm_num) hz0.le
    have hs1 : s.re ≤ Real.log (1002 / 1000) := by
      rw [hs_re]; exact Real.log_le_log hwpos hz
    have hsu : s.re ≤ u := hs1.trans (Real.log_le_log (by norm_num) (by norm_num))
    have hmain := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      hlu ⟨hsl, hsu⟩ hDC hB ha hb'
    have hhs : h s = ℓ z := by simp only [h, hes, add_sub_cancel]
    rw [hhs] at hmain
    refine hmain.trans ?_
    have hθs : (s.re - l) / (u - l) ≤ theta := by
      unfold theta
      apply div_le_div_of_nonneg_right _ (by linarith)
      linarith
    have hθs0 : 0 ≤ (s.re - l) / (u - l) := div_nonneg (by linarith) (by linarith)
    -- `A0^(1-x) A2^x` is monotone in `x` since `A0 ≤ A2`
    have key : ∀ x y : ℝ, x ≤ y → A0 ^ (1 - x) * A2 ^ x ≤ A0 ^ (1 - y) * A2 ^ y := by
      intro x y hxy
      have hA2pos : 0 < A2 := lt_of_lt_of_le hA0pos hA0A2
      have e1 : A0 ^ (1 - x) = A0 ^ (1 - y) * A0 ^ (y - x) := by
        rw [← Real.rpow_add hA0pos]; ring_nf
      have e2 : A2 ^ y = A2 ^ x * A2 ^ (y - x) := by
        rw [← Real.rpow_add hA2pos]; ring_nf
      rw [e1, e2]
      have : A0 ^ (y - x) ≤ A2 ^ (y - x) :=
        Real.rpow_le_rpow hA0pos.le hA0A2 (by linarith)
      have h1 : 0 ≤ A0 ^ (1 - y) := by positivity
      have h2 : 0 ≤ A2 ^ x := by positivity
      calc A0 ^ (1 - y) * A0 ^ (y - x) * A2 ^ x = (A0 ^ (1 - y) * A2 ^ x) * A0 ^ (y - x) := by ring
        _ ≤ (A0 ^ (1 - y) * A2 ^ x) * A2 ^ (y - x) := by gcongr
        _ = A0 ^ (1 - y) * (A2 ^ x * A2 ^ (y - x)) := by ring
    exact key _ _ hθs
  -- conclusion
  have hzR : z ∈ ball c (10035 / 10000) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hfz : (f z)⁻¹ = exp (-ℓ z) := by rw [exp_neg, hℓe z hzR]
  rw [hfz, norm_exp]
  apply Real.exp_le_exp.2
  have h1 : (-ℓ z).re ≤ ‖ℓ z‖ := by
    rw [neg_re]; exact (neg_le_abs _).trans (abs_re_le_norm _)
  refine h1.trans (hthree.trans ?_)
  rw [hA2, Real.mul_rpow (by linarith) hbpos.le]
  have hm1 : 1 ≤ m + 1 := by linarith
  have e : A0 ^ (1 - theta) * ((m + 1) ^ theta * b ^ theta) =
      (A0 ^ (1 - theta) * b ^ theta) * (m + 1) ^ theta := by ring
  rw [e]
  have hp : 0 ≤ (m + 1) ^ theta := by positivity
  nlinarith [mul_nonneg hA0pos.le hp]

end L3Z

end ArtinPrimitiveRoots

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


/-- The uniform upper bound `‖L^S(ξ, ηχ•(u))‖ ≤ ∑_𝔞 q_𝔞^{-σ₀}` on `Re ξ ≥ σ₀ > 1`. -/
theorem norm_twistedL_le (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪)
    (u : SInt 𝔪) {σ₀ : ℝ} (hσ : 1 < σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖twistedL ι χ u s‖ ≤ ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ₀) := by
  rw [twistedL_eq_tsum]
  have hsum := T12B.summable_absNorm_rpow (F := F) hσ
  have hb : ∀ I : Ideal (𝓞 F), ‖twCoeff ι χ u I * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤
      ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ₀) :=
    norm_term_le (twCoeff_bot ι χ u) (norm_twCoeff_le ι h𝔪 χ u) hs
  have hn : Summable fun I : Ideal (𝓞 F) => ‖twCoeff ι χ u I * (Ideal.absNorm I : ℂ) ^ (-s)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hb hn hsum)

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Main: Proposition 8.2 from the zero-free rectangles and the convexity bound

`zeroDetector_of_rowZeroFree`: the conclusion of the stub
`exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one`, from `RowZeroFree` and
`TwistedConvexity`. This is the last paragraph of the proof of Proposition 8.2 (p. 55):
`E'(U) = E(U) ∪ P`, `D = Λ⁻¹`, and the reciprocal bound from `inv_bound_disk` on the disks about
`2 + it`, with `M = C' U^e` from (8.3) and `K` from the Euler product on `Re ξ ≥ 1.0005`. -/

open NumberField Complex Metric Set Filter Topology

namespace ArtinPrimitiveRoots

namespace L3Z

/-- `y^θ ≤ Y₀^{θ-1} y + Y₀^θ`. -/
lemma rpow_le_young {θ : ℝ} (hθ1 : θ < 1) (hθ0 : 0 < θ) {Y₀ y : ℝ} (hY : 0 < Y₀) (hy : 0 ≤ y) :
    y ^ θ ≤ Y₀ ^ (θ - 1) * y + Y₀ ^ θ := by
  rcases le_or_gt y Y₀ with h | h
  · have : y ^ θ ≤ Y₀ ^ θ := Real.rpow_le_rpow hy h hθ0.le
    have : 0 ≤ Y₀ ^ (θ - 1) * y := by positivity
    linarith
  · have hy0 : 0 < y := hY.trans h
    have e : y ^ θ = y ^ (θ - 1) * y := by
      rw [← Real.rpow_add_one hy0.ne']; ring_nf
    have : y ^ (θ - 1) ≤ Y₀ ^ (θ - 1) :=
      Real.rpow_le_rpow_of_nonpos hY h.le (by linarith)
    have : 0 ≤ Y₀ ^ θ := by positivity
    rw [e]
    nlinarith

/-- `exp (a (c + e log U)^θ) ≪_ε U^ε`. -/
lemma exp_rpow_log_le {θ : ℝ} (hθ1 : θ < 1) (hθ0 : 0 < θ) {a c e : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (he : 0 ≤ e) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → Real.exp (a * (c + e * Real.log U) ^ θ) ≤ C * U ^ ε := by
  set x := ε / (a * e + 1) with hx
  have hxpos : 0 < x := by positivity
  set Y₀ := x ^ (1 / (θ - 1)) with hY
  have hY0 : 0 < Y₀ := by positivity
  have hYx : Y₀ ^ (θ - 1) = x := by
    rw [hY, ← Real.rpow_mul hxpos.le]
    rw [one_div, inv_mul_cancel₀ (by linarith : θ - 1 ≠ 0), Real.rpow_one]
  refine ⟨Real.exp (a * (x * c + Y₀ ^ θ)), fun U hU => ?_⟩
  have hU0 : 0 < U := by linarith
  have hlog : 0 ≤ Real.log U := Real.log_nonneg hU
  have hy : 0 ≤ c + e * Real.log U := by positivity
  have h1 := rpow_le_young hθ1 hθ0 hY0 hy
  rw [hYx] at h1
  have hxe : a * (x * e) ≤ ε := by
    rw [hx]
    have : a * (ε / (a * e + 1) * e) = ε * (a * e / (a * e + 1)) := by ring
    rw [this]
    have : a * e / (a * e + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  rw [Real.rpow_def_of_pos hU0, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have : a * (c + e * Real.log U) ^ θ ≤ a * (x * (c + e * Real.log U) + Y₀ ^ θ) :=
    mul_le_mul_of_nonneg_left h1 ha
  have h2 : a * (x * (c + e * Real.log U) + Y₀ ^ θ) =
      a * (x * c + Y₀ ^ θ) + a * (x * e) * Real.log U := by ring
  nlinarith

/-- `SmallPrimesDvd` is monotone in the cutoff. -/
lemma smallPrimesDvd_mono {F : Type*} [Field F] [NumberField F] {N₁ N₂ : ℕ} (h : N₁ ≤ N₂)
    {𝔪 : Ideal (𝓞 F)} (h𝔪 : SmallPrimesDvd N₂ 𝔪) : SmallPrimesDvd N₁ 𝔪 :=
  fun P hP hP0 hN => h𝔪 P hP hP0 (hN.trans h)

/-- `(2 + y)^A ≤ (2 + Y)^|A|` for `0 ≤ y ≤ Y`. -/
lemma two_add_rpow_le {A y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    (2 + y) ^ A ≤ (2 + Y) ^ |A| := by
  rcases le_or_gt 0 A with hA | hA
  · rw [abs_of_nonneg hA]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hA
  · have h1 : (2 + y) ^ A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hA.le
    have h2 : 1 ≤ (2 + Y) ^ |A| := Real.one_le_rpow (by linarith) (abs_nonneg A)
    linarith

theorem zeroDetector_of_rowZeroFree (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ)
    (hZF : RowZeroFree F ι) (hTC : TwistedConvexity F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
        ∃ E : ℝ → Finset (FreqClass 𝔪),
          (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪,
            r ≠ principalFreq 𝔪 → U ≤ (Ideal.absNorm r.1.1 : ℝ) →
            (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
            ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < 3 * U ^ ρ} ∧
              (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < 3 * U ^ ρ →
                D ξ * twistedL ι χ (freqElt g r) ξ = 1) ∧
              ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → ‖D ξ‖ ≤ C * U ^ ε := by
  classical
  obtain ⟨N₁, hN₁⟩ := hZF
  obtain ⟨N₂, hN₂⟩ := hTC
  refine ⟨max N₁ N₂, fun 𝔪 h𝔪 hS χ g => ?_⟩
  obtain ⟨ρ, hρ, C₀, U₀, E, hE, hZ⟩ :=
    hN₁ 𝔪 h𝔪 (smallPrimesDvd_mono (le_max_left _ _) hS) χ g
  obtain ⟨P, A, hTCr⟩ := hN₂ 𝔪 h𝔪 (smallPrimesDvd_mono (le_max_right _ _) hS) χ g
  obtain ⟨C₁, hC₁⟩ := hTCr (1 / 2) (by norm_num)
  -- the Euler constants on `Re ξ ≥ 1.0005` and `Re ξ ≥ 5/2`
  obtain ⟨B₁, hB₁0, hB₁⟩ := twistedL_inv_bound (F := F) (by norm_num : (1 : ℝ) < 10005 / 10000)
  obtain ⟨B₂, hB₂0, hB₂⟩ := twistedL_inv_bound (F := F) (by norm_num : (1 : ℝ) < 5 / 2)
  set Z₁ : ℝ := ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(10005 / 10000 : ℝ))
  set K : ℝ := max 1 (max Z₁ B₁) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  obtain ⟨a, ha, hdisk⟩ := inv_bound_disk K hK1
  set C' : ℝ := max 1 (2 * max C₁ 0 * 6 ^ |A|) with hC'
  have hC'1 : 1 ≤ C' := le_max_left _ _
  set e : ℝ := 1 + ρ * |A| with he
  have he0 : 0 ≤ e := by positivity
  refine ⟨ρ, hρ, C₀ + P.card, max U₀ 1, fun U => E U ∪ P, ?_, ?_⟩
  · intro U hU
    have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
    have h1 : ((E U ∪ P).card : ℝ) ≤ (E U).card + P.card := by
      exact_mod_cast Finset.card_union_le _ _
    have h2 := hE U ((le_max_left _ _).trans hU)
    have h3 : (1 : ℝ) ≤ U ^ (1 / 2 : ℝ) := Real.one_le_rpow hU1 (by norm_num)
    have h4 : (P.card : ℝ) ≤ P.card * U ^ (1 / 2 : ℝ) := by
      nlinarith [(Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)]
    nlinarith
  intro ε hε
  obtain ⟨C₂, hC₂⟩ := exp_rpow_log_le theta_lt_one theta_pos ha.le
    (by have := Real.log_nonneg hC'1; linarith : 0 ≤ Real.log C' + 1) he0 hε
  refine ⟨max C₂ B₂, fun U hU r hr hU1 hU2 hrE => ?_⟩
  have hU1' : 1 ≤ U := (le_max_right _ _).trans hU
  have hU0 : 0 < U := by linarith
  have hUρ : 1 ≤ U ^ ρ := Real.one_le_rpow hU1' hρ.le
  have hrE' : r ∉ E U := fun h => hrE (Finset.mem_union_left _ h)
  have hrP : r ∉ P := fun h => hrE (Finset.mem_union_right _ h)
  obtain ⟨Λ, hΛd, hΛe, hΛb⟩ := hC₁ r hr hrP
  set u := freqElt g r
  have hL0 : ∀ ξ : ℂ, 1 < ξ.re → twistedL ι χ u ξ ≠ 0 := fun ξ hξ =>
    (twistedL_inv_bound (F := F) hξ |>.choose_spec.2 ι 𝔪 h𝔪 χ u ξ le_rfl).1
  -- nonvanishing
  have hnz : ∀ ξ : ℂ, 996 / 1000 < ξ.re → |ξ.im| ≤ 4 * U ^ ρ → Λ ξ ≠ 0 := by
    intro ξ h1 h2
    by_cases hre : 1 < ξ.re
    · rw [hΛe ξ hre]; exact hL0 ξ hre
    · exact hZ U ((le_max_left _ _).trans hU) r hr hU1 hU2 hrE' Λ hΛd hΛe ξ h1.le h2
  refine ⟨fun ξ => (Λ ξ)⁻¹, ?_, ?_, ?_⟩
  · intro ξ hξ
    exact ((hΛd ξ).inv (hnz ξ (by linarith [hξ.1]) (by linarith [hξ.2]))).differentiableWithinAt
  · intro ξ hξ _
    show (Λ ξ)⁻¹ * twistedL ι χ u ξ = 1
    rw [← hΛe ξ hξ]
    exact inv_mul_cancel₀ (by rw [hΛe ξ hξ]; exact hL0 ξ hξ)
  · intro ξ h1 h2
    show ‖(Λ ξ)⁻¹‖ ≤ max C₂ B₂ * U ^ ε
    have hUε : 1 ≤ U ^ ε := Real.one_le_rpow hU1' hε.le
    have hmax0 : 0 ≤ max C₂ B₂ := le_max_of_le_right hB₂0
    by_cases hbig : 5 / 2 ≤ ξ.re
    · rw [hΛe ξ (by linarith)]
      have := (hB₂ ι 𝔪 h𝔪 χ u ξ hbig).2
      calc ‖(twistedL ι χ u ξ)⁻¹‖ ≤ B₂ := this
        _ ≤ max C₂ B₂ := le_max_right _ _
        _ ≤ max C₂ B₂ * U ^ ε := le_mul_of_one_le_right hmax0 hUε
    push Not at hbig
    set c : ℂ := (2 : ℂ) + (ξ.im : ℂ) * I with hc
    have hξc : ‖ξ - c‖ ≤ 1002 / 1000 := by
      have : ξ - c = ((ξ.re - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hball : ∀ z ∈ ball c (10035 / 10000), 9965 / 10000 < z.re ∧ z.re < 30035 / 10000 ∧
        |z.im| ≤ 2 * U ^ ρ + 10035 / 10000 := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have hre := (abs_re_le_norm (z - c)).trans_lt hz
      have him := (abs_im_le_norm (z - c)).trans_lt hz
      simp only [sub_re, sub_im, hc, add_re, add_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im,
        mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] at hre him
      rw [abs_lt] at hre
      refine ⟨by linarith, by linarith, ?_⟩
      have := abs_sub_abs_le_abs_sub z.im ξ.im
      linarith
    have hM1 : 1 ≤ C' * U ^ e := one_le_mul_of_one_le_of_one_le hC'1 (Real.one_le_rpow hU1' he0)
    have hb := hdisk Λ c (C' * U ^ e) hM1 hΛd.differentiableOn
      (fun z hz => by
        obtain ⟨h1, -, h3⟩ := hball z hz
        exact hnz z (by linarith) (by linarith))
      (fun z hz => by
        obtain ⟨h1, h2', h3⟩ := hball z hz
        have hq0 : (0 : ℝ) ≤ Ideal.absNorm r.1.1 := Nat.cast_nonneg _
        have hΛz := hΛb z (by linarith) (by linarith)
        have hp : (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + 1 / 2 : ℝ) = Ideal.absNorm r.1.1 := by
          norm_num
        rw [hp] at hΛz
        have ht : (2 + |z.im|) ^ A ≤ (2 + 4 * U ^ ρ) ^ |A| :=
          two_add_rpow_le (abs_nonneg _) (by linarith)
        have ht2 : (2 + 4 * U ^ ρ) ^ |A| ≤ 6 ^ |A| * U ^ (ρ * |A|) := by
          rw [Real.rpow_mul hU0.le, ← Real.mul_rpow (by norm_num) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg A)
        have hX0 : 0 ≤ (2 + |z.im|) ^ A := by positivity
        calc ‖Λ z‖ ≤ C₁ * Ideal.absNorm r.1.1 * (2 + |z.im|) ^ A := hΛz
          _ ≤ max C₁ 0 * Ideal.absNorm r.1.1 * (2 + |z.im|) ^ A := by gcongr; exact le_max_left _ _
          _ ≤ max C₁ 0 * (2 * U) * (6 ^ |A| * U ^ (ρ * |A|)) := by
            have h0 : 0 ≤ max C₁ 0 := le_max_right _ _
            exact mul_le_mul (mul_le_mul_of_nonneg_left hU2.le h0) (ht.trans ht2) hX0
              (by positivity)
          _ = (2 * max C₁ 0 * 6 ^ |A|) * U ^ e := by
            rw [he, Real.rpow_add hU0, Real.rpow_one]; ring
          _ ≤ C' * U ^ e := by gcongr; exact le_max_right _ _)
      (fun z hz => by
        rw [mem_ball, dist_eq_norm] at hz
        have hre := (abs_re_le_norm (z - c)).trans_lt hz
        simp only [sub_re, hc, add_re, re_ofNat, ofReal_re, mul_re, I_re, I_im, mul_zero,
          mul_one, sub_zero, ofReal_im, add_zero] at hre
        rw [abs_lt] at hre
        have hz1 : 10005 / 10000 ≤ z.re := by linarith
        rw [hΛe z (by linarith)]
        exact ⟨(norm_twistedL_le ι h𝔪 χ u (by norm_num) hz1).trans
            ((le_max_left _ _).trans (le_max_right _ _)),
          (hB₁ ι 𝔪 h𝔪 χ u z hz1).2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩)
      ξ hξc
    have hlog : Real.log (C' * U ^ e) + 1 = (Real.log C' + 1) + e * Real.log U := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow hU0]; ring
    rw [hlog] at hb
    calc ‖(Λ ξ)⁻¹‖ ≤ _ := hb
      _ ≤ C₂ * U ^ ε := hC₂ U hU1'
      _ ≤ max C₂ B₂ * U ^ ε := by gcongr; exact le_max_left _ _

end L3Z

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

noncomputable def cancelledKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma (z + 1) * dslope f 0 z * g z

noncomputable def literalKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma z * f z * g z

theorem cancelledKernel_eq_literal {f g : ℂ → ℂ} {Y : ℝ} (hf0 : f 0 = 0)
    {z : ℂ} (hz : z ≠ 0) : cancelledKernel f g Y z = literalKernel f g Y z := by
  unfold cancelledKernel literalKernel
  rw [Gamma_add_one z hz, dslope_of_ne f hz]
  simp only [slope, sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

theorem dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr hf.differentiableOn

theorem cancelledKernel_differentiableAt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {Y : ℝ} (hY : 0 < Y) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (cancelledKernel f g Y) z := by
  exact ((((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).mul
    ((gamma_differentiableAt_right (by change 0 < z.re + 1; linarith)).comp z
      (differentiableAt_id.add_const 1))).mul (dslope_entire hf z)).mul (hg z))

theorem literalKernel_norm (f g : ℂ → ℂ) {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖literalKernel f g Y z‖ = Y ^ z.re * ‖Gamma z‖ * ‖f z‖ * ‖g z‖ := by
  simp only [literalKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]

theorem cancelledKernel_large_height_bound {f g : ℂ → ℂ} (hf0 : f 0 = 0)
    {Y a b A B G : ℝ} (hY : 1 ≤ Y) (n : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgamma : ∀ z : ℂ, a + 1 ≤ z.re → z.re ≤ b + 1 →
      (1 + |z.im|) ^ (n + 2) * ‖Gamma z‖ ≤ G)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) (hzi : 1 ≤ |z.im|) :
    ‖cancelledKernel f g Y z‖ ≤ (Y ^ b * G * A * B) / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzi
  have hga := hgamma (z + 1) (by simpa using hza) (by simpa using hzb)
  simp only [add_im, one_im, add_zero] at hga
  have hweighted : (1 + z.im ^ 2) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) ≤ G := by
    calc
      _ ≤ (1 + |z.im|) ^ 2 * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by
        gcongr
        nlinarith [sq_abs z.im, abs_nonneg z.im]
      _ = (1 + |z.im|) ^ (n + 2) * ‖Gamma (z + 1)‖ := by rw [pow_add]; ring
      _ ≤ _ := hga
  have hgdiv : ‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n ≤ G / (1 + z.im ^ 2) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hweighted)
  rw [cancelledKernel_eq_literal hf0 hz0, literalKernel_norm f g hY0]
  have hnorm : 1 ≤ ‖z‖ := hzi.trans (Complex.abs_im_le_norm z)
  have hΓ : ‖Gamma z‖ ≤ ‖Gamma (z + 1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hnorm
  have hYb : Y ^ z.re ≤ Y ^ b := Real.rpow_le_rpow_of_exponent_le hY hzb
  calc
    _ ≤ Y ^ b * ‖Gamma (z + 1)‖ * (A * (1 + |z.im|) ^ n) * B := by
      gcongr
      · exact hf z hza hzb
      · exact hg z hza hzb
    _ = (Y ^ b * A * B) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by ring
    _ ≤ (Y ^ b * A * B) * (G / (1 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hgdiv (by positivity)
    _ = _ := by ring

theorem cancelledKernel_strip_bound {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨G, hG, hgamma⟩ := gamma_rapid_bound (a + 1) (b + 1) (by linarith) (n + 2)
  let S : Set ℂ := Icc a b ×ℂ Icc (-1 : ℝ) 1
  have hc : ContinuousOn (cancelledKernel f g Y) S := by
    intro z hz
    exact (cancelledKernel_differentiableAt hf hg hY0
      (ha.trans_le hz.1.1)).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖cancelledKernel f g Y z‖) S :=
    (continuous_const.add (continuous_im.pow 2)).continuousOn.mul hc.norm
  obtain ⟨K, hK⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact S).bddAbove_image hw
  refine ⟨|K| + Y ^ b * G * A * B + 1, by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · apply (cancelledKernel_large_height_bound hf0 hY n hA hB hgamma
      hfbound hgbound hza hzb ht).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [abs_nonneg K]
  · have hzS : z ∈ S := ⟨⟨hza, hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have hb := hK (Set.mem_image_of_mem _ hzS)
    apply (le_div_iff₀ (by positivity : 0 < 1 + z.im ^ 2)).mpr
    have hnonneg : 0 ≤ Y ^ b * G * A * B := by positivity
    nlinarith [le_abs_self K]

lemma tendsto_inv_one_add_sq_atTop (C : ℝ) :
    Tendsto (fun t : ℝ => C * (1 + t ^ 2)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  simpa using (tendsto_inv_atTop_zero.comp h).const_mul C

lemma tendsto_inv_one_add_sq_atBot (C : ℝ) :
    Tendsto (fun t : ℝ => C * (1 + t ^ 2)⁻¹) atBot (𝓝 0) := by
  have := (tendsto_inv_one_add_sq_atTop C).comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def, neg_sq] using this

theorem cancelledKernel_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (hab : a ≤ b) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    (∫ t : ℝ, cancelledKernel f g Y ((a : ℂ) + t * I)) =
      ∫ t : ℝ, cancelledKernel f g Y ((b : ℂ) + t * I) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨C, _, hbnd⟩ := cancelledKernel_strip_bound hf hg hf0 hY ha n hA hB hfbound hgbound
  refine C3P.C3P_shift (g := fun t => C * (1 + t ^ 2)⁻¹) hab ?_
    (integrable_inv_one_add_sq.const_mul C) (tendsto_inv_one_add_sq_atTop C)
    (tendsto_inv_one_add_sq_atBot C) ?_
  · intro z hz
    exact (cancelledKernel_differentiableAt hf hg hY0
      (ha.trans_le hz.1)).differentiableWithinAt
  · intro s h1 h2
    have := hbnd s h1 h2
    rwa [div_eq_mul_inv] at this

theorem literal_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y A B : ℝ}
    (hY : 1 ≤ Y) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) :
    (∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ) + t * I) := by
  have h := cancelledKernel_contour_shift hf hg hf0 hY (by norm_num : (-1 : ℝ) < -(1/4))
    (by norm_num : (-(1/4) : ℝ) ≤ 2) n hA hB hfbound hgbound
  have he (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      cancelledKernel f g Y ((x : ℂ) + t * I) = literalKernel f g Y ((x : ℂ) + t * I) := by
    apply cancelledKernel_eq_literal hf0
    intro hz
    apply hx
    simpa using congrArg Complex.re hz
  simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one] at h
  have h2 (t : ℝ) := he 2 (by norm_num) t
  have hq (t : ℝ) := he (-(1/4)) (by norm_num) t
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one] at h2 hq
  simpa only [h2, hq] using h.symm

theorem gamma_negative_quarter_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ t : ℝ,
      (1 + t ^ 2) * (1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ ≤ G := by
  obtain ⟨C, hC, hgamma⟩ := gamma_rapid_bound (3/4) (3/4) (by norm_num) (n + 2)
  refine ⟨4 * C, by positivity, ?_⟩
  intro t
  let z : ℂ := (-(1/4) : ℂ) + t * I
  have hzre : z.re = -(1/4) := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzre
  have hn : (1/4 : ℝ) ≤ ‖z‖ := by
    simpa only [hzre, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1/4)] using
      Complex.abs_re_le_norm z
  have hΓ : ‖Gamma z‖ ≤ 4 * ‖Gamma (z + 1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    nlinarith [norm_nonneg (Gamma z)]
  have hbound := hgamma (z + 1) (by norm_num [hzre]) (by norm_num [hzre])
  simp only [add_im, one_im, add_zero, hzim] at hbound
  have hp : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  change (1 + t ^ 2) * (1 + |t|) ^ n * ‖Gamma z‖ ≤ 4 * C
  calc
    _ ≤ (1 + |t|) ^ 2 * (1 + |t|) ^ n * (4 * ‖Gamma (z + 1)‖) := by gcongr
    _ = 4 * ((1 + |t|) ^ (n + 2) * ‖Gamma (z + 1)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem literal_shifted_integral_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      0 < Y → 0 ≤ A → 0 ≤ B →
      (∀ t : ℝ, ‖f ((-(1/4) : ℂ) + t * I)‖ ≤ A * (1 + |t|) ^ n) →
      (∀ t : ℝ, ‖g ((-(1/4) : ℂ) + t * I)‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ) + t * I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G, hG, hgamma⟩ := gamma_negative_quarter_bound n
  refine ⟨G, hG, ?_⟩
  intro f g Y A B hY hA hB hf hg
  have hbound (t : ℝ) :
      ‖literalKernel f g Y ((-(1/4) : ℂ) + t * I)‖ ≤
        (G * A * B * Y ^ (-(1/4 : ℝ))) * (1 + t ^ 2)⁻¹ := by
    have hga : (1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ ≤ G / (1 + t ^ 2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hgamma t])
    rw [literalKernel_norm f g hY]
    have hzre : (((-(1/4) : ℂ) + t * I).re) = (-(1/4) : ℝ) := by norm_num
    rw [hzre]
    calc
      _ ≤ Y ^ (-(1/4 : ℝ)) * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ * (A * (1 + |t|) ^ n) * B := by
        gcongr; exact hf t; exact hg t
      _ = (A * B * Y ^ (-(1/4 : ℝ))) * ((1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖) := by
        ring
      _ ≤ (A * B * Y ^ (-(1/4 : ℝ))) * (G / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hga (by positivity)
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (G * A * B * Y ^ (-(1/4 : ℝ)))) (ae_of_all _ hbound)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  convert hint using 1; ring

theorem literal_detector_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      Differentiable ℂ f → Differentiable ℂ g → f 0 = 0 →
      1 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A * (1 + |z.im|) ^ n) →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G, hG, hbound⟩ := literal_shifted_integral_bound n
  refine ⟨G, hG, ?_⟩
  intro f g Y A B hf hg hf0 hY hA hB hfb hgb
  rw [literal_contour_shift hf hg hf0 hY n hA hB hfb hgb]
  apply hbound f g Y A B (by linarith) hA hB
  · intro t; simpa using hfb ((-(1/4) : ℂ) + t * I) (by norm_num) (by norm_num)
  · intro t; exact hgb _ (by norm_num) (by norm_num)

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

lemma absNorm_le_of_dvd {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (h : J ∣ I) :
    Ideal.absNorm J ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (absNorm_pos hI) (map_dvd Ideal.absNorm h)

/-- The divisors of `I`. -/
noncomputable def idealDivisors (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  by classical exact (idealsUpTo F (Ideal.absNorm I)).filter (fun J => J ∣ I)

lemma mem_idealDivisors {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) : J ∈ idealDivisors I ↔ J ∣ I := by
  classical
  simp only [idealDivisors, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨fun hJ => hI ?_, by exact_mod_cast absNorm_le_of_dvd hI h⟩, h⟩
    rw [hJ] at h
    exact zero_dvd_iff.1 (by simpa using h)

/-- The prime support of `I`. -/
noncomputable def primeSupport (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  by classical exact (normalizedFactors I).toFinset

theorem support_prime {I P : Ideal (𝓞 F)} (hP : P ∈ primeSupport I) : Prime P := by
  classical
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {S : Finset (Ideal (𝓞 F))}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  classical
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal (𝓞 F)}
    {S T : Finset (Ideal (𝓞 F))} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  classical
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal (𝓞 F)} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  classical
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  classical
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  classical
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := Multiset.toFinset_eq_empty.mp h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_subset_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

theorem sum_moebius_divisors (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  classical
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card :=
      Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    rw [heq, sum_subset_sign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

/-- `∑_{J ∣ I} |μ(J)| ≤ 2^{ω(I)}`. -/
theorem sum_abs_moebius_le (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ J ∈ s, J ∣ I) :
    (∑ J ∈ s, ‖(moebius J : ℂ)‖) ≤ 2 ^ (primeSupport I).card := by
  classical
  have h1 : (∑ J ∈ s, ‖(moebius J : ℂ)‖) ≤ ∑ J ∈ idealDivisors I, ‖(moebius J : ℂ)‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun J hJ => (mem_idealDivisors hI).2 (hs J hJ))
      (fun _ _ _ => norm_nonneg _)
  have h2 : (∑ J ∈ idealDivisors I, ‖(moebius J : ℂ)‖) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, ‖(moebius J : ℂ)‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero, norm_zero]
  have h3 : (∑ J ∈ (idealDivisors I).filter Squarefree, ‖(moebius J : ℂ)‖) ≤
      ((idealDivisors I).filter Squarefree).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun J hJ => ?_
    have hJ' := (Finset.mem_filter.1 hJ).2
    rw [hJ'.moebius_eq]
    simp
  have h4 : ((idealDivisors I).filter Squarefree).card ≤ 2 ^ (primeSupport I).card := by
    rw [squarefree_divisors_eq_image I hI]
    exact Finset.card_image_le.trans (by rw [Finset.card_powerset])
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ _ := by exact_mod_cast h4

/-- `∏_{P ∈ supp I} q_P ≤ q_I`. -/
lemma prod_support_norm_le (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ∏ P ∈ primeSupport I, Ideal.absNorm P ≤ Ideal.absNorm I := by
  rw [← map_prod]
  exact absNorm_le_of_dvd hI (support_product_dvd hI subset_rfl)

/-- `2^{ω(I)} ≪_δ q_I^δ`. -/
theorem two_pow_card_support_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ δ := by
  classical
  set R : ℝ := 2 ^ (1 / δ)
  set small := idealsUpTo F R
  refine ⟨2 ^ small.card, by positivity, fun I hI => ?_⟩
  have hsplit : (2 : ℝ) ^ (primeSupport I).card = ∏ P ∈ primeSupport I, (2 : ℝ) := by simp
  have hP : ∀ P ∈ primeSupport I, (2 : ℝ) ≤ (if P ∈ small then 2 else 1) *
      (Ideal.absNorm P : ℝ) ^ δ := by
    intro P hP
    have hP0 : P ≠ ⊥ := (support_prime hP).ne_zero
    have hq : (1 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast absNorm_pos hP0
    split_ifs with hs
    · have : 1 ≤ (Ideal.absNorm P : ℝ) ^ δ := Real.one_le_rpow hq hδ.le
      linarith
    · rw [mem_idealsUpTo] at hs
      push Not at hs
      have hR := hs hP0
      have : (2 : ℝ) = R ^ δ := by
        rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      rw [one_mul, this]
      exact Real.rpow_le_rpow (by positivity) hR.le hδ.le
  calc (2 : ℝ) ^ (primeSupport I).card = ∏ P ∈ primeSupport I, (2 : ℝ) := hsplit
    _ ≤ ∏ P ∈ primeSupport I, ((if P ∈ small then 2 else 1) * (Ideal.absNorm P : ℝ) ^ δ) :=
        Finset.prod_le_prod (fun _ _ => by norm_num) hP
    _ = (∏ P ∈ primeSupport I, (if P ∈ small then (2 : ℝ) else 1)) *
        ∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ δ := Finset.prod_mul_distrib
    _ ≤ 2 ^ small.card * (Ideal.absNorm I : ℝ) ^ δ := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          apply pow_le_pow_right₀ (by norm_num)
          apply Finset.card_le_card
          intro P hP; exact (Finset.mem_filter.1 hP).2
        · rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
          apply Real.rpow_le_rpow (by positivity) _ hδ.le
          exact_mod_cast prod_support_norm_le I hI

open Classical in
/-- The mollified coefficients `α_X(n) = ∑_{d ∣ n, q_d ≤ X} μ(d)` of (8.5). -/
noncomputable def alpha (F : Type*) [Field F] [NumberField F] (X : ℝ) (n : Ideal (𝓞 F)) : ℂ :=
  ∑ d ∈ (idealsUpTo F X).filter (fun d => d ∣ n), (moebius d : ℂ)

lemma alpha_eq_of_le {X : ℝ} {n : Ideal (𝓞 F)} (hn : n ≠ ⊥) (hX : (Ideal.absNorm n : ℝ) ≤ X) :
    alpha F X n = if n = ⊤ then 1 else 0 := by
  classical
  rw [← sum_moebius_divisors n hn, alpha]
  congr 1
  ext d
  simp only [Finset.mem_filter, mem_idealsUpTo, mem_idealDivisors hn]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨fun hd => hn ?_, le_trans (by exact_mod_cast absNorm_le_of_dvd hn h) hX⟩, h⟩
    rw [hd] at h; exact zero_dvd_iff.1 (by simpa using h)

lemma norm_alpha_le (X : ℝ) {n : Ideal (𝓞 F)} (hn : n ≠ ⊥) :
    ‖alpha F X n‖ ≤ 2 ^ (primeSupport n).card := by
  classical
  refine (norm_sum_le _ _).trans ?_
  exact sum_abs_moebius_le n hn _ (fun d hd => (Finset.mem_filter.1 hd).2)

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
/-! # L3Z_Det: the detector identity (8.6)–(8.7) for one row

For a completely multiplicative `a` on the ideals with `‖a‖ ≤ 1`, `a ⊥ = 0`, whose Dirichlet
series continues to an entire `Λ` of polynomial growth `‖Λ s‖ ≤ B (2 + |Im s|)^A` on
`.003 ≤ Re s ≤ 4`, and a zero `ρ₀` of `Λ` with `.996 ≤ Re ρ₀ ≤ 1`:

`∑_{(d, I)} μ(d) a(I d) q_{Id}^{-ρ₀} e^{-q_{Id}/Y} = S` with `‖S‖ ≤ G B (2 + |Im ρ₀|)^{|A|} #D Y^{-1/4}`,

the sum over `d ∈ D = idealsUpTo X` (the mollifier `M(s) = ∑_D μ(d) a(d) q_d^{-s}`) and all
ideals `I`. `G` depends only on `A`. -/

open NumberField Complex MeasureTheory Filter Topology Set UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F]

lemma norm_moebius_le (d : Ideal (𝓞 F)) : ‖(moebius d : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree d
  · rw [h.moebius_eq]; simp
  · rw [moebius_of_not_squarefree h]; simp

/-- The mollifier `M_X(s) = ∑_{q_d ≤ X} μ(d) a(d) q_d^{-s}`. -/
noncomputable def mollifier (F : Type*) [Field F] [NumberField F] (a : Ideal (𝓞 F) → ℂ) (X : ℝ)
    (s : ℂ) : ℂ :=
  ∑ d ∈ idealsUpTo F X, (moebius d : ℂ) * a d * (Ideal.absNorm d : ℂ) ^ (-s)

lemma mollifier_entire (a : Ideal (𝓞 F) → ℂ) (X : ℝ) : Differentiable ℂ (mollifier F a X) := by
  intro s
  unfold mollifier
  refine DifferentiableAt.fun_sum fun d hd => ?_
  have hd0 : (Ideal.absNorm d : ℂ) ≠ 0 := by
    exact_mod_cast (absNorm_pos (mem_idealsUpTo.1 hd).1).ne'
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hd0))

lemma norm_mollifier_le {a : Ideal (𝓞 F) → ℂ} (ha : ∀ I, ‖a I‖ ≤ 1) (X : ℝ) {s : ℂ}
    (hs : 0 ≤ s.re) : ‖mollifier F a X s‖ ≤ (idealsUpTo F X).card := by
  unfold mollifier
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hq : (1 : ℝ) ≤ Ideal.absNorm d := by exact_mod_cast absNorm_pos (mem_idealsUpTo.1 hd).1
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (absNorm_pos (mem_idealsUpTo.1 hd).1)]
  have h1 : ‖(moebius d : ℂ)‖ ≤ 1 := norm_moebius_le d
  have h2 : (Ideal.absNorm d : ℝ) ^ (-s).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (by simp; linarith)
  have := mul_le_mul (mul_le_mul h1 (ha d) (norm_nonneg _) zero_le_one) h2 (by positivity)
    (by norm_num)
  simpa using this

/-- The product of the series and the mollifier, as a double series. -/
lemma lseries_mul_mollifier {a : Ideal (𝓞 F) → ℂ} (hmul : ∀ I J, a (I * J) = a I * a J)
    (ha : ∀ I, ‖a I‖ ≤ 1) (ha0 : a ⊥ = 0) (X : ℝ) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    (∑' I : Ideal (𝓞 F), a I * (Ideal.absNorm I : ℂ) ^ (-s)) * mollifier F a X s =
      ∑' p : ↥(idealsUpTo F X) × Ideal (𝓞 F),
        (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F))) *
          (Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℂ) ^ (-s) := by
  have hsum := T12B.summable_absNorm_rpow (F := F) hσ
  have hterm : ∀ I : Ideal (𝓞 F), ‖a I * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤
      ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := fun I => norm_term_le ha0 ha hs I
  have hS : Summable fun I : Ideal (𝓞 F) => a I * (Ideal.absNorm I : ℂ) ^ (-s) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum).of_norm
  set f : ↥(idealsUpTo F X) × Ideal (𝓞 F) → ℂ := fun p =>
    (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F))) * (Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℂ) ^ (-s)
  have hf : ∀ p : ↥(idealsUpTo F X) × Ideal (𝓞 F), f p =
      ((moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a p.1 * (Ideal.absNorm (p.1 : Ideal (𝓞 F)) : ℂ) ^ (-s)) *
        (a p.2 * (Ideal.absNorm p.2 : ℂ) ^ (-s)) := by
    intro p
    simp only [f, hmul, map_mul, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have hfs : Summable f := by
    have hn : Summable fun p : ↥(idealsUpTo F X) × Ideal (𝓞 F) =>
        ‖(moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a p.1 *
          (Ideal.absNorm (p.1 : Ideal (𝓞 F)) : ℂ) ^ (-s)‖ *
          ‖a p.2 * (Ideal.absNorm p.2 : ℂ) ^ (-s)‖ :=
      Summable.mul_of_nonneg
        (f := fun d : ↥(idealsUpTo F X) => ‖(moebius (d : Ideal (𝓞 F)) : ℂ) * a d *
          (Ideal.absNorm (d : Ideal (𝓞 F)) : ℂ) ^ (-s)‖)
        (g := fun I : Ideal (𝓞 F) => ‖a I * (Ideal.absNorm I : ℂ) ^ (-s)‖)
        (Summable.of_finite)
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine Summable.of_norm (hn.congr fun p => ?_)
    simp only [hf, norm_mul]
  rw [hfs.tsum_prod' (fun b => by
    have : (fun c => f (b, c)) = fun c => ((moebius (b : Ideal (𝓞 F)) : ℂ) * a b *
        (Ideal.absNorm (b : Ideal (𝓞 F)) : ℂ) ^ (-s)) * (a c * (Ideal.absNorm c : ℂ) ^ (-s)) :=
      funext fun c => hf (b, c)
    rw [this]; exact hS.mul_left _)]
  rw [tsum_fintype (fun b : ↥(idealsUpTo F X) => ∑' c, f (b, c))]
  have : ∀ b : ↥(idealsUpTo F X), ∑' c, f (b, c) =
      ((moebius (b : Ideal (𝓞 F)) : ℂ) * a b * (Ideal.absNorm (b : Ideal (𝓞 F)) : ℂ) ^ (-s)) *
        ∑' c : Ideal (𝓞 F), a c * (Ideal.absNorm c : ℂ) ^ (-s) := by
    intro b
    rw [← tsum_mul_left]
    exact tsum_congr fun c => hf (b, c)
  rw [Finset.sum_congr rfl fun b _ => this b, ← Finset.sum_mul, mul_comm, mollifier]
  congr 1
  exact (Finset.sum_coe_sort (idealsUpTo F X)
    (fun d => (moebius d : ℂ) * a d * (Ideal.absNorm d : ℂ) ^ (-s))).symm

/-- `(2 + y)^A ≤ (2 + Y)^|A|` for `0 ≤ y ≤ Y`. -/
lemma two_add_rpow_le_abs {A y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    (2 + y) ^ A ≤ (2 + Y) ^ |A| := by
  rcases le_or_gt 0 A with hA | hA
  · rw [abs_of_nonneg hA]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hA
  · have h1 : (2 + y) ^ A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hA.le
    have h2 : 1 ≤ (2 + Y) ^ |A| := Real.one_le_rpow (by linarith) (abs_nonneg A)
    linarith

/-- **The detector bound** (8.6)–(8.7) for one row. -/
theorem detector_bound (A : ℝ) : ∃ G : ℝ, 0 < G ∧ ∀ (a : Ideal (𝓞 F) → ℂ),
    (∀ I J, a (I * J) = a I * a J) → (∀ I, ‖a I‖ ≤ 1) → a ⊥ = 0 →
    ∀ Λ : ℂ → ℂ, Differentiable ℂ Λ →
    (∀ s : ℂ, 1 < s.re → Λ s = ∑' I : Ideal (𝓞 F), a I * (Ideal.absNorm I : ℂ) ^ (-s)) →
    ∀ B : ℝ, 0 ≤ B → (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 → ‖Λ s‖ ≤ B * (2 + |s.im|) ^ A) →
    ∀ ρ₀ : ℂ, 996 / 1000 ≤ ρ₀.re → ρ₀.re ≤ 1 → Λ ρ₀ = 0 → ∀ X Y : ℝ, 1 ≤ Y →
    ∃ S : ℂ, HasSum (fun p : ↥(idealsUpTo F X) × Ideal (𝓞 F) =>
        (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F))) *
          (((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ)) : ℂ) ^ (-ρ₀) *
          Complex.exp (-(((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ)) : ℂ) / (Y : ℂ))) S ∧
      ‖S‖ ≤ G * B * (2 + |ρ₀.im|) ^ |A| * (idealsUpTo F X).card * Y ^ (-(1 / 4 : ℝ)) := by
  set n : ℕ := ⌈|A|⌉₊
  obtain ⟨G, hG, hdet⟩ := literal_detector_bound n
  refine ⟨G, hG, fun a hmul ha ha0 Λ hΛd hΛe B hB hΛb ρ₀ h1 h2 hz X Y hY => ?_⟩
  set f : ℂ → ℂ := fun z => Λ (ρ₀ + z)
  set g : ℂ → ℂ := fun z => mollifier F a X (ρ₀ + z)
  have hfd : Differentiable ℂ f := hΛd.comp ((differentiable_const ρ₀).add differentiable_id)
  have hgd : Differentiable ℂ g :=
    (mollifier_entire a X).comp ((differentiable_const ρ₀).add differentiable_id)
  have hf0 : f 0 = 0 := by simp [f, hz]
  set c : ↥(idealsUpTo F X) × Ideal (𝓞 F) → ℂ := fun p =>
    (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F)))
  set N : ↥(idealsUpTo F X) × Ideal (𝓞 F) → ℝ := fun p =>
    ((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℕ) : ℝ)
  have hN0 : ∀ p, 0 ≤ N p := fun p => Nat.cast_nonneg _
  have hNz : ∀ p, N p = 0 → c p = 0 := by
    intro p hp
    simp only [N, Nat.cast_eq_zero] at hp
    have : p.2 * (p.1 : Ideal (𝓞 F)) = ⊥ := Ideal.absNorm_eq_zero_iff.1 hp
    simp [c, this, ha0]
  have hYpos : (0 : ℝ) < Y := by linarith
  have hsum : Summable fun p => ‖c p‖ * (N p) ^ (-(ρ₀.re + 2)) := by
    have hσ : (1 : ℝ) < ρ₀.re + 2 := by linarith
    have hs := T12B.summable_absNorm_rpow (F := F) hσ
    have hprod : Summable fun p : ↥(idealsUpTo F X) × Ideal (𝓞 F) =>
        ((Ideal.absNorm (p.1 : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-(ρ₀.re + 2)) *
          ((Ideal.absNorm p.2 : ℕ) : ℝ) ^ (-(ρ₀.re + 2)) :=
      Summable.mul_of_nonneg
        (f := fun d : ↥(idealsUpTo F X) => ((Ideal.absNorm (d : Ideal (𝓞 F)) : ℕ) : ℝ) ^
          (-(ρ₀.re + 2)))
        (g := fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(ρ₀.re + 2)))
        Summable.of_finite hs (fun _ => by positivity) (fun _ => by positivity)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hprod
    have hc : ‖c p‖ ≤ 1 := by
      simp only [c, norm_mul]
      exact mul_le_one₀ (norm_moebius_le _) (norm_nonneg _) (ha _)
    have hNe : N p ^ (-(ρ₀.re + 2)) = ((Ideal.absNorm (p.1 : Ideal (𝓞 F)) : ℕ) : ℝ) ^
        (-(ρ₀.re + 2)) * ((Ideal.absNorm p.2 : ℕ) : ℝ) ^ (-(ρ₀.re + 2)) := by
      simp only [N, map_mul, Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity), mul_comm]
    rw [hNe]
    exact mul_le_of_le_one_left (by positivity) hc
  have hexp := gamma_expansion c N hN0 hNz ρ₀ hYpos hsum
  -- the integrand is the literal kernel
  have hint : ∀ t : ℝ, ∑' p, gammaTerm (c p) (N p) ρ₀ Y t =
      literalKernel f g Y ((2 : ℂ) + t * I) := by
    intro t
    have hv : (ρ₀ + line t).re = ρ₀.re + 2 := by simp
    have hre : (1 : ℝ) < (ρ₀ + line t).re := by rw [hv]; linarith
    have hprod := lseries_mul_mollifier hmul ha ha0 X (by linarith : (1 : ℝ) < 29 / 10)
      (s := ρ₀ + line t) (by rw [hv]; linarith)
    rw [← hΛe _ hre] at hprod
    unfold gammaTerm
    have hcast : ∀ p : ↥(idealsUpTo F X) × Ideal (𝓞 F),
        c p * ((N p : ℝ) : ℂ) ^ (-(ρ₀ + line t)) =
        (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F))) *
          (Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℂ) ^ (-(ρ₀ + line t)) := by
      intro p; simp [c, N]
    have : (∑' p, (Y : ℂ) ^ line t * Gamma (line t) * c p * ((N p : ℝ) : ℂ) ^ (-(ρ₀ + line t))) =
        (Y : ℂ) ^ line t * Gamma (line t) * ∑' p, c p * ((N p : ℝ) : ℂ) ^ (-(ρ₀ + line t)) := by
      rw [← tsum_mul_left]; congr 1; funext p; ring
    rw [this, tsum_congr hcast, ← hprod]
    simp only [literalKernel, f, g, line]
    ring
  have hfb : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 →
      ‖f z‖ ≤ (B * (2 + |ρ₀.im|) ^ |A|) * (1 + |z.im|) ^ n := by
    intro z hz1 hz2
    have hb := hΛb (ρ₀ + z) (by simp; linarith) (by simp; linarith)
    have him : |(ρ₀ + z).im| ≤ |ρ₀.im| + |z.im| := by simpa using abs_add_le ρ₀.im z.im
    have e1 : (2 + |(ρ₀ + z).im|) ^ A ≤ (2 + (|ρ₀.im| + |z.im|)) ^ |A| :=
      two_add_rpow_le_abs (abs_nonneg _) him
    have e2 : (2 + (|ρ₀.im| + |z.im|)) ^ |A| ≤ ((2 + |ρ₀.im|) * (1 + |z.im|)) ^ |A| :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg ρ₀.im, abs_nonneg z.im])
        (abs_nonneg A)
    have e3 : (1 + |z.im|) ^ |A| ≤ (1 + |z.im|) ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (Nat.le_ceil _)
    rw [Real.mul_rpow (by positivity) (by positivity)] at e2
    calc ‖f z‖ ≤ B * (2 + |(ρ₀ + z).im|) ^ A := hb
      _ ≤ B * ((2 + |ρ₀.im|) ^ |A| * (1 + |z.im|) ^ |A|) := by gcongr; exact e1.trans e2
      _ ≤ B * ((2 + |ρ₀.im|) ^ |A| * (1 + |z.im|) ^ n) := by gcongr
      _ = _ := by ring
  have hgb : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ (idealsUpTo F X).card := by
    intro z hz1 _
    exact norm_mollifier_le ha X (by simp; linarith)
  have hbound := hdet f g Y _ _ hfd hgd hf0 hY (by positivity) (by positivity) hfb hgb
  refine ⟨((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, ∑' p, gammaTerm (c p) (N p) ρ₀ Y t, ?_, ?_⟩
  · exact hexp
  · rw [show (∫ t : ℝ, ∑' p, gammaTerm (c p) (N p) ρ₀ Y t) =
        ∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I) from integral_congr_ae (ae_of_all _ hint)]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hpi := Real.pi_pos
    calc (2 * Real.pi)⁻¹ * ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)‖
        ≤ (2 * Real.pi)⁻¹ * (Real.pi * G * (B * (2 + |ρ₀.im|) ^ |A|) *
          (idealsUpTo F X).card * Y ^ (-(1/4 : ℝ))) := by gcongr
      _ = (1 / 2) * (G * B * (2 + |ρ₀.im|) ^ |A| * (idealsUpTo F X).card *
          Y ^ (-(1 / 4 : ℝ))) := by field_simp
      _ ≤ _ := by
          have : 0 ≤ G * B * (2 + |ρ₀.im|) ^ |A| * (idealsUpTo F X).card *
            Y ^ (-(1 / 4 : ℝ)) := by positivity
          linarith

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Lower: the lower bound for the detected sum (p. 54)

From the double series of `L3Z_Det` (index `(d, I)`, `d ∈ idealsUpTo X`):

* the terms with `q_{Id} > Z` are `≤ 6 Y³ Z^{-2.8} ζ_F(1.196)²` in total
  (`e^{-x} ≤ 6 x^{-3}`);
* the others regroup by `n = I d` into `∑_{q_n ≤ Z} a(n) α_X(n) q_n^{-ρ₀} e^{-q_n/Y}`;
* the unit term is `e^{-1/Y}` and the terms with `1 < q_n ≤ X` vanish (8.5).

Hence `‖∑_{X < q_n ≤ Z} a(n) α_X(n) q_n^{-ρ₀} e^{-q_n/Y}‖ ≥ e^{-1/Y} − ‖S‖ − 6Y³Z^{-2.8}ζ²`. -/

open NumberField Complex Filter Topology Set UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] Classical.propDecidable

/-- `ζ_F(σ)` as a real series. -/
noncomputable def zetaR (F : Type*) [Field F] [NumberField F] (σ : ℝ) : ℝ :=
  ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)

/-- The detected term `a(n) α_X(n) q_n^{-ρ} e^{-q_n/Y}`. -/
noncomputable def detTerm (F : Type*) [Field F] [NumberField F] (a : Ideal (𝓞 F) → ℂ) (X Y : ℝ)
    (ρ : ℂ) (n : Ideal (𝓞 F)) : ℂ :=
  a n * alpha F X n * (((Ideal.absNorm n : ℕ) : ℝ) : ℂ) ^ (-ρ) *
    Complex.exp (-(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ))

lemma exp_neg_le_six_div {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 6 / x ^ 3 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 3
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos x) (by positivity)]
  rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num [Nat.factorial]] at h
  rw [inv_div]; exact h

/-- The tail bound for one term. -/
lemma norm_pairTerm_le {a : Ideal (𝓞 F) → ℂ} (ha : ∀ I, ‖a I‖ ≤ 1) {ρ₀ : ℂ}
    (h1 : 996 / 1000 ≤ ρ₀.re) {Y Z : ℝ} (hY : 0 < Y) (hZ : 0 < Z) (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (n : Ideal (𝓞 F)) (hn : Z < Ideal.absNorm n) :
    ‖μ * a n * (((Ideal.absNorm n : ℕ) : ℝ) : ℂ) ^ (-ρ₀) *
        Complex.exp (-(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ))‖ ≤
      6 * Y ^ 3 * Z ^ (-(28 / 10 : ℝ)) * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)) := by
  set q : ℝ := ((Ideal.absNorm n : ℕ) : ℝ)
  have hq : 0 < q := hZ.trans hn
  have hq1 : 1 ≤ q := by
    have h0 : 0 < Ideal.absNorm n := by
      have : (0 : ℝ) < (Ideal.absNorm n : ℝ) := hq
      exact_mod_cast this
    have h1 : 1 ≤ Ideal.absNorm n := h0
    show (1 : ℝ) ≤ ((Ideal.absNorm n : ℕ) : ℝ)
    exact_mod_cast h1
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.norm_exp]
  have hre : (-(q : ℂ) / (Y : ℂ)).re = -(q / Y) := by
    rw [show -(q : ℂ) / (Y : ℂ) = ((-(q / Y) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [hre]
  have he : Real.exp (-(q / Y)) ≤ 6 / (q / Y) ^ 3 := exp_neg_le_six_div (by positivity)
  have hp : q ^ (-ρ₀).re ≤ q ^ (-(996 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by simp; linarith)
  have hma : ‖μ‖ * ‖a n‖ ≤ 1 := mul_le_one₀ hμ (norm_nonneg _) (ha n)
  calc ‖μ‖ * ‖a n‖ * q ^ (-ρ₀).re * Real.exp (-(q / Y))
      ≤ 1 * q ^ (-(996 / 1000 : ℝ)) * (6 / (q / Y) ^ 3) :=
        mul_le_mul (mul_le_mul hma hp (by positivity) zero_le_one) he (by positivity)
          (by positivity)
    _ = 6 * Y ^ 3 * (q ^ (-(996 / 1000 : ℝ)) * (q ^ 3)⁻¹) := by field_simp
    _ = 6 * Y ^ 3 * (q ^ (-(28 / 10 : ℝ)) * q ^ (-(1196 / 1000 : ℝ))) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_neg hq.le, ← Real.rpow_add hq, ← Real.rpow_add hq]
        norm_num
    _ ≤ 6 * Y ^ 3 * (Z ^ (-(28 / 10 : ℝ)) * q ^ (-(1196 / 1000 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hZ hn.le (by norm_num)) (by positivity)
    _ = _ := by ring

theorem lower_bound {a : Ideal (𝓞 F) → ℂ} (hmul : ∀ I J, a (I * J) = a I * a J)
    (ha : ∀ I, ‖a I‖ ≤ 1) (ha0 : a ⊥ = 0) (ha1 : a ⊤ = 1) {ρ₀ : ℂ} (h1 : 996 / 1000 ≤ ρ₀.re)
    {X Y Z : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z) (hY : 0 < Y) {S : ℂ}
    (hS : HasSum (fun p : ↥(idealsUpTo F X) × Ideal (𝓞 F) =>
        (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F))) *
          (((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ)) : ℂ) ^ (-ρ₀) *
          Complex.exp (-(((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ)) : ℂ) / (Y : ℂ))) S) :
    Real.exp (-1 / Y) - ‖S‖ - 6 * Y ^ 3 * Z ^ (-(28 / 10 : ℝ)) * zetaR F (1196 / 1000) ^ 2 ≤
      ‖∑ n ∈ (idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ)),
        detTerm F a X Y ρ₀ n‖ := by
  have hZ : 0 < Z := by linarith
  set D := idealsUpTo F X
  set f : ↥D × Ideal (𝓞 F) → ℂ := fun p =>
    (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * a (p.2 * (p.1 : Ideal (𝓞 F))) *
      (((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ)) : ℂ) ^ (-ρ₀) *
      Complex.exp (-(((Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ)) : ℂ) / (Y : ℂ)) with hf
  set P : Finset (↥D × Ideal (𝓞 F)) := (Finset.univ ×ˢ idealsUpTo F Z).filter
    (fun p => (Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) : ℝ) ≤ Z) with hP
  -- A: split
  have hfin : HasSum (fun p => if p ∈ P then f p else 0) (∑ p ∈ P, f p) := by
    have : HasSum (fun p => if p ∈ P then f p else 0) (∑ b ∈ P, if b ∈ P then f b else 0) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    rwa [Finset.sum_congr rfl (fun p hp => if_pos hp)] at this
  have htail : HasSum (fun p => if p ∈ P then 0 else f p) (S - ∑ p ∈ P, f p) := by
    have := hS.sub hfin
    have e : (fun p => if p ∈ P then 0 else f p) = fun b => f b - if b ∈ P then f b else 0 := by
      funext p; split_ifs <;> simp
    rw [e]; exact this
  -- B: pointwise tail bound
  set K : ℝ := 6 * Y ^ 3 * Z ^ (-(28 / 10 : ℝ)) with hK
  set w : ↥D × Ideal (𝓞 F) → ℝ := fun p =>
    ((Ideal.absNorm (p.1 : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)) *
      ((Ideal.absNorm p.2 : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ))
  have hσ : (1 : ℝ) < 1196 / 1000 := by norm_num
  have hζ := T12B.summable_absNorm_rpow (F := F) hσ
  have hws : Summable w :=
    Summable.mul_of_nonneg
      (f := fun d : ↥D => ((Ideal.absNorm (d : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)))
      (g := fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)))
      Summable.of_finite hζ (fun _ => by positivity) (fun _ => by positivity)
  have hb : ∀ p, ‖(if p ∈ P then 0 else f p)‖ ≤ K * w p := by
    intro p
    have hKw : 0 ≤ K * w p := by positivity
    split_ifs with hp
    · simpa using hKw
    by_cases h2 : p.2 = ⊥
    · have : f p = 0 := by simp [hf, h2, ha0]
      rw [this, norm_zero]; exact hKw
    have hd0 : (p.1 : Ideal (𝓞 F)) ≠ ⊥ := (mem_idealsUpTo.1 p.1.2).1
    have hn0 : p.2 * (p.1 : Ideal (𝓞 F)) ≠ ⊥ := mul_ne_zero h2 hd0
    have hgt : Z < Ideal.absNorm (p.2 * (p.1 : Ideal (𝓞 F))) := by
      by_contra hle
      push Not at hle
      apply hp
      rw [hP, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_univ _, mem_idealsUpTo.2 ⟨h2, ?_⟩⟩, hle⟩
      refine le_trans ?_ hle
      exact_mod_cast absNorm_le_of_dvd hn0 (dvd_mul_right _ _)
    have := norm_pairTerm_le ha h1 hY hZ (moebius (p.1 : Ideal (𝓞 F)) : ℂ)
      (norm_moebius_le _) _ hgt
    refine this.trans (le_of_eq ?_)
    simp only [hK, w, map_mul, Nat.cast_mul]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    ring
  -- C: the tail sum
  have hT : ‖S - ∑ p ∈ P, f p‖ ≤ K * zetaR F (1196 / 1000) ^ 2 := by
    have h := htail.norm_le_of_bounded (hws.hasSum.mul_left K) hb
    refine h.trans ?_
    gcongr
    have hw_eq : ∑' p, w p = (∑' d : ↥D, ((Ideal.absNorm (d : Ideal (𝓞 F)) : ℕ) : ℝ) ^
        (-(1196 / 1000 : ℝ))) * ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^
          (-(1196 / 1000 : ℝ)) :=
      (tsum_mul_tsum_of_summable_norm
        (f := fun d : ↥D => ((Ideal.absNorm (d : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)))
        (g := fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)))
        Summable.of_finite (by simpa only [Real.norm_eq_abs] using hζ.abs)).symm
    rw [hw_eq, sq, zetaR]
    have h0 : 0 ≤ ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)) :=
      tsum_nonneg fun _ => by positivity
    gcongr
    rw [tsum_fintype]
    rw [Finset.sum_coe_sort D (fun d => ((Ideal.absNorm d : ℕ) : ℝ) ^ (-(1196 / 1000 : ℝ)))]
    exact hζ.sum_le_tsum _ (fun _ _ => by positivity)
  -- D: regroup
  have hmaps : ∀ p ∈ P, p.2 * (p.1 : Ideal (𝓞 F)) ∈ idealsUpTo F Z := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_product] at hp
    exact mem_idealsUpTo.2 ⟨mul_ne_zero (mem_idealsUpTo.1 hp.1.2).1 (mem_idealsUpTo.1 p.1.2).1,
      hp.2⟩
  have hregroup : ∑ p ∈ P, f p = ∑ n ∈ idealsUpTo F Z, detTerm F a X Y ρ₀ n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 := (mem_idealsUpTo.1 hn).1
    have hfib : ∀ p ∈ P.filter (fun p => p.2 * (p.1 : Ideal (𝓞 F)) = n),
        f p = (moebius (p.1 : Ideal (𝓞 F)) : ℂ) * (a n * (((Ideal.absNorm n : ℕ) : ℝ) : ℂ) ^ (-ρ₀) *
          Complex.exp (-(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ))) := by
      intro p hp
      have hpn := (Finset.mem_filter.1 hp).2
      simp only [hf, hpn]
      ring
    rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul, detTerm, alpha]
    have hbij : ∑ p ∈ P.filter (fun p => p.2 * (p.1 : Ideal (𝓞 F)) = n),
        (moebius (p.1 : Ideal (𝓞 F)) : ℂ) =
        ∑ d ∈ (idealsUpTo F X).filter (fun d => d ∣ n), (moebius d : ℂ) := by
      refine Finset.sum_bij (fun p _ => (p.1 : Ideal (𝓞 F))) ?_ ?_ ?_ (fun p _ => rfl)
      · intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨p.1.2, ⟨p.2, by rw [← hp.2, mul_comm]⟩⟩
      · intro p hp p' hp' h
        rw [Finset.mem_filter] at hp hp'
        have hd0 : (p.1 : Ideal (𝓞 F)) ≠ ⊥ := (mem_idealsUpTo.1 p.1.2).1
        have h1' : p.1 = p'.1 := Subtype.ext h
        have h2' : p.2 = p'.2 := by
          have : p.2 * (p.1 : Ideal (𝓞 F)) = p'.2 * (p.1 : Ideal (𝓞 F)) := by
            rw [hp.2, h, hp'.2]
          exact mul_right_cancel₀ hd0 this
        exact Prod.ext h1' h2'
      · intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨c, hc⟩ := hd.2
        have hc0 : c ≠ ⊥ := by
          rintro rfl; exact hn0 (by simp [hc])
        refine ⟨(⟨d, hd.1⟩, c), ?_, rfl⟩
        have hcn : c * d = n := by rw [mul_comm]; exact hc.symm
        have hcZ : c ∈ idealsUpTo F Z := by
          refine mem_idealsUpTo.2 ⟨hc0, le_trans ?_ (mem_idealsUpTo.1 hn).2⟩
          exact_mod_cast absNorm_le_of_dvd hn0 (Dvd.intro_left d hc.symm)
        have hnZ : (Ideal.absNorm (c * d) : ℝ) ≤ Z := by
          rw [hcn]; exact (mem_idealsUpTo.1 hn).2
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        exact ⟨⟨hcZ, hnZ⟩, hcn⟩
    rw [hbij]; ring
  -- E: the unit term and the vanishing range
  have htop : ⊤ ∈ (idealsUpTo F Z).filter (fun n => ¬ X < (Ideal.absNorm n : ℝ)) := by
    rw [Finset.mem_filter, mem_idealsUpTo]
    simp only [Ideal.absNorm_top, Nat.cast_one]
    exact ⟨⟨top_ne_bot, by linarith⟩, by linarith⟩
  have hsmall : ∑ n ∈ (idealsUpTo F Z).filter (fun n => ¬ X < (Ideal.absNorm n : ℝ)),
      detTerm F a X Y ρ₀ n = detTerm F a X Y ρ₀ ⊤ := by
    refine Finset.sum_eq_single_of_mem _ htop fun n hn hne => ?_
    rw [Finset.mem_filter, mem_idealsUpTo] at hn
    have hα : alpha F X n = 0 := by
      rw [alpha_eq_of_le hn.1.1 (by push Not at hn; exact hn.2), if_neg hne]
    simp [detTerm, hα]
  have hunit : detTerm F a X Y ρ₀ ⊤ = Complex.exp (-1 / (Y : ℂ)) := by
    have hα : alpha F X ⊤ = 1 := by
      rw [alpha_eq_of_le top_ne_bot (by simp; linarith), if_pos rfl]
    simp [detTerm, hα, ha1]
  have hsplit := Finset.sum_filter_add_sum_filter_not (idealsUpTo F Z)
    (fun n => X < (Ideal.absNorm n : ℝ)) (detTerm F a X Y ρ₀)
  rw [hsmall, hunit, ← hregroup] at hsplit
  set R := ∑ n ∈ (idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ)),
    detTerm F a X Y ρ₀ n
  have hR : Complex.exp (-1 / (Y : ℂ)) = S - (S - ∑ p ∈ P, f p) - R := by
    rw [← hsplit]; ring
  have hnorm : ‖Complex.exp (-1 / (Y : ℂ))‖ = Real.exp (-1 / Y) := by
    rw [Complex.norm_exp]
    congr 1
    rw [show (-1 / (Y : ℂ)) = ((-1 / Y : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have h3 : ‖Complex.exp (-1 / (Y : ℂ))‖ ≤ ‖S‖ + ‖S - ∑ p ∈ P, f p‖ + ‖R‖ := by
    rw [hR]
    exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  rw [hnorm] at h3
  linarith

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Sob: the Sobolev sup bound of p. 54

`sup_{|x| ≤ H} ‖P x‖² ≤ 2 ∫_{-H}^{H} (‖P‖² + ‖P'‖²)` for `H ≥ 1/2` and a `C¹` function `P`;
and the Dirichlet polynomials `dpoly B c L t = ∑_{n ∈ B} c n e^{-i t L n}` with their
derivatives. -/

open Complex MeasureTheory intervalIntegral Set

namespace ArtinPrimitiveRoots

namespace L3Z

theorem sobolev_sup {P P' : ℝ → ℂ} (hd : ∀ t, HasDerivAt P (P' t) t) (hc : Continuous P)
    (hc' : Continuous P') {H : ℝ} (hH : 1 / 2 ≤ H) {x : ℝ} (hx : |x| ≤ H) :
    ‖P x‖ ^ 2 ≤ 2 * ∫ t in (-H)..H, (‖P t‖ ^ 2 + ‖P' t‖ ^ 2) := by
  set g : ℝ → ℝ := fun t => ‖P t‖ ^ 2 + ‖P' t‖ ^ 2 with hg
  have hgc : Continuous g := by fun_prop
  have hg0 : ∀ t, 0 ≤ g t := fun t => by positivity
  set J := ∫ t in (-H)..H, g t
  set h' : ℝ → ℝ := fun t => 2 * inner ℝ (P t) (P' t)
  have hh'c : Continuous h' := by
    have : Continuous fun t => inner ℝ (P t) (P' t) := hc.inner hc'
    exact continuous_const.mul this
  have hh'g : ∀ t, |h' t| ≤ g t := by
    intro t
    have h1 := abs_real_inner_le_norm (P t) (P' t)
    simp only [h', hg, abs_mul, abs_two]
    nlinarith [sq_nonneg (‖P t‖ - ‖P' t‖), norm_nonneg (P t), norm_nonneg (P' t)]
  have hHx : -H ≤ x ∧ x ≤ H := abs_le.1 hx
  have hint_le : ∀ a b, -H ≤ a → a ≤ b → b ≤ H → |∫ t in a..b, h' t| ≤ J := by
    intro a b ha hab hb
    refine (abs_integral_le_integral_abs hab).trans ?_
    refine (integral_mono_on hab (hh'c.abs.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _) fun t _ => hh'g t).trans ?_
    exact integral_mono_interval ha hab hb (Filter.Eventually.of_forall hg0)
      (hgc.intervalIntegrable _ _)
  have hpt : ∀ y, -H ≤ y → y ≤ H → ‖P x‖ ^ 2 ≤ ‖P y‖ ^ 2 + J := by
    intro y hy1 hy2
    have hftc : ∫ t in y..x, h' t = ‖P x‖ ^ 2 - ‖P y‖ ^ 2 :=
      integral_eq_sub_of_hasDerivAt (f := fun t => ‖P t‖ ^ 2) (fun t _ => (hd t).norm_sq)
        (hh'c.intervalIntegrable _ _)
    have : |∫ t in y..x, h' t| ≤ J := by
      rcases le_total y x with hyx | hxy
      · exact hint_le y x hy1 hyx hHx.2
      · rw [integral_symm, abs_neg]; exact hint_le x y hHx.1 hxy hy2
    rw [hftc] at this
    linarith [le_abs_self (‖P x‖ ^ 2 - ‖P y‖ ^ 2)]
  have hHH : -H ≤ H := by linarith
  have hPc : Continuous fun t => ‖P t‖ ^ 2 := by fun_prop
  have hav : ∫ _y in (-H)..H, ‖P x‖ ^ 2 ≤ ∫ y in (-H)..H, (‖P y‖ ^ 2 + J) :=
    integral_mono_on hHH intervalIntegrable_const
      ((hPc.add continuous_const).intervalIntegrable _ _) fun y hy => hpt y hy.1 hy.2
  rw [intervalIntegral.integral_const, integral_add (hPc.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const] at hav
  simp only [sub_neg_eq_add, smul_eq_mul] at hav
  have hPJ : ∫ y in (-H)..H, ‖P y‖ ^ 2 ≤ J :=
    integral_mono_on hHH (hPc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
      fun t _ => by simp only [hg]; nlinarith [sq_nonneg ‖P' t‖]
  have hJ0 : 0 ≤ J := integral_nonneg hHH fun t _ => hg0 t
  have hH0 : 0 < H + H := by linarith
  have : (H + H) * ‖P x‖ ^ 2 ≤ J + (H + H) * J := by linarith
  have h2 : ‖P x‖ ^ 2 ≤ J / (H + H) + J := by
    rw [div_add' _ _ _ hH0.ne', le_div_iff₀ hH0]; linarith
  have h3 : J / (H + H) ≤ J := by
    rw [div_le_iff₀ hH0]; nlinarith
  linarith

/-- `∑_{n ∈ B} c n e^{-i t L n}`. -/
noncomputable def dpoly {ι : Type*} (B : Finset ι) (c : ι → ℂ) (L : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ B, c n * Complex.exp (-((t * L n : ℝ) : ℂ) * I)

lemma dpoly_hasDerivAt {ι : Type*} (B : Finset ι) (c : ι → ℂ) (L : ι → ℝ) (t : ℝ) :
    HasDerivAt (dpoly B c L) (dpoly B (fun n => c n * (-(L n : ℂ) * I)) L t) t := by
  unfold dpoly
  have : ∀ n ∈ B, HasDerivAt (fun t : ℝ => c n * Complex.exp (-((t * L n : ℝ) : ℂ) * I))
      (c n * (-(L n : ℂ) * I) * Complex.exp (-((t * L n : ℝ) : ℂ) * I)) t := by
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => (-((t * L n : ℝ) : ℂ) * I)) (-(L n : ℂ) * I) t := by
      have := ((hasDerivAt_id t).mul_const (L n)).ofReal_comp
      simp only [id, one_mul] at this
      have := (this.neg).mul_const I
      simpa using this
    have h2 := (h1.cexp).const_mul (c n)
    have e : c n * (-(L n : ℂ) * I) * Complex.exp (-((t * L n : ℝ) : ℂ) * I) =
        c n * (Complex.exp (-((t * L n : ℝ) : ℂ) * I) * (-(L n : ℂ) * I)) := by ring
    rw [e]; exact h2
  have := HasDerivAt.fun_sum this
  convert this using 1

lemma dpoly_continuous {ι : Type*} (B : Finset ι) (c : ι → ℂ) (L : ι → ℝ) :
    Continuous (dpoly B c L) := by
  unfold dpoly; fun_prop

lemma norm_dpoly_sq_le {ι : Type*} (B : Finset ι) (c : ι → ℂ) (L : ι → ℝ) {H : ℝ}
    (hH : 1 / 2 ≤ H) {x : ℝ} (hx : |x| ≤ H) :
    ‖dpoly B c L x‖ ^ 2 ≤ 2 * ∫ t in (-H)..H, (‖dpoly B c L t‖ ^ 2 +
      ‖dpoly B (fun n => c n * (-(L n : ℂ) * I)) L t‖ ^ 2) :=
  sobolev_sup (dpoly_hasDerivAt B c L) (dpoly_continuous B c L) (dpoly_continuous _ _ _) hH hx

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Block: removing `β` and `γ` from one dyadic block

On a block `B` with `N < q_n ≤ 2N`, write `q_n^{-(δ + iγ)} = N^{-δ} e^{-δ ℓ_n} e^{-iγ log q_n}`,
`ℓ_n = log(q_n/N) ∈ (0, log 2]`, and expand `e^{-δℓ} = ∑_k (-δℓ)^k/k!`. With
`P_k(t) = ∑_B w(n) ℓ_n^k a(n) e^{-it log q_n}`, a lower bound `c ≤ ‖∑_B a w q^{-(δ+iγ)}‖` for some
`0 ≤ δ ≤ 1/250`, `|γ| ≤ H`, gives (Cauchy–Schwarz in the weighted form `x ≤ 1/(2λ) + λx²/2`)

`c²/2 ≤ ∑_k (1/250)^k/k! · Sob_k`,  `Sob_k = 2∫_{-H}^{H} (‖P_k‖² + ‖P_k'‖²)`,

a quantity independent of `(δ, γ)`. This replaces the prefix-maximal argument of p. 54. -/

open Complex MeasureTheory intervalIntegral Set NumberField

namespace ArtinPrimitiveRoots

namespace L3Z

variable {ι : Type*}

lemma norm_dpoly_le (B : Finset ι) (c : ι → ℂ) (L : ι → ℝ) (t : ℝ) :
    ‖dpoly B c L t‖ ≤ ∑ n ∈ B, ‖c n‖ := by
  unfold dpoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  have : ‖Complex.exp (-((t * L n : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]

/-- The block polynomial `P_k`. -/
noncomputable def blockPoly (B : Finset ι) (w a : ι → ℂ) (ℓ Lg : ι → ℝ) (k : ℕ) : ℝ → ℂ :=
  dpoly B (fun n => w n * ((ℓ n : ℂ) ^ k) * a n) Lg

/-- `Sob_k = 2 ∫_{-H}^{H} (‖P_k‖² + ‖P_k'‖²)`. -/
noncomputable def blockSob (B : Finset ι) (w a : ι → ℂ) (ℓ Lg : ι → ℝ) (H : ℝ) (k : ℕ) : ℝ :=
  2 * ∫ t in (-H)..H, (‖blockPoly B w a ℓ Lg k t‖ ^ 2 +
    ‖dpoly B (fun n => w n * ((ℓ n : ℂ) ^ k) * a n * (-(Lg n : ℂ) * I)) Lg t‖ ^ 2)

lemma blockSob_nonneg (B : Finset ι) (w a : ι → ℂ) (ℓ Lg : ι → ℝ) {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    0 ≤ blockSob B w a ℓ Lg H k := by
  unfold blockSob
  have : 0 ≤ ∫ t in (-H)..H, (‖blockPoly B w a ℓ Lg k t‖ ^ 2 +
      ‖dpoly B (fun n => w n * ((ℓ n : ℂ) ^ k) * a n * (-(Lg n : ℂ) * I)) Lg t‖ ^ 2) :=
    integral_nonneg (by linarith) fun _ _ => by positivity
  linarith

lemma blockSob_le (B : Finset ι) (w a : ι → ℂ) (ℓ Lg : ι → ℝ) (hℓ : ∀ n ∈ B, |ℓ n| ≤ 1)
    {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    blockSob B w a ℓ Lg H k ≤ 2 * ((H + H) * ((∑ n ∈ B, ‖w n * a n‖) ^ 2 +
      (∑ n ∈ B, ‖w n * a n‖ * |Lg n|) ^ 2)) := by
  unfold blockSob
  have hc1 : ∀ n ∈ B, ‖w n * ((ℓ n : ℂ) ^ k) * a n‖ ≤ ‖w n * a n‖ := by
    intro n hn
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have : |ℓ n| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hℓ n hn)
    nlinarith [norm_nonneg (w n), norm_nonneg (a n), mul_nonneg (norm_nonneg (w n)) (norm_nonneg (a n))]
  have hc2 : ∀ n ∈ B, ‖w n * ((ℓ n : ℂ) ^ k) * a n * (-(Lg n : ℂ) * I)‖ ≤ ‖w n * a n‖ * |Lg n| := by
    intro n hn
    rw [norm_mul (w n * _ * a n), show ‖(-(Lg n : ℂ) * I)‖ = |Lg n| by simp]
    exact mul_le_mul_of_nonneg_right (hc1 n hn) (abs_nonneg _)
  have hb : ∀ t ∈ Set.uIcc (-H) H, ‖blockPoly B w a ℓ Lg k t‖ ^ 2 +
      ‖dpoly B (fun n => w n * ((ℓ n : ℂ) ^ k) * a n * (-(Lg n : ℂ) * I)) Lg t‖ ^ 2 ≤
      (∑ n ∈ B, ‖w n * a n‖) ^ 2 + (∑ n ∈ B, ‖w n * a n‖ * |Lg n|) ^ 2 := by
    intro t _
    have e1 := (norm_dpoly_le B _ Lg t).trans (Finset.sum_le_sum hc1)
    have e2 := (norm_dpoly_le B _ Lg t).trans (Finset.sum_le_sum hc2)
    unfold blockPoly
    gcongr
  have hcont : Continuous fun t => ‖blockPoly B w a ℓ Lg k t‖ ^ 2 +
      ‖dpoly B (fun n => w n * ((ℓ n : ℂ) ^ k) * a n * (-(Lg n : ℂ) * I)) Lg t‖ ^ 2 := by
    unfold blockPoly
    exact ((dpoly_continuous _ _ _).norm.pow 2).add ((dpoly_continuous _ _ _).norm.pow 2)
  have := intervalIntegral.integral_mono_on (by linarith : -H ≤ H)
    (hcont.intervalIntegrable _ _) (intervalIntegrable_const (μ := MeasureTheory.volume))
    (fun t ht => hb t (by rw [Set.uIcc_of_le (by linarith)]; exact ht))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add] at this
  linarith

lemma exp_one_div_250_le_two : Real.exp (1 / 250) ≤ 2 := by
  have h : (1 / 250 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  calc Real.exp (1 / 250) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h
    _ = 2 := Real.exp_log (by norm_num)

lemma hasSum_exp_real (x : ℝ) : HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at this

/-- The cpow factorization on a block. -/
lemma cpow_block {q N δ γ : ℝ} (hq : 0 < q) (hN : 0 < N) :
    ((q : ℂ)) ^ (-((δ : ℂ) + γ * I)) = ((N ^ (-δ) : ℝ) : ℂ) *
      ((Real.exp (-δ * Real.log (q / N)) : ℝ) : ℂ) *
      Complex.exp (-((γ * Real.log q : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne'), ← Complex.ofReal_log hq.le,
    Real.rpow_def_of_pos hN, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add, Real.log_div hq.ne' hN.ne']
  congr 1
  push_cast
  ring

lemma abs_log_div_le_one {q N : ℝ} (hN0 : 0 < N) (h1 : N ≤ q) (h2 : q < 2 * N) :
    |Real.log (q / N)| ≤ 1 := by
  have h1' : 1 ≤ q / N := (one_le_div hN0).2 h1
  have h2' : q / N ≤ 2 := (div_le_iff₀ hN0).2 (by linarith)
  have hl0 : 0 ≤ Real.log (q / N) := Real.log_nonneg h1'
  have hl1 : Real.log (q / N) ≤ Real.log 2 := Real.log_le_log (by linarith) h2'
  have := Real.log_two_lt_d9
  rw [abs_of_nonneg hl0]; linarith

lemma summable_sob (B : Finset ι) (w a : ι → ℂ) (ℓ Lg : ι → ℝ) (hℓ : ∀ n ∈ B, |ℓ n| ≤ 1)
    {H : ℝ} (hH : 0 ≤ H) :
    Summable fun k => ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) * blockSob B w a ℓ Lg H k := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity)
    (blockSob_nonneg B w a ℓ Lg hH k)) (fun k => mul_le_mul_of_nonneg_left
    (blockSob_le B w a ℓ Lg hℓ hH k) (by positivity)) ?_
  exact (hasSum_exp_real (1 / 250)).summable.mul_right _

/-- **The block bound.** -/
theorem block_bound (B : Finset ι) (q : ι → ℝ) (w a : ι → ℂ) {N H c δ γ : ℝ} (hN : 1 ≤ N)
    (hB : ∀ n ∈ B, N ≤ q n ∧ q n < 2 * N) (hH : 1 / 2 ≤ H) (hγ : |γ| ≤ H) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 250) (hc : 0 < c)
    (hlow : c ≤ ‖∑ n ∈ B, a n * w n * ((q n : ℂ)) ^ (-((δ : ℂ) + γ * I))‖) :
    c ^ 2 / 2 ≤ ∑' k : ℕ, ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
      blockSob B w a (fun n => Real.log (q n / N)) (fun n => Real.log (q n)) H k := by
  set ℓ : ι → ℝ := fun n => Real.log (q n / N)
  set Lg : ι → ℝ := fun n => Real.log (q n)
  have hN0 : 0 < N := by linarith
  have hq0 : ∀ n ∈ B, 0 < q n := fun n hn => hN0.trans_le (hB n hn).1
  have hℓ : ∀ n ∈ B, |ℓ n| ≤ 1 := by
    intro n hn
    have h1 : 1 ≤ q n / N := (one_le_div hN0).2 (hB n hn).1
    have h2 : q n / N ≤ 2 := (div_le_iff₀ hN0).2 (by linarith [(hB n hn).2])
    have hl0 : 0 ≤ Real.log (q n / N) := Real.log_nonneg h1
    have hl1 : Real.log (q n / N) ≤ Real.log 2 := Real.log_le_log (by linarith) h2
    have := Real.log_two_lt_d9
    rw [abs_of_nonneg hl0]; linarith
  set P : ℕ → ℝ → ℂ := blockPoly B w a ℓ Lg
  -- the expansion
  set K : ι → ℂ := fun n => a n * w n * ((N ^ (-δ) : ℝ) : ℂ) *
    Complex.exp (-((γ * Lg n : ℝ) : ℂ) * I)
  have hterm : ∀ n ∈ B, HasSum (fun k : ℕ => K n * ((((-δ * ℓ n) ^ k / (Nat.factorial k : ℝ)) : ℝ) : ℂ))
      (a n * w n * ((q n : ℂ)) ^ (-((δ : ℂ) + γ * I))) := by
    intro n hn
    have h := (Complex.hasSum_ofReal.2 (hasSum_exp_real (-δ * ℓ n))).mul_left (K n)
    rw [cpow_block (hq0 n hn) hN0]
    have e : a n * w n * (((N ^ (-δ) : ℝ) : ℂ) * ((Real.exp (-δ * Real.log (q n / N)) : ℝ) : ℂ) *
        Complex.exp (-((γ * Real.log (q n) : ℝ) : ℂ) * I)) =
        K n * ((Real.exp (-δ * ℓ n) : ℝ) : ℂ) := by
      simp only [K, ℓ, Lg]; ring
    rw [e]; exact h
  have hsum := hasSum_sum hterm
  have hk : ∀ k : ℕ, ∑ n ∈ B, K n * ((((-δ * ℓ n) ^ k / (Nat.factorial k : ℝ)) : ℝ) : ℂ) =
      ((N ^ (-δ) : ℝ) : ℂ) * ((((-δ) ^ k / (Nat.factorial k : ℝ)) : ℝ) : ℂ) * P k γ := by
    intro k
    rw [show P k γ = ∑ n ∈ B, (w n * ((ℓ n : ℂ) ^ k) * a n) *
      Complex.exp (-((γ * Lg n : ℝ) : ℂ) * I) from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [K]
    push_cast
    ring
  simp only [hk] at hsum
  -- norms
  set M0 : ℝ := ∑ n ∈ B, ‖w n * a n‖
  have hP : ∀ k t, ‖P k t‖ ≤ M0 := by
    intro k t
    refine (norm_dpoly_le B _ Lg t).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul]
    have : |ℓ n| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hℓ n hn)
    nlinarith [norm_nonneg (w n), norm_nonneg (a n), mul_nonneg (norm_nonneg (w n)) (norm_nonneg (a n))]
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set u : ℕ → ℝ := fun k => δ ^ k / (Nat.factorial k : ℝ)
  have hu : HasSum u (Real.exp δ) := hasSum_exp_real δ
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  set g : ℕ → ℝ := fun k => u k * ‖P k γ‖
  have hgs : Summable g :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => mul_le_mul_of_nonneg_left (hP k γ)
      (hu0 k)) (hu.summable.mul_right M0)
  have hNd : (N ^ (-δ) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hbd : ∀ k, ‖((N ^ (-δ) : ℝ) : ℂ) * ((((-δ) ^ k / (Nat.factorial k : ℝ)) : ℝ) : ℂ) * P k γ‖
      ≤ g k := by
    intro k
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_div, abs_pow, abs_neg,
      abs_of_nonneg hδ0, Nat.abs_cast]
    have : 0 ≤ δ ^ k / (Nat.factorial k : ℝ) * ‖P k γ‖ := by positivity
    calc N ^ (-δ) * (δ ^ k / (Nat.factorial k : ℝ)) * ‖P k γ‖
        = N ^ (-δ) * (δ ^ k / (Nat.factorial k : ℝ) * ‖P k γ‖) := by ring
      _ ≤ 1 * (δ ^ k / (Nat.factorial k : ℝ) * ‖P k γ‖) := by gcongr
      _ = g k := by simp [g, u]
  have hlow2 : c ≤ ∑' k, g k := hlow.trans (hsum.norm_le_of_bounded hgs.hasSum hbd)
  -- weighted Cauchy–Schwarz
  set lam : ℝ := 2 / c
  have hlam : 0 < lam := by positivity
  have hx2s : Summable fun k => u k * ‖P k γ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hP k γ) 2) (hu0 k))
      (hu.summable.mul_right (M0 ^ 2))
  have hamgm : ∀ k, g k ≤ u k / (2 * lam) + lam / 2 * (u k * ‖P k γ‖ ^ 2) := by
    intro k
    have hx := norm_nonneg (P k γ)
    have : ‖P k γ‖ ≤ 1 / (2 * lam) + lam / 2 * ‖P k γ‖ ^ 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (lam * ‖P k γ‖ - 1)]
    calc g k = u k * ‖P k γ‖ := rfl
      _ ≤ u k * (1 / (2 * lam) + lam / 2 * ‖P k γ‖ ^ 2) := mul_le_mul_of_nonneg_left this (hu0 k)
      _ = _ := by ring
  have hsum2 : ∑' k, g k ≤ Real.exp δ / (2 * lam) + lam / 2 * ∑' k, u k * ‖P k γ‖ ^ 2 := by
    have h1 := (hu.div_const (2 * lam)).add (hx2s.hasSum.mul_left (lam / 2))
    exact hasSum_le hamgm hgs.hasSum h1
  have hexpδ : Real.exp δ ≤ 2 := (Real.exp_le_exp.2 hδ).trans exp_one_div_250_le_two
  have hQ : c ^ 2 / 2 ≤ ∑' k, u k * ‖P k γ‖ ^ 2 := by
    have h1 : Real.exp δ / (2 * lam) ≤ c / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      simp only [lam]
      field_simp
      nlinarith
    have h2 : c / 2 ≤ lam / 2 * ∑' k, u k * ‖P k γ‖ ^ 2 := by linarith
    simp only [lam] at h2
    have : c / 2 ≤ (1 / c) * ∑' k, u k * ‖P k γ‖ ^ 2 := by
      convert h2 using 1; ring
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc] at this
    nlinarith
  -- compare with the Sobolev quantity
  have hSob : ∀ k, u k * ‖P k γ‖ ^ 2 ≤ ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
      blockSob B w a ℓ Lg H k := by
    intro k
    have h1 : u k ≤ (1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ) := by
      simp only [u]; gcongr
    have h2 : ‖P k γ‖ ^ 2 ≤ blockSob B w a ℓ Lg H k := by
      have := norm_dpoly_sq_le B (fun n => w n * ((ℓ n : ℂ) ^ k) * a n) Lg hH hγ
      simpa [blockSob, blockPoly, P] using this
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hSobS : Summable fun k => ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
      blockSob B w a ℓ Lg H k := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity)
      (blockSob_nonneg B w a ℓ Lg (by linarith) k)) (fun k => mul_le_mul_of_nonneg_left
      (blockSob_le B w a ℓ Lg hℓ (by linarith) k) (by positivity)) ?_
    exact (hasSum_exp_real (1 / 250)).summable.mul_right _
  exact hQ.trans (hx2s.tsum_le_tsum hSob hSobS)

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_LSum: the large sieve applied to the Sobolev quantities

If `∑_{r ∈ T} ‖∑_{n ∈ B} b_n a_r(n)‖² ≤ Λ₀ ∑_B ‖b_n‖²` for every `b`, then for every `k`,
`∑_{r ∈ T} Sob_{r,k} ≤ 2 (2H) Λ₀ ∑_B ‖w_n‖² (1 + (log q_n)²)`: apply the large sieve at each `t`
to `P_k(t)` and `P_k'(t)` and integrate over `|t| ≤ H`. -/

open Complex MeasureTheory intervalIntegral Set

namespace ArtinPrimitiveRoots

namespace L3Z

variable {R ι : Type*}

theorem sum_blockSob_le (T : Finset R) (B : Finset ι) (w : ι → ℂ) (ar : R → ι → ℂ)
    (ℓ Lg : ι → ℝ) (hℓ : ∀ n ∈ B, |ℓ n| ≤ 1) {H Λ₀ : ℝ} (hH : 0 ≤ H) (hΛ : 0 ≤ Λ₀)
    (hLS : ∀ b : ι → ℂ, ∑ r ∈ T, ‖∑ n ∈ B, b n * ar r n‖ ^ 2 ≤ Λ₀ * ∑ n ∈ B, ‖b n‖ ^ 2)
    (k : ℕ) :
    ∑ r ∈ T, blockSob B w (ar r) ℓ Lg H k ≤
      2 * ((H + H) * (Λ₀ * ∑ n ∈ B, ‖w n‖ ^ 2 * (1 + Lg n ^ 2))) := by
  set E : ℝ → ι → ℂ := fun t n => Complex.exp (-((t * Lg n : ℝ) : ℂ) * I)
  have hE : ∀ t n, ‖E t n‖ = 1 := fun t n => by simp [E, Complex.norm_exp]
  set A : R → ℝ → ℝ := fun r t => ‖blockPoly B w (ar r) ℓ Lg k t‖ ^ 2
  set D : R → ℝ → ℝ := fun r t =>
    ‖dpoly B (fun n => w n * ((ℓ n : ℂ) ^ k) * ar r n * (-(Lg n : ℂ) * I)) Lg t‖ ^ 2
  have hAc : ∀ r, Continuous (A r) := fun r => by
    simp only [A, blockPoly]; exact (dpoly_continuous _ _ _).norm.pow 2
  have hDc : ∀ r, Continuous (D r) := fun r => by
    simp only [D]; exact (dpoly_continuous _ _ _).norm.pow 2
  have hℓk : ∀ n ∈ B, ‖((ℓ n : ℂ) ^ k)‖ ≤ 1 := by
    intro n hn
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hℓ n hn)
  have hpt : ∀ t, ∑ r ∈ T, (A r t + D r t) ≤ Λ₀ * ∑ n ∈ B, ‖w n‖ ^ 2 * (1 + Lg n ^ 2) := by
    intro t
    rw [Finset.sum_add_distrib]
    have h1 := hLS (fun n => w n * ((ℓ n : ℂ) ^ k) * E t n)
    have h2 := hLS (fun n => w n * ((ℓ n : ℂ) ^ k) * (-(Lg n : ℂ) * I) * E t n)
    have eA : ∀ r, A r t = ‖∑ n ∈ B, w n * ((ℓ n : ℂ) ^ k) * E t n * ar r n‖ ^ 2 := by
      intro r; simp only [A, blockPoly, dpoly, E]
      congr 2; exact Finset.sum_congr rfl fun n _ => by ring
    have eD : ∀ r, D r t = ‖∑ n ∈ B, w n * ((ℓ n : ℂ) ^ k) * (-(Lg n : ℂ) * I) * E t n *
        ar r n‖ ^ 2 := by
      intro r; simp only [D, dpoly, E]
      congr 2; exact Finset.sum_congr rfl fun n _ => by ring
    simp only [eA, eD]
    have b1 : ∑ n ∈ B, ‖w n * ((ℓ n : ℂ) ^ k) * E t n‖ ^ 2 ≤ ∑ n ∈ B, ‖w n‖ ^ 2 := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [norm_mul, norm_mul, hE, mul_one]
      have := hℓk n hn
      have : ‖w n‖ * ‖((ℓ n : ℂ) ^ k)‖ ≤ ‖w n‖ :=
        mul_le_of_le_one_right (norm_nonneg _) this
      exact pow_le_pow_left₀ (by positivity) this 2
    have b2 : ∑ n ∈ B, ‖w n * ((ℓ n : ℂ) ^ k) * (-(Lg n : ℂ) * I) * E t n‖ ^ 2 ≤
        ∑ n ∈ B, ‖w n‖ ^ 2 * Lg n ^ 2 := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [norm_mul, norm_mul, norm_mul, hE, mul_one,
        show ‖(-(Lg n : ℂ) * I)‖ = |Lg n| by simp]
      have := hℓk n hn
      have : ‖w n‖ * ‖((ℓ n : ℂ) ^ k)‖ * |Lg n| ≤ ‖w n‖ * |Lg n| := by
        gcongr; exact mul_le_of_le_one_right (norm_nonneg _) this
      calc (‖w n‖ * ‖((ℓ n : ℂ) ^ k)‖ * |Lg n|) ^ 2 ≤ (‖w n‖ * |Lg n|) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = ‖w n‖ ^ 2 * Lg n ^ 2 := by rw [mul_pow, sq_abs]
    have : Λ₀ * ∑ n ∈ B, ‖w n‖ ^ 2 * (1 + Lg n ^ 2) =
        Λ₀ * ∑ n ∈ B, ‖w n‖ ^ 2 + Λ₀ * ∑ n ∈ B, ‖w n‖ ^ 2 * Lg n ^ 2 := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1; exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    exact add_le_add (h1.trans (mul_le_mul_of_nonneg_left b1 hΛ))
      (h2.trans (mul_le_mul_of_nonneg_left b2 hΛ))
  have hsum : ∑ r ∈ T, blockSob B w (ar r) ℓ Lg H k =
      2 * ∫ t in (-H)..H, ∑ r ∈ T, (A r t + D r t) := by
    have := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := -H) (b := H)
      (s := T) (f := fun r t => A r t + D r t)
      (fun r _ => ((hAc r).add (hDc r)).intervalIntegrable _ _)
    rw [this, Finset.mul_sum]
    rfl
  rw [hsum]
  have hmono := intervalIntegral.integral_mono_on (by linarith : -H ≤ H)
    (f := fun t => ∑ r ∈ T, (A r t + D r t))
    ((continuous_finsetSum _ fun r _ => (hAc r).add (hDc r)).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := MeasureTheory.volume)) (fun t _ => hpt t)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add] at hmono
  linarith

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Row: one detected row gives a large zero-independent quantity

Split `X < q_n ≤ Z` into the dyadic blocks `2^j ≤ q_n < 2^{j+1}` (`j = Nat.log 2 q_n < J`),
restricted to the ideals where the coefficient can be nonzero. If the detected sum has norm
`≥ 1/2`, one block has norm `≥ 1/(2J)`, and `block_bound` (with `σ₀ = .996`,
`w(n) = α_X(n) q_n^{-σ₀} e^{-q_n/Y}`) gives `1/(8J²) ≤ ∑_j ∑_k (1/250)^k/k! Sob_{j,k}`. -/

open NumberField Complex Filter Topology Set UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] Classical.propDecidable

/-- The number of dyadic blocks up to `Z`. -/
noncomputable def numBlocks (Z : ℝ) : ℕ := Nat.log 2 ⌊Z⌋₊ + 1

/-- The `j`-th block: `X < q_n`, `2^j ≤ q_n < 2^{j+1}`, `n ∈ Ext`. -/
noncomputable def blk (F : Type*) [Field F] [NumberField F] (Ext : Ideal (𝓞 F) → Prop) (X Z : ℝ)
    (j : ℕ) : Finset (Ideal (𝓞 F)) :=
  ((idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ) ∧ Nat.log 2 (Ideal.absNorm n) = j)).filter
    Ext

/-- The fixed weight `w(n) = α_X(n) q_n^{-σ₀} e^{-q_n/Y}`. -/
noncomputable def wt (F : Type*) [Field F] [NumberField F] (X Y : ℝ) (n : Ideal (𝓞 F)) : ℂ :=
  alpha F X n * ((((Ideal.absNorm n : ℕ) : ℝ) ^ (-(996 / 1000 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (-(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ))

/-- The zero-independent row quantity. -/
noncomputable def rowQ (F : Type*) [Field F] [NumberField F] (Ext : Ideal (𝓞 F) → Prop)
    (a : Ideal (𝓞 F) → ℂ) (X Y Z H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (numBlocks Z), ∑' k : ℕ, ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
    blockSob (blk F Ext X Z j) (wt F X Y) a
      (fun n => Real.log ((Ideal.absNorm n : ℝ) / (2 ^ j : ℝ)))
      (fun n => Real.log (Ideal.absNorm n : ℝ)) H k

lemma mem_blk_bounds {Ext : Ideal (𝓞 F) → Prop} {X Z : ℝ} {j : ℕ} {n : Ideal (𝓞 F)}
    (hn : n ∈ blk F Ext X Z j) :
    (2 ^ j : ℝ) ≤ Ideal.absNorm n ∧ (Ideal.absNorm n : ℝ) < 2 * 2 ^ j := by
  simp only [blk, Finset.mem_filter, mem_idealsUpTo] at hn
  have hq : Ideal.absNorm n ≠ 0 := (absNorm_pos hn.1.1.1).ne'
  rw [← hn.1.2.2]
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 hq
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Ideal.absNorm n)
    rw [pow_succ] at this
    have : (Ideal.absNorm n : ℝ) < ((2 ^ Nat.log 2 (Ideal.absNorm n) * 2 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this; linarith

theorem row_detect (a : Ideal (𝓞 F) → ℂ) (Ext : Ideal (𝓞 F) → Prop)
    (hExt : ∀ n, ¬ Ext n → a n = 0) {X Y Z H : ℝ} (hH : 1 / 2 ≤ H) {ρ₀ : ℂ}
    (h1 : 996 / 1000 ≤ ρ₀.re) (h2 : ρ₀.re ≤ 1) (hγ : |ρ₀.im| ≤ H)
    (hR : 1 / 2 ≤ ‖∑ n ∈ (idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ)),
      detTerm F a X Y ρ₀ n‖) :
    1 / (8 * (numBlocks Z : ℝ) ^ 2) ≤ rowQ F Ext a X Y Z H := by
  set J := numBlocks Z
  have hJ : 0 < J := Nat.succ_pos _
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  -- 1. the dyadic split
  have hmaps : ∀ n ∈ (idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ)),
      Nat.log 2 (Ideal.absNorm n) ∈ Finset.range J := by
    intro n hn
    simp only [Finset.mem_filter, mem_idealsUpTo] at hn
    rw [Finset.mem_range]
    have hq : Ideal.absNorm n ≤ ⌊Z⌋₊ := Nat.le_floor hn.1.2
    exact Nat.lt_succ_of_le (Nat.log_mono_right hq)
  have hsplit : ∑ n ∈ (idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ)),
      detTerm F a X Y ρ₀ n = ∑ j ∈ Finset.range J, ∑ n ∈ blk F Ext X Z j, detTerm F a X Y ρ₀ n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hb : blk F Ext X Z j = (((idealsUpTo F Z).filter (fun n => X < (Ideal.absNorm n : ℝ))).filter
        (fun n => Nat.log 2 (Ideal.absNorm n) = j)).filter Ext := by
      rw [blk, Finset.filter_filter, Finset.filter_filter, Finset.filter_filter]; simp only [and_assoc]
    rw [hb, Finset.sum_filter_of_ne (p := Ext) (fun n _ hne => by
      by_contra hx
      exact hne (by simp [detTerm, hExt n hx]))]
  rw [hsplit] at hR
  -- 2. pigeonhole
  obtain ⟨j, hj, hjb⟩ : ∃ j ∈ Finset.range J,
      1 / (2 * (J : ℝ)) ≤ ‖∑ n ∈ blk F Ext X Z j, detTerm F a X Y ρ₀ n‖ := by
    by_contra hcon
    push Not at hcon
    have h := (norm_sum_le _ _).trans_lt (Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.2 hJ.ne') hcon)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have : (J : ℝ) * (1 / (2 * J)) = 1 / 2 := by field_simp
    linarith
  -- 3. the block bound
  set δ := ρ₀.re - 996 / 1000
  have hρ : ρ₀ = ((996 / 1000 : ℝ) : ℂ) + ((δ : ℂ) + (ρ₀.im : ℂ) * I) := by
    apply Complex.ext <;> simp [δ]
  have hterm : ∀ n ∈ blk F Ext X Z j, detTerm F a X Y ρ₀ n =
      a n * wt F X Y n * (((Ideal.absNorm n : ℕ) : ℝ) : ℂ) ^ (-((δ : ℂ) + (ρ₀.im : ℂ) * I)) := by
    intro n hn
    have hq : (0 : ℝ) < ((Ideal.absNorm n : ℕ) : ℝ) := by
      have := (mem_blk_bounds hn).1; have : (0 : ℝ) < 2 ^ j := by positivity
      linarith
    have hcp : (((Ideal.absNorm n : ℕ) : ℝ) : ℂ) ^ (-ρ₀) =
        ((((Ideal.absNorm n : ℕ) : ℝ) ^ (-(996 / 1000 : ℝ)) : ℝ) : ℂ) *
          (((Ideal.absNorm n : ℕ) : ℝ) : ℂ) ^ (-((δ : ℂ) + (ρ₀.im : ℂ) * I)) := by
      conv_lhs => rw [hρ]
      rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hq.ne'),
        Complex.ofReal_cpow hq.le]
      push_cast; ring_nf
    simp only [detTerm, wt, hcp]
    ring
  rw [Finset.sum_congr rfl hterm] at hjb
  have hbb := block_bound (blk F Ext X Z j) (fun n => ((Ideal.absNorm n : ℕ) : ℝ)) (wt F X Y) a
    (N := 2 ^ j) (one_le_pow₀ (by norm_num)) (fun n hn => mem_blk_bounds hn) hH hγ
    (by simp only [δ]; linarith) (by simp only [δ]; linarith) (by positivity) hjb
  -- 4. one block suffices
  have hc : (1 / (2 * (J : ℝ))) ^ 2 / 2 = 1 / (8 * (J : ℝ) ^ 2) := by field_simp; ring
  rw [hc] at hbb
  refine hbb.trans ?_
  unfold rowQ
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j => ∑' k : ℕ,
    ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) * blockSob (blk F Ext X Z j) (wt F X Y) a
      (fun n => Real.log ((Ideal.absNorm n : ℝ) / (2 ^ j : ℝ)))
      (fun n => Real.log (Ideal.absNorm n : ℝ)) H k) (fun j _ => tsum_nonneg fun k =>
      mul_nonneg (by positivity) (blockSob_nonneg _ _ _ _ _ (by linarith) k)) hj)
  push_cast
  rfl

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Count: Chebyshev's inequality over the rows

If every row of `T` has `rowQ ≥ 1/(8J²)` and the large sieve holds on every block with constant
`Λ_j`, then `|T| / (8J²) ≤ 2 ∑_{j<J} 2 (2H) Λ_j ∑_{blk j} ‖w‖² (1 + log² q)`. -/

open NumberField Complex Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F] {R : Type*}

attribute [local instance] Classical.propDecidable

theorem count_bound (T : Finset R) (ar : R → Ideal (𝓞 F) → ℂ) (Ext : Ideal (𝓞 F) → Prop)
    {X Y Z H : ℝ} (hH : 0 ≤ H) (Λ : ℕ → ℝ) (hΛ : ∀ j, 0 ≤ Λ j)
    (hLS : ∀ j ∈ Finset.range (numBlocks Z), ∀ b : Ideal (𝓞 F) → ℂ,
      ∑ r ∈ T, ‖∑ n ∈ blk F Ext X Z j, b n * ar r n‖ ^ 2 ≤
        Λ j * ∑ n ∈ blk F Ext X Z j, ‖b n‖ ^ 2)
    (hrow : ∀ r ∈ T, 1 / (8 * (numBlocks Z : ℝ) ^ 2) ≤ rowQ F Ext (ar r) X Y Z H) :
    (T.card : ℝ) * (1 / (8 * (numBlocks Z : ℝ) ^ 2)) ≤
      ∑ j ∈ Finset.range (numBlocks Z), 2 * (2 * ((H + H) * (Λ j *
        ∑ n ∈ blk F Ext X Z j, ‖wt F X Y n‖ ^ 2 *
          (1 + Real.log (Ideal.absNorm n : ℝ) ^ 2)))) := by
  set J := numBlocks Z
  have h1 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) ≤ ∑ r ∈ T, rowQ F Ext (ar r) X Y Z H := by
    have := Finset.card_nsmul_le_sum T _ _ hrow
    rwa [nsmul_eq_mul] at this
  refine h1.trans ?_
  unfold rowQ
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j hj => ?_
  set ℓ : Ideal (𝓞 F) → ℝ := fun n => Real.log ((Ideal.absNorm n : ℝ) / (2 ^ j : ℝ))
  set Lg : Ideal (𝓞 F) → ℝ := fun n => Real.log (Ideal.absNorm n : ℝ)
  have hℓ : ∀ n ∈ blk F Ext X Z j, |ℓ n| ≤ 1 := by
    intro n hn
    have hb := mem_blk_bounds hn
    exact abs_log_div_le_one (by positivity) hb.1 hb.2
  have hsumm : ∀ r ∈ T, Summable fun k => ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
      blockSob (blk F Ext X Z j) (wt F X Y) (ar r) ℓ Lg H k :=
    fun r _ => summable_sob _ _ _ _ _ hℓ hH
  rw [← Summable.tsum_finsetSum hsumm]
  set Bd := 2 * ((H + H) * (Λ j * ∑ n ∈ blk F Ext X Z j, ‖wt F X Y n‖ ^ 2 * (1 + Lg n ^ 2)))
  have hk : ∀ k : ℕ, ∑ r ∈ T, ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
      blockSob (blk F Ext X Z j) (wt F X Y) (ar r) ℓ Lg H k ≤
      ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) * Bd := by
    intro k
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_blockSob_le T _ (wt F X Y) ar ℓ Lg hℓ hH (hΛ j)
      (hLS j hj) k) (by positivity)
  have hBd : HasSum (fun k : ℕ => ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) * Bd)
      (Real.exp (1 / 250) * Bd) := (hasSum_exp_real _).mul_right _
  have hBd0 : 0 ≤ Bd := mul_nonneg (by norm_num) (mul_nonneg (by linarith)
    (mul_nonneg (hΛ j) (Finset.sum_nonneg fun _ _ => by positivity)))
  calc ∑' k, ∑ r ∈ T, ((1 / 250 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
        blockSob (blk F Ext X Z j) (wt F X Y) (ar r) ℓ Lg H k
      ≤ Real.exp (1 / 250) * Bd :=
        hasSum_le hk (summable_sum fun r hr => hsumm r hr).hasSum hBd
    _ ≤ 2 * Bd := mul_le_mul_of_nonneg_right exp_one_div_250_le_two hBd0

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Mass: the large-sieve cost of one block, (8.9)

With `X = U²`, `Y = U^20`, `Z = U^22` and `N = 2^{j+1}`: on a nonempty block `U² < N`, so
`(N + U²)(NU)^{.001} ∑_{blk} ‖w‖² (1 + log² q) ≪ N^{2.002} U^{.021} (N/2)^{-1.99} ≪ U^{.285}`,
since `‖w(n)‖ ≤ C_δ q^{-.995}` (`|α| ≤ 2^ω ≪ q^{.001}`), `#{q < N} ≤ N^{1.001} ζ(1.001)` and
`N ≤ 2Z`. -/

open NumberField Complex Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L3Z

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] Classical.propDecidable

lemma norm_wt_le {Cδ : ℝ}
    (hCδ : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ Cδ * (Ideal.absNorm I : ℝ) ^ (1 / 1000 : ℝ))
    {X Y : ℝ} (hY : 0 < Y) {n : Ideal (𝓞 F)} (hn : n ≠ ⊥) :
    ‖wt F X Y n‖ ≤ Cδ * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(995 / 1000 : ℝ)) := by
  have hq : (0 : ℝ) < ((Ideal.absNorm n : ℕ) : ℝ) := by exact_mod_cast absNorm_pos hn
  unfold wt
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Complex.norm_exp]
  have he : Real.exp (-(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ)).re ≤ 1 := by
    rw [Real.exp_le_one_iff]
    rw [show -(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ) =
      ((-(((Ideal.absNorm n : ℕ) : ℝ)) / Y : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hY.le
  have hα := (norm_alpha_le X hn).trans (hCδ n hn)
  have hCδ0 : 0 ≤ Cδ * (Ideal.absNorm n : ℝ) ^ (1 / 1000 : ℝ) := (by positivity : (0:ℝ) ≤ 2 ^ _).trans
    ((le_refl _).trans (hCδ n hn))
  calc ‖alpha F X n‖ * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(996 / 1000 : ℝ)) *
        Real.exp (-(((Ideal.absNorm n : ℕ) : ℝ) : ℂ) / (Y : ℂ)).re
      ≤ (Cδ * (Ideal.absNorm n : ℝ) ^ (1 / 1000 : ℝ)) *
        ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(996 / 1000 : ℝ)) * 1 := by gcongr
    _ = Cδ * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(995 / 1000 : ℝ)) := by
      rw [mul_one, mul_assoc, ← Real.rpow_add hq]; norm_num

lemma one_add_log_sq_le {U q : ℝ} (hU : 1 ≤ U) (hq : 1 ≤ q) (hqZ : q ≤ U ^ (22 : ℝ)) :
    1 + Real.log q ^ 2 ≤ (1 + 2200 ^ 2) * U ^ (2 / 100 : ℝ) := by
  have hU0 : 0 < U := by linarith
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have hl1 : Real.log q ≤ 22 * Real.log U := by
    have := Real.log_le_log (by linarith) hqZ
    rwa [Real.log_rpow hU0] at this
  have hl2 : Real.log U ≤ U ^ (1 / 100 : ℝ) / (1 / 100) := Real.log_le_rpow_div hU0.le (by norm_num)
  have hl3 : Real.log q ≤ 2200 * U ^ (1 / 100 : ℝ) := by
    have : U ^ (1 / 100 : ℝ) / (1 / 100) = 100 * U ^ (1 / 100 : ℝ) := by ring
    linarith
  have hsq : (U ^ (1 / 100 : ℝ)) ^ 2 = U ^ (2 / 100 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
  have h1 : 1 ≤ U ^ (2 / 100 : ℝ) := Real.one_le_rpow hU (by norm_num)
  have h2 : Real.log q ^ 2 ≤ 2200 ^ 2 * U ^ (2 / 100 : ℝ) := by
    rw [← hsq, ← mul_pow]; exact pow_le_pow_left₀ hl0 hl3 2
  nlinarith

theorem block_mass_bound (Ext : Ideal (𝓞 F) → Prop) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C : ℝ, 0 ≤ C → ∀ U : ℝ, 2 ≤ U → ∀ j : ℕ, (2 : ℝ) ^ j ≤ U ^ (22 : ℝ) →
      C * ((2 * 2 ^ j : ℝ) + U ^ 2) * ((2 * 2 ^ j : ℝ) * U) ^ (1 / 1000 : ℝ) *
        ∑ n ∈ blk F Ext (U ^ (2 : ℝ)) (U ^ (22 : ℝ)) j, ‖wt F (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) n‖ ^ 2 *
          (1 + Real.log (Ideal.absNorm n : ℝ) ^ 2) ≤ C * K * U ^ (285 / 1000 : ℝ) := by
  obtain ⟨Cδ, hCδpos, hCδ⟩ := two_pow_card_support_le (F := F) (by norm_num : (0 : ℝ) < 1 / 1000)
  have hσ : (1 : ℝ) < 1001 / 1000 := by norm_num
  set ζ := zetaR F (1001 / 1000)
  have hζ0 : 0 ≤ ζ := tsum_nonneg fun _ => by positivity
  set K : ℝ := 4 * (ζ * Cδ ^ 2 * 2 ^ (199 / 100 : ℝ) * (1 + 2200 ^ 2)) * 2 ^ (12 / 1000 : ℝ)
  refine ⟨2 * K, by positivity, fun C hC U hU j hj => ?_⟩
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  set N : ℝ := 2 * 2 ^ j with hN
  have hN0 : 0 < N := by positivity
  set S := ∑ n ∈ blk F Ext (U ^ (2 : ℝ)) (U ^ (22 : ℝ)) j,
    ‖wt F (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) n‖ ^ 2 * (1 + Real.log (Ideal.absNorm n : ℝ) ^ 2)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hRHS : 0 ≤ C * (2 * K) * U ^ (285 / 1000 : ℝ) := by positivity
  rcases (blk F Ext (U ^ (2 : ℝ)) (U ^ (22 : ℝ)) j).eq_empty_or_nonempty with he | ⟨n₀, hn₀⟩
  · have : S = 0 := by simp only [S, he, Finset.sum_empty]
    rw [this, mul_zero]; exact hRHS
  -- the block is nonempty: `U² < N`
  have hUN : U ^ 2 < N := by
    have h1 := mem_blk_bounds hn₀
    simp only [blk, Finset.mem_filter] at hn₀
    have h2 : U ^ (2 : ℝ) < Ideal.absNorm n₀ := hn₀.1.2.1
    rw [Real.rpow_two] at h2
    rw [hN]; exact lt_trans h2 h1.2
  -- pointwise bound
  have hterm : ∀ n ∈ blk F Ext (U ^ (2 : ℝ)) (U ^ (22 : ℝ)) j,
      ‖wt F (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) n‖ ^ 2 * (1 + Real.log (Ideal.absNorm n : ℝ) ^ 2) ≤
        Cδ ^ 2 * (N / 2) ^ (-(199 / 100 : ℝ)) * ((1 + 2200 ^ 2) * U ^ (2 / 100 : ℝ)) := by
    intro n hn
    have hb := mem_blk_bounds hn
    have hn' := hn
    simp only [blk, Finset.mem_filter, mem_idealsUpTo] at hn'
    have hn0 := hn'.1.1.1
    have hq1 : (1 : ℝ) ≤ Ideal.absNorm n := by exact_mod_cast absNorm_pos hn0
    have hq : (0 : ℝ) < Ideal.absNorm n := by linarith
    have hw := norm_wt_le hCδ (X := U ^ (2 : ℝ)) (by positivity : (0 : ℝ) < U ^ (20 : ℝ)) hn0
    have hw2 : ‖wt F (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) n‖ ^ 2 ≤
        Cδ ^ 2 * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(199 / 100 : ℝ)) := by
      calc _ ≤ (Cδ * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(995 / 1000 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hw 2
        _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast (((Ideal.absNorm n : ℕ) : ℝ) ^ _),
            ← Real.rpow_mul hq.le]; norm_num
    have hq2 : ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(199 / 100 : ℝ)) ≤ (N / 2) ^ (-(199 / 100 : ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
      rw [hN]; field_simp; exact_mod_cast hb.1
    have hlog := one_add_log_sq_le hU1 hq1 hn'.1.1.2
    calc _ ≤ (Cδ ^ 2 * ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(199 / 100 : ℝ))) *
          ((1 + 2200 ^ 2) * U ^ (2 / 100 : ℝ)) :=
          mul_le_mul hw2 hlog (by positivity) (by positivity)
      _ ≤ _ := by gcongr
  -- the count
  have hcard : ((blk F Ext (U ^ (2 : ℝ)) (U ^ (22 : ℝ)) j).card : ℝ) ≤ N ^ (1001 / 1000 : ℝ) * ζ := by
    have hsub : blk F Ext (U ^ (2 : ℝ)) (U ^ (22 : ℝ)) j ⊆ idealsUpTo F N := by
      intro n hn
      have hb := mem_blk_bounds hn
      simp only [blk, Finset.mem_filter, mem_idealsUpTo] at hn
      exact mem_idealsUpTo.2 ⟨hn.1.1.1, by rw [hN]; linarith [hb.2]⟩
    refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
    exact card_idealsUpTo_le (by norm_num) hN0.le (T12B.summable_absNorm_rpow hσ)
  have hSb : S ≤ N ^ (1001 / 1000 : ℝ) * ζ *
      (Cδ ^ 2 * (N / 2) ^ (-(199 / 100 : ℝ)) * ((1 + 2200 ^ 2) * U ^ (2 / 100 : ℝ))) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  -- assembling the powers of `N`
  have hNU : (N + U ^ 2) ≤ 2 * N := by linarith
  have hNU' : (N * U) ^ (1 / 1000 : ℝ) = N ^ (1 / 1000 : ℝ) * U ^ (1 / 1000 : ℝ) :=
    Real.mul_rpow hN0.le hU0.le
  have hNpow : N * N ^ (1 / 1000 : ℝ) * N ^ (1001 / 1000 : ℝ) * (N / 2) ^ (-(199 / 100 : ℝ)) =
      2 ^ (199 / 100 : ℝ) * N ^ (12 / 1000 : ℝ) := by
    rw [Real.div_rpow hN0.le (by norm_num)]
    have e1 : N * N ^ (1 / 1000 : ℝ) * N ^ (1001 / 1000 : ℝ) * N ^ (-(199 / 100 : ℝ)) =
        N ^ (12 / 1000 : ℝ) := by
      rw [← Real.rpow_one_add' hN0.le (by norm_num), ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      norm_num
    have e2 : (2 : ℝ) ^ (-(199 / 100 : ℝ)) = (2 ^ (199 / 100 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
    rw [e2, div_inv_eq_mul, ← mul_assoc, e1]; ring
  have hNZ : N ^ (12 / 1000 : ℝ) ≤ 2 ^ (12 / 1000 : ℝ) * U ^ (264 / 1000 : ℝ) := by
    have h1 : N ≤ 2 * U ^ (22 : ℝ) := by rw [hN]; linarith
    calc N ^ (12 / 1000 : ℝ) ≤ (2 * U ^ (22 : ℝ)) ^ (12 / 1000 : ℝ) :=
          Real.rpow_le_rpow hN0.le h1 (by norm_num)
      _ = 2 ^ (12 / 1000 : ℝ) * U ^ (264 / 1000 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hU0.le]; norm_num
  have hUU : U ^ (1 / 1000 : ℝ) * U ^ (2 / 100 : ℝ) * U ^ (264 / 1000 : ℝ) = U ^ (285 / 1000 : ℝ) := by
    rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]; norm_num
  have hpos1 : 0 ≤ (N * U) ^ (1 / 1000 : ℝ) := by positivity
  calc C * (N + U ^ 2) * (N * U) ^ (1 / 1000 : ℝ) * S
      ≤ C * (2 * N) * (N * U) ^ (1 / 1000 : ℝ) * (N ^ (1001 / 1000 : ℝ) * ζ *
          (Cδ ^ 2 * (N / 2) ^ (-(199 / 100 : ℝ)) * ((1 + 2200 ^ 2) * U ^ (2 / 100 : ℝ)))) := by
        gcongr
    _ = C * (2 * (ζ * Cδ ^ 2 * (1 + 2200 ^ 2))) * (N * N ^ (1 / 1000 : ℝ) * N ^ (1001 / 1000 : ℝ) *
          (N / 2) ^ (-(199 / 100 : ℝ))) * (U ^ (1 / 1000 : ℝ) * U ^ (2 / 100 : ℝ)) := by
        rw [hNU']; ring
    _ = C * (2 * (ζ * Cδ ^ 2 * (1 + 2200 ^ 2))) * 2 ^ (199 / 100 : ℝ) * N ^ (12 / 1000 : ℝ) *
          (U ^ (1 / 1000 : ℝ) * U ^ (2 / 100 : ℝ)) := by rw [hNpow]; ring
    _ ≤ C * (2 * (ζ * Cδ ^ 2 * (1 + 2200 ^ 2))) * 2 ^ (199 / 100 : ℝ) *
          (2 ^ (12 / 1000 : ℝ) * U ^ (264 / 1000 : ℝ)) * (U ^ (1 / 1000 : ℝ) * U ^ (2 / 100 : ℝ)) := by
        gcongr
    _ = C * (K / 2) * (U ^ (1 / 1000 : ℝ) * U ^ (2 / 100 : ℝ) * U ^ (264 / 1000 : ℝ)) := by
        simp only [K]; ring
    _ ≤ C * (2 * K) * U ^ (285 / 1000 : ℝ) := by
        rw [hUU]
        have hK0 : 0 ≤ K := by positivity
        gcongr; linarith

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Zero: the zero-free rectangles (Proposition 8.2, first half)

`rowZeroFree_of_cuts : RowLargeSieve F ι → TwistedConvexity F ι → RowZeroFree F ι`, with
`ρ = min(1/10, 1/(10(|A|+1)))`, `X = U²`, `Y = U^20`, `Z = U^22`, `H = 4U^ρ`, `σ₀ = .996`.
A row with a zero in the rectangle has `rowQ ≥ 1/(8J²)` (`L3Z_Row`), and Chebyshev with the
large sieve (`L3Z_Count`, `L3Z_Mass`) bounds their number by `≪ J³ U^{ρ + .285} ≪ U^{.415}`. -/

open NumberField Complex Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L3Z

attribute [local instance] Classical.propDecidable

/-- Two entire functions agreeing on `Re ξ > 1` are equal. -/
lemma eq_of_entire {Λ Λ' : ℂ → ℂ} (h : Differentiable ℂ Λ) (h' : Differentiable ℂ Λ')
    (he : ∀ ξ : ℂ, 1 < ξ.re → Λ ξ = Λ' ξ) : Λ = Λ' := by
  have hU : IsOpen {ξ : ℂ | 1 < ξ.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {ξ : ℂ | 1 < ξ.re} := by simp
  have hev : Λ =ᶠ[𝓝 (2 : ℂ)] Λ' := by
    filter_upwards [hU.mem_nhds h2] with ξ hξ
    exact he ξ hξ
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := Set.univ)
    (fun z _ => h.analyticAt z) (fun z _ => h'.analyticAt z) isPreconnected_univ
    (Set.mem_univ 2) hev
  funext z; exact this (Set.mem_univ z)

lemma finite_of_card_le {α : Type*} {S : Set α} {M : ℝ}
    (h : ∀ T : Finset α, (↑T : Set α) ⊆ S → (T.card : ℝ) ≤ M) : S.Finite := by
  by_contra hinf
  obtain ⟨T, hT, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊M⌋₊ + 1)
  have := h T hT
  rw [hc] at this
  push_cast at this
  have hM : 0 ≤ M := le_trans (by positivity) this
  linarith [Nat.lt_floor_add_one M]

/-- `J ≤ 3201 U^{1/100}`. -/
lemma numBlocks_le {U : ℝ} (hU : 2 ≤ U) :
    (numBlocks (U ^ (22 : ℝ)) : ℝ) ≤ 3201 * U ^ (1 / 100 : ℝ) := by
  have hU0 : 0 < U := by linarith
  have h1 : (1 : ℝ) ≤ U ^ (1 / 100 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  set m := ⌊U ^ (22 : ℝ)⌋₊
  have hlog : (Nat.log 2 m : ℝ) ≤ 3200 * U ^ (1 / 100 : ℝ) := by
    by_cases hm : m = 0
    · rw [hm]; simp; positivity
    have hp : ((2 : ℝ) ^ Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hm
    have hmZ : (m : ℝ) ≤ U ^ (22 : ℝ) := Nat.floor_le (by positivity)
    have h2 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ 22 * Real.log U := by
      have := Real.log_le_log (by positivity) (hp.trans hmZ)
      rwa [Real.log_pow, Real.log_rpow hU0] at this
    have hl2 := Real.log_two_gt_d9
    have hlU : Real.log U ≤ U ^ (1 / 100 : ℝ) / (1 / 100) := Real.log_le_rpow_div hU0.le (by norm_num)
    have hlU0 : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
    have h3 : (Nat.log 2 m : ℝ) ≤ 22 * Real.log U / Real.log 2 := by
      rw [le_div_iff₀ (by linarith)]; exact h2
    have h4 : 22 * Real.log U / Real.log 2 ≤ 32 * Real.log U := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : U ^ (1 / 100 : ℝ) / (1 / 100) = 100 * U ^ (1 / 100 : ℝ) := by ring
    linarith
  unfold numBlocks
  push_cast
  linarith

variable {F : Type*} [Field F] [NumberField F]

lemma twCoeff_eq_zero_of_not_exterior (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪)
    (u : SInt 𝔪) {n : Ideal (𝓞 F)} (hn : ¬ IsExterior 𝔪 n) : twCoeff ι χ u n = 0 := by
  unfold twCoeff
  have : χ.toFun n = 0 := by
    rw [χ.eq_zero_iff']
    by_contra h
    push Not at h
    exact hn ⟨h.1, h.2⟩
  rw [this, zero_mul]

/-- **One row with a zero.** -/
theorem row_bound (A : ℝ) : ∃ G : ℝ, 0 < G ∧ ∀ (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ →
    ∀ (χ : HeckeChar F 𝔪) (u : SInt 𝔪) (Λ : ℂ → ℂ), Differentiable ℂ Λ →
    (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ u ξ) → ∀ B : ℝ, 0 ≤ B →
    (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 → ‖Λ s‖ ≤ B * (2 + |s.im|) ^ A) →
    ∀ U : ℝ, 2 ≤ U → ∀ ρ₀ : ℂ, 996 / 1000 ≤ ρ₀.re → Λ ρ₀ = 0 → ∀ H : ℝ, 1 / 2 ≤ H →
    |ρ₀.im| ≤ H →
    G * B * (2 + |ρ₀.im|) ^ |A| * (idealsUpTo F (U ^ (2 : ℝ))).card *
      (U ^ (20 : ℝ)) ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 →
    6 * (U ^ (20 : ℝ)) ^ 3 * (U ^ (22 : ℝ)) ^ (-(28 / 10 : ℝ)) * zetaR F (1196 / 1000) ^ 2 ≤ 1 / 8 →
    1 / (8 * (numBlocks (U ^ (22 : ℝ)) : ℝ) ^ 2) ≤
      rowQ F (IsExterior 𝔪) (twCoeff ι χ u) (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) (U ^ (22 : ℝ)) H := by
  obtain ⟨G, hG, hdet⟩ := detector_bound (F := F) A
  refine ⟨G, hG, fun ι 𝔪 h𝔪 χ u Λ hΛd hΛe B hB hΛb U hU ρ₀ h1 hz H hH hγ hsmall htail => ?_⟩
  have hU0 : 0 < U := by linarith
  set a := twCoeff ι χ u
  have hβ : ρ₀.re ≤ 1 := by
    by_contra hb
    push Not at hb
    have := (twistedL_inv_bound (F := F) hb |>.choose_spec.2 ι 𝔪 h𝔪 χ u ρ₀ le_rfl).1
    rw [← hΛe ρ₀ hb] at this
    exact this hz
  have hΛe' : ∀ s : ℂ, 1 < s.re → Λ s = ∑' I : Ideal (𝓞 F), a I * (Ideal.absNorm I : ℂ) ^ (-s) := by
    intro s hs; rw [hΛe s hs, twistedL_eq_tsum]
  have hY1 : (1 : ℝ) ≤ U ^ (20 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  obtain ⟨S, hS, hSb⟩ := hdet a (twCoeff_mul ι χ u) (norm_twCoeff_le ι h𝔪 χ u) (twCoeff_bot ι χ u)
    Λ hΛd hΛe' B hB hΛb ρ₀ h1 hβ hz (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) hY1
  have hX1 : (1 : ℝ) ≤ U ^ (2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hXZ : U ^ (2 : ℝ) ≤ U ^ (22 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlow := lower_bound (twCoeff_mul ι χ u) (norm_twCoeff_le ι h𝔪 χ u) (twCoeff_bot ι χ u)
    (twCoeff_top ι χ u) h1 hX1 hXZ (by positivity) hS
  have hexp : 3 / 4 ≤ Real.exp (-1 / U ^ (20 : ℝ)) := by
    have h4 : (4 : ℝ) ≤ U ^ (20 : ℝ) := by
      calc (4 : ℝ) ≤ 2 ^ (2 : ℝ) := by norm_num
        _ ≤ U ^ (2 : ℝ) := Real.rpow_le_rpow (by norm_num) hU (by norm_num)
        _ ≤ U ^ (20 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have := Real.add_one_le_exp (-1 / U ^ (20 : ℝ))
    have : -1 / U ^ (20 : ℝ) ≥ -1 / 4 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  have hR : 1 / 2 ≤ ‖∑ n ∈ (idealsUpTo F (U ^ (22 : ℝ))).filter
      (fun n => U ^ (2 : ℝ) < (Ideal.absNorm n : ℝ)), detTerm F a (U ^ (2 : ℝ)) (U ^ (20 : ℝ)) ρ₀ n‖ := by
    linarith
  exact row_detect a (IsExterior 𝔪) (fun n hn => twCoeff_eq_zero_of_not_exterior ι χ u hn) hH h1 hβ hγ hR

lemma eventually_small (K a : ℝ) (ha : 0 < a) :
    ∃ U₁ : ℝ, ∀ U : ℝ, U₁ ≤ U → K * U ^ (-a) ≤ 1 / 8 := by
  have h := (tendsto_rpow_neg_atTop ha).const_mul K
  rw [mul_zero] at h
  obtain ⟨U₁, hU₁⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 (1 / 8) (by norm_num))
  exact ⟨U₁, fun U hU => (hU₁ U hU).le⟩

lemma smallPrimesDvd_mono' {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) {𝔪 : Ideal (𝓞 F)}
    (h𝔪 : SmallPrimesDvd N₂ 𝔪) : SmallPrimesDvd N₁ 𝔪 :=
  fun P hP hP0 hN => h𝔪 P hP hP0 (hN.trans h)

/-- **Proposition 8.2, first half, from the two cuts.** -/
theorem rowZeroFree_of_cuts (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ)
    (hLS : RowLargeSieve F ι) (hTC : TwistedConvexity F ι) : RowZeroFree F ι := by
  obtain ⟨N₁, hN₁⟩ := hLS
  obtain ⟨N₂, hN₂⟩ := hTC
  refine ⟨max N₁ N₂, fun 𝔪 h𝔪 hS χ g => ?_⟩
  obtain ⟨P, A, hTCr⟩ := hN₂ 𝔪 h𝔪 (smallPrimesDvd_mono' (le_max_right _ _) hS) χ g
  obtain ⟨C₁, hC₁⟩ := hTCr (1 / 2) (by norm_num)
  obtain ⟨CL, hCL⟩ := hN₁ 𝔪 h𝔪 (smallPrimesDvd_mono' (le_max_left _ _) hS) χ g (1 / 1000)
    (by norm_num)
  obtain ⟨G, hG, hrowb⟩ := row_bound (F := F) A
  obtain ⟨K, hK0, hmass⟩ := block_mass_bound (F := F) (IsExterior 𝔪)
  set ρ : ℝ := min (1 / 10) (1 / (10 * (|A| + 1))) with hρdef
  have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 10 := min_le_left _ _
  have hρA : ρ * |A| ≤ 1 / 10 := by
    have h1 : ρ ≤ 1 / (10 * (|A| + 1)) := min_le_right _ _
    have h2 : ρ * (|A| + 1) ≤ 1 / 10 := by
      rw [le_div_iff₀ (by positivity)] at h1
      have : 1 / (10 * (|A| + 1)) * (10 * (|A| + 1)) = 1 := by field_simp
      nlinarith [abs_nonneg A]
    nlinarith [abs_nonneg A]
  -- constants
  set C₁' := max C₁ 0
  set CL' := max CL 0
  set K₁ : ℝ := G * C₁' * 2 * 6 ^ |A| * zetaR F (11 / 10)
  set K₂ : ℝ := 6 * zetaR F (1196 / 1000) ^ 2
  obtain ⟨U₁, hU₁⟩ := eventually_small K₁ (17 / 10) (by norm_num)
  obtain ⟨U₂, hU₂⟩ := eventually_small K₂ (16 / 10) (by norm_num)
  set K₃ : ℝ := 256 * 3201 ^ 3 * CL' * K
  -- the exceptional set
  let bad : ℝ → Set (FreqClass 𝔪) := fun U => {r | r ≠ principalFreq 𝔪 ∧ r ∉ P ∧
    U ≤ (Ideal.absNorm r.1.1 : ℝ) ∧ (Ideal.absNorm r.1.1 : ℝ) < 2 * U ∧
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ (freqElt g r) ξ) ∧
      ∃ ξ : ℂ, 996 / 1000 ≤ ξ.re ∧ |ξ.im| ≤ 4 * U ^ ρ ∧ Λ ξ = 0}
  set U₀ := max (max U₁ U₂) 2
  -- the count
  have hcount : ∀ U : ℝ, U₀ ≤ U → ∀ T : Finset (FreqClass 𝔪), (↑T : Set _) ⊆ bad U →
      (T.card : ℝ) ≤ K₃ * U ^ (1 / 2 : ℝ) := by
    intro U hU T hT
    have hU2 : 2 ≤ U := (le_max_right _ _).trans hU
    have hU0 : 0 < U := by linarith
    have hU1 : 1 ≤ U := by linarith
    set X := U ^ (2 : ℝ)
    set Y := U ^ (20 : ℝ)
    set Z := U ^ (22 : ℝ)
    set H := 4 * U ^ ρ
    set J := numBlocks Z
    have hUρ : 1 ≤ U ^ ρ := Real.one_le_rpow hU1 hρ0.le
    have hH : 1 / 2 ≤ H := by simp only [H]; linarith
    let ar : FreqClass 𝔪 → Ideal (𝓞 F) → ℂ := fun r => twCoeff ι χ (freqElt g r)
    -- each row of `T` is detected
    have hrow : ∀ r ∈ T, 1 / (8 * (J : ℝ) ^ 2) ≤ rowQ F (IsExterior 𝔪) (ar r) X Y Z H := by
      intro r hr
      obtain ⟨hrp, hrP, -, hrU2, Λ', hΛ'd, hΛ'e, ξ, hξ1, hξ2, hξ0⟩ := hT hr
      obtain ⟨Λ, hΛd, hΛe, hΛb⟩ := hC₁ r hrp hrP
      have hΛΛ' : Λ = Λ' := eq_of_entire hΛd hΛ'd (fun ξ h => by rw [hΛe ξ h, hΛ'e ξ h])
      have hz : Λ ξ = 0 := by rw [hΛΛ']; exact hξ0
      have hq0 : (0 : ℝ) ≤ Ideal.absNorm r.1.1 := Nat.cast_nonneg _
      refine hrowb ι 𝔪 h𝔪 χ (freqElt g r) Λ hΛd hΛe (C₁' * (2 * U)) (by positivity) ?_ U hU2 ξ
        hξ1 hz H hH hξ2 ?_ ?_
      · intro s hs1 hs2
        have hb := hΛb s hs1 hs2
        rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at hb
        have hp : 0 ≤ (2 + |s.im|) ^ A := by positivity
        calc ‖Λ s‖ ≤ C₁ * Ideal.absNorm r.1.1 * (2 + |s.im|) ^ A := hb
          _ ≤ C₁' * (2 * U) * (2 + |s.im|) ^ A := by
            have h1 : C₁ * Ideal.absNorm r.1.1 ≤ C₁' * (2 * U) := by
              calc C₁ * Ideal.absNorm r.1.1 ≤ C₁' * Ideal.absNorm r.1.1 :=
                    mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
                _ ≤ C₁' * (2 * U) := mul_le_mul_of_nonneg_left hrU2.le (le_max_right _ _)
            exact mul_le_mul_of_nonneg_right h1 hp
      · -- the detector integral is small
        have hγ : (2 + |ξ.im|) ^ |A| ≤ 6 ^ |A| * U ^ (1 / 10 : ℝ) := by
          calc (2 + |ξ.im|) ^ |A| ≤ (6 * U ^ ρ) ^ |A| :=
                Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg A)
            _ = 6 ^ |A| * U ^ (ρ * |A|) := by
                rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hU0.le]
            _ ≤ 6 ^ |A| * U ^ (1 / 10 : ℝ) := by
                gcongr
        have hD : ((idealsUpTo F X).card : ℝ) ≤ U ^ (22 / 10 : ℝ) * zetaR F (11 / 10) := by
          have := card_idealsUpTo_le (F := F) (σ := 11 / 10) (by norm_num) (R := X) (by positivity)
            (T12B.summable_absNorm_rpow (by norm_num))
          rw [← Real.rpow_mul hU0.le] at this
          refine this.trans (le_of_eq ?_)
          norm_num
          left; rfl
        have hY : Y ^ (-(1 / 4 : ℝ)) = U ^ (-5 : ℝ) := by
          rw [← Real.rpow_mul hU0.le]; norm_num
        have hz0 : 0 ≤ zetaR F (11 / 10) := tsum_nonneg fun _ => by positivity
        calc G * (C₁' * (2 * U)) * (2 + |ξ.im|) ^ |A| * ((idealsUpTo F X).card : ℝ) * Y ^ (-(1 / 4 : ℝ))
            ≤ G * (C₁' * (2 * U)) * (6 ^ |A| * U ^ (1 / 10 : ℝ)) *
              (U ^ (22 / 10 : ℝ) * zetaR F (11 / 10)) * U ^ (-5 : ℝ) := by
              rw [hY]; gcongr
          _ = K₁ * (U ^ (1 : ℝ) * U ^ (1 / 10 : ℝ) * U ^ (22 / 10 : ℝ) * U ^ (-5 : ℝ)) := by
              simp only [K₁, Real.rpow_one]; ring
          _ = K₁ * U ^ (-(17 / 10) : ℝ) := by
              rw [← Real.rpow_add hU0, ← Real.rpow_add hU0, ← Real.rpow_add hU0]; norm_num
          _ ≤ 1 / 8 := hU₁ U ((le_max_left _ _).trans ((le_max_left _ _).trans hU))
      · have e : 6 * Y ^ 3 * Z ^ (-(28 / 10 : ℝ)) * zetaR F (1196 / 1000) ^ 2 =
            K₂ * U ^ (-(16 / 10) : ℝ) := by
          simp only [K₂, Y, Z]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le]
          have : U ^ ((20 : ℝ) * ((3 : ℕ) : ℝ)) * U ^ ((22 : ℝ) * (-(28 / 10))) =
              U ^ (-(16 / 10) : ℝ) := by
            rw [← Real.rpow_add hU0]; norm_num
          rw [← this]; ring
        rw [e]
        exact hU₂ U ((le_max_right _ _).trans ((le_max_left _ _).trans hU))
    -- the large sieve on each block
    set Λf : ℕ → ℝ := fun j => CL' * ((2 * 2 ^ j : ℝ) + U ^ 2) * ((2 * 2 ^ j : ℝ) * U) ^ (1 / 1000 : ℝ)
    have hΛf : ∀ j, 0 ≤ Λf j := fun j => by positivity
    have hLSj : ∀ j ∈ Finset.range J, ∀ b : Ideal (𝓞 F) → ℂ,
        ∑ r ∈ T, ‖∑ n ∈ blk F (IsExterior 𝔪) X Z j, b n * ar r n‖ ^ 2 ≤
          Λf j * ∑ n ∈ blk F (IsExterior 𝔪) X Z j, ‖b n‖ ^ 2 := by
      intro j _ b
      have h2j : (2 : ℝ) ≤ 2 * 2 ^ j := by
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        linarith
      have h := hCL U (2 * 2 ^ j) hU2 h2j T (fun r hr => (hT hr).2.2.2.1)
        (blk F (IsExterior 𝔪) X Z j) (fun I hI => ⟨(Finset.mem_filter.1 hI).2,
          (mem_blk_bounds hI).2.le⟩) b
      refine h.trans ?_
      have : 0 ≤ ((2 * 2 ^ j : ℝ) + U ^ 2) * ((2 * 2 ^ j : ℝ) * U) ^ (1 / 1000 : ℝ) *
          ∑ n ∈ blk F (IsExterior 𝔪) X Z j, ‖b n‖ ^ 2 := by positivity
      have hC : CL ≤ CL' := le_max_left _ _
      simp only [Λf]
      nlinarith
    have hcb := count_bound T ar (IsExterior 𝔪) (by positivity : (0 : ℝ) ≤ H) Λf hΛf hLSj hrow
    -- bound each block
    have hblock : ∀ j ∈ Finset.range J, 2 * (2 * ((H + H) * (Λf j *
        ∑ n ∈ blk F (IsExterior 𝔪) X Z j, ‖wt F X Y n‖ ^ 2 *
          (1 + Real.log (Ideal.absNorm n : ℝ) ^ 2)))) ≤
        4 * (H + H) * (CL' * K * U ^ (285 / 1000 : ℝ)) := by
      intro j hj
      have h2j : (2 : ℝ) ^ j ≤ Z := by
        rw [Finset.mem_range] at hj
        have hjl : j ≤ Nat.log 2 ⌊Z⌋₊ := Nat.lt_succ_iff.1 hj
        have hZ1 : (1 : ℝ) ≤ Z := Real.one_le_rpow hU1 (by norm_num)
        have hfl : 1 ≤ ⌊Z⌋₊ := Nat.le_floor (by exact_mod_cast hZ1)
        calc (2 : ℝ) ^ j ≤ 2 ^ (Nat.log 2 ⌊Z⌋₊) := pow_le_pow_right₀ (by norm_num) hjl
          _ ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
          _ ≤ Z := Nat.floor_le (by positivity)
      have hm := hmass CL' (le_max_right _ _) U hU2 j h2j
      have hH0 : 0 ≤ H + H := by positivity
      have : (H + H) * (Λf j * ∑ n ∈ blk F (IsExterior 𝔪) X Z j, ‖wt F X Y n‖ ^ 2 *
          (1 + Real.log (Ideal.absNorm n : ℝ) ^ 2)) ≤ (H + H) * (CL' * K * U ^ (285 / 1000 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [Λf, mul_assoc] using hm) hH0
      linarith
    have hsum := (hcb.trans (Finset.sum_le_sum hblock))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    -- the final arithmetic
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast Nat.succ_pos _
    have hJb := numBlocks_le hU2
    have hcard : (T.card : ℝ) ≤ 8 * (J : ℝ) ^ 2 * ((J : ℝ) * (4 * (H + H) *
        (CL' * K * U ^ (285 / 1000 : ℝ)))) := by
      have := hsum
      rw [mul_one_div, div_le_iff₀ (by positivity)] at this
      linarith
    have hHb : H + H ≤ 8 * U ^ (1 / 10 : ℝ) := by
      have : U ^ ρ ≤ U ^ (1 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1 hρ1
      simp only [H]; linarith
    have hpow : (U ^ (1 / 100 : ℝ)) ^ 3 * U ^ (1 / 10 : ℝ) * U ^ (285 / 1000 : ℝ) ≤ U ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_add hU0, ← Real.rpow_add hU0]
      exact Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have hCK : 0 ≤ CL' * K := by positivity
    calc (T.card : ℝ) ≤ 8 * (J : ℝ) ^ 2 * ((J : ℝ) * (4 * (H + H) * (CL' * K * U ^ (285 / 1000 : ℝ)))) :=
          hcard
      _ = 32 * (J : ℝ) ^ 3 * (H + H) * (CL' * K) * U ^ (285 / 1000 : ℝ) := by ring
      _ ≤ 32 * (3201 * U ^ (1 / 100 : ℝ)) ^ 3 * (8 * U ^ (1 / 10 : ℝ)) * (CL' * K) *
            U ^ (285 / 1000 : ℝ) := by gcongr
      _ = K₃ * ((U ^ (1 / 100 : ℝ)) ^ 3 * U ^ (1 / 10 : ℝ) * U ^ (285 / 1000 : ℝ)) := by
          simp only [K₃]; ring
      _ ≤ K₃ * U ^ (1 / 2 : ℝ) := by gcongr
  -- the exceptional sets
  refine ⟨ρ, hρ0, K₃ + P.card, U₀,
    fun U => if h : (bad U).Finite then h.toFinset ∪ P else P, ?_, ?_⟩
  · intro U hU
    have hfin := finite_of_card_le (hcount U hU)
    show ((if h : (bad U).Finite then h.toFinset ∪ P else P).card : ℝ) ≤ _
    rw [dif_pos hfin]
    have h1 : ((hfin.toFinset ∪ P).card : ℝ) ≤ hfin.toFinset.card + P.card := by
      exact_mod_cast Finset.card_union_le _ _
    have h2 := hcount U hU hfin.toFinset (by simp)
    have hU1 : 1 ≤ U := by linarith [le_max_right (max U₁ U₂) 2]
    have h3 : (1 : ℝ) ≤ U ^ (1 / 2 : ℝ) := Real.one_le_rpow hU1 (by norm_num)
    have h4 : (P.card : ℝ) ≤ P.card * U ^ (1 / 2 : ℝ) := by
      nlinarith [(Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)]
    nlinarith
  · intro U hU r hr hU1 hU2 hrE Λ hΛd hΛe ξ hξ1 hξ2 hξ0
    have hfin := finite_of_card_le (hcount U hU)
    change r ∉ (if h : (bad U).Finite then h.toFinset ∪ P else P) at hrE
    rw [dif_pos hfin] at hrE
    have hrP : r ∉ P := fun h => hrE (Finset.mem_union_right _ h)
    apply hrE
    apply Finset.mem_union_left
    rw [Set.Finite.mem_toFinset]
    exact ⟨hr, hrP, hU1, hU2, Λ, hΛd, hΛe, ξ, hξ1, hξ2, hξ0⟩

end L3Z

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Final: ZeroDetector (stub dbe1ee75) from the two cuts

`chk_exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one_of_cuts`: the statement of
`exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one` verbatim, from
`L3Z.RowLargeSieve F ι` (Lemma 8.1 for the rows) and `L3Z.TwistedConvexity F ι` ((8.3) for the
rows). This module does not import the stub; `L3Z_Chk` compares the types. -/

open NumberField

namespace ArtinPrimitiveRoots

theorem chk_exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one_of_cuts (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (hLS : L3Z.RowLargeSieve F ι)
    (hTC : L3Z.TwistedConvexity F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
        ∃ E : ℝ → Finset (FreqClass 𝔪),
          (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪,
            r ≠ principalFreq 𝔪 → U ≤ (Ideal.absNorm r.1.1 : ℝ) →
            (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
            ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < 3 * U ^ ρ} ∧
              (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < 3 * U ^ ρ →
                D ξ * twistedL ι χ (freqElt g r) ξ = 1) ∧
              ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → ‖D ξ‖ ≤ C * U ^ ε :=
  L3Z.zeroDetector_of_rowZeroFree F ι (L3Z.rowZeroFree_of_cuts F ι hLS hTC) hTC

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3Z_Dev: ZeroDetector (Proposition 8.2, dbe1ee75), statement verbatim, from the two draft
cut stubs `…_eq_twistedL_and_norm_le` ((8.3) for the rows) and
`…_sum_norm_sq_sum_mul_conj_residueSymbol_le` (Lemma 8.1 for the rows). Their bodies are
`L3Z.TwistedConvexity` and `L3Z.RowLargeSieve` inlined, so the bridges are definitional. -/

open NumberField

namespace ArtinPrimitiveRoots

theorem exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
        ∃ E : ℝ → Finset (FreqClass 𝔪),
          (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪,
            r ≠ principalFreq 𝔪 → U ≤ (Ideal.absNorm r.1.1 : ℝ) →
            (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
            ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < 3 * U ^ ρ} ∧
              (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < 3 * U ^ ρ →
                D ξ * twistedL ι χ (freqElt g r) ξ = 1) ∧
              ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → ‖D ξ‖ ≤ C * U ^ ε :=
  chk_exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one_of_cuts n hn0 hn F ι
    (exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le n hn0 hn F ι)
    (exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le n hn0 hn F ι)

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
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
        ∃ E : ℝ → Finset (FreqClass 𝔪),
          (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪,
            r ≠ principalFreq 𝔪 → U ≤ (Ideal.absNorm r.1.1 : ℝ) →
            (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
            ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < 3 * U ^ ρ} ∧
              (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < 3 * U ^ ρ →
                D ξ * twistedL ι χ (freqElt g r) ξ = 1) ∧
              ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → ‖D ξ‖ ≤ C * U ^ ε := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one n hn0 hn F ι

end
