-- Prove2me | Definitions.Def_OAIQWSIFP000
-- name    : OAIQWSIFP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:18:46.724042+00:00
-- url     : https://prove2.me/theorems/0e019d22-4812-4e41-9720-99f880a92a00
-- title:
--   OpenAI strict inverse-first-power split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.StrictInverseFirstPower.main`, the statement that normalized univalent maps of the disk satisfy a uniform inverse-first-power integral-means bound with exponent strictly below $1/4$, so the bounded universal spectrum has $B_b(-1) < 1/4$ and Kraetzer's conjectured spectrum fails. The bundle holds OpenAI's Lean definitions, structures and instances from `lean/OAI/Analysis/StrictMeans` (OpenAI, *A strict inverse-first-power bound for univalent functions*, OpenAI Math Release, September 24, 2026, result family 072, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with OpenAI's `@[simp]` lemmas about them.
--
--   Among them: the compact family `DiskFamily` of normalized univalent disk maps and its half-plane model `halfPlaneFunction`; the affine rebasings `rebase` and the weight `halfPlaneQ`; the dyadic sampling operator `dyadicOperator` and its growth exponent `dyadicExponent`; the probability-law condition `AffineProbabilityLaw`; the critical map `criticalMap`, `criticalHeight`, `jacobianExpression` and `jacobianPart`; good targets `GoodPair`; and the measurable rank pairing (`sourcePairingDomain`, `sourcePartner`, `partnerRatio`, `sourceMassDensity`, `badSourceTest`).
--
--   The bundle also contains the lemmas those definitions use in their bodies. Several definitions need the instance `CompactSpace DiskFamily` (continuous functions on the family form a Banach space only with it). Its proof is the Montel–Hurwitz compactness argument for the normalized family, which rests on equicontinuity and therefore on the Koebe distortion theorem, Bieberbach's $|a_2| \le 2$ and Gronwall's coefficient bound. A definitions bundle cannot import theorem statements, so the bundle carries the compactness proof and re-proves those three classical results under different names because the compactness instance of the definitions needs them: `derivative_distortion_disk`, `second_coefficient_le_two_disk` and `pole_coefficient_le_one_disk` (all in `OAI.StrictInverseFirstPower`). They state exactly what the published standalone statements `OAI.StrictInverseFirstPower.derivative_distortion`, `second_coefficient_le_two` and `pole_coefficient_le_one` state. The distinct names let a file import this bundle together with those statements.
--
--   The definitions of the published goal (`disk`, `NormalizedUnivalent`, `BoundedNormalizedUnivalent`, `integralMean`, `growthExponent`, `boundedSpectrum`, `kraetzerPrediction`) are not repeated: the bundle imports them from the published bundle `Def_StrictMeans`. It also imports `ellipseLinear`, `ellipseInverse` and `diskAutomorphism` from the bundle `OAIQWSIFPK000` of the classical statements, and no other bundle.
--
--   The theorems the definitions do not need are proved in the four solutions of this split: three prove the published intermediate statements `OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero`, `ae_bad_base_positive_zero` and `ae_base_positive_le_weighted`, and the fourth proves `OAI.StrictInverseFirstPower.main` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/StrictMeans at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWSIFPK000
import Definitions.Def_StrictMeans

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RectangleLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Complex
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

def complexBox (S a b : ℝ) : Set ℂ := {z | |z.re| ≤ S ∧ a ≤ z.im ∧ z.im ≤ b}

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma norm_sq_sub_complex (w a : ℂ) :
    ‖w - a‖ ^ 2 = ‖w‖ ^ 2 - 2 * (conj a * w).re + ‖a‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_sq_center_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DiffContOnCl ℂ f (ball c |r|)) :
    ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c r := by
  by_cases hr : r = 0
  · simp [hr]
  have hs : ContinuousOn f (sphere c |r|) := hf.2.mono (sphere_subset_closedBall.trans (by
    rw [closure_ball _ (abs_ne_zero.mpr hr)]))
  have hc : ContinuousOn (fun z => (conj (f c) * f z).re) (sphere c |r|) :=
    Complex.continuous_re.comp_continuousOn (hs.const_mul _)
  have hm : Real.circleAverage (fun z => (conj (f c) * f z).re) c r = ‖f c‖ ^ 2 := by
    have hd : DiffContOnCl ℂ (fun z => conj (f c) * f z) (ball c |r|) :=
      ⟨fun z hz => (hf.1 z hz).const_mul _, hf.2.const_mul _⟩
    calc
      _ = (Real.circleAverage (fun z => conj (f c) * f z) c r).re :=
        Complex.reCLM.circleAverage_comp_comm ((hs.const_mul _).circleIntegrable')
      _ = (conj (f c) * f c).re := by rw [hd.circleAverage]
      _ = ‖f c‖ ^ 2 := by
        simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re]
  have hineq := Real.circleAverage_mono
    ((hc.const_mul 2).sub (continuousOn_const (c := ‖f c‖ ^ 2))).circleIntegrable'
    (hs.norm.pow 2).circleIntegrable' (fun z _ => ?_)
  · rw [Real.circleAverage_sub] at hineq
    change Real.circleAverage ((2 : ℝ) • (fun z => (conj (f c) * f z).re)) c r -
      Real.circleAverage (fun _ => ‖f c‖ ^ 2) c r ≤ _ at hineq
    rw [Real.circleAverage_smul, Real.circleAverage_const, hm] at hineq
    · change 2 * ‖f c‖ ^ 2 - ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c r at hineq
      linarith
    · exact (hc.const_mul 2).circleIntegrable'
    · exact circleIntegrable_const _ _ _
  · have hn := sq_nonneg ‖f z - f c‖
    rw [norm_sq_sub_complex] at hn
    change 2 * (conj (f c) * f z).re - ‖f c‖ ^ 2 ≤ ‖f z‖ ^ 2
    linarith

lemma inverse_sq_conj_of_norm_eq {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    conj (z⁻¹ ^ 2) = z ^ 2 / (r : ℂ) ^ 4 := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; linarith
  have hc0 : conj z ≠ 0 := by simpa using hz0
  have hconj : conj z * z = (r : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz, Complex.ofReal_pow]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [map_pow, map_inv₀]
  apply (eq_div_iff (pow_ne_zero 4 hr0)).mpr
  calc
    (conj z)⁻¹ ^ 2 * (r : ℂ) ^ 4 = (conj z)⁻¹ ^ 2 * (conj z * z) ^ 2 := by
      rw [hconj]; ring
    _ = z ^ 2 := by field_simp

lemma norm_sq_inverse_sq_sub {z w : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    ‖w - z⁻¹ ^ 2‖ ^ 2 = ‖w‖ ^ 2 + r⁻¹ ^ 4 - 2 * r⁻¹ ^ 4 * (z ^ 2 * w).re := by
  rw [norm_sq_sub_complex, inverse_sq_conj_of_norm_eq hr hz, norm_pow, norm_inv, hz]
  rw [div_mul_eq_mul_div, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem circleAverage_norm_sq_pole {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball 0 r)) :
    Real.circleAverage (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) 0 r =
      Real.circleAverage (fun z => ‖g z‖ ^ 2) 0 r + r⁻¹ ^ 4 := by
  have hs : ContinuousOn g (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact hg.2.mono (sphere_subset_closedBall.trans (by rw [closure_ball _ hr.ne']))
  have hp : DiffContOnCl ℂ (fun z => z ^ 2 * g z) (ball 0 |r|) := by
    rw [abs_of_pos hr]
    exact ⟨fun z hz => ((differentiableAt_id.pow 2).differentiableWithinAt.mul (hg.1 z hz)),
      (continuousOn_id.pow 2).mul hg.2⟩
  have hpc : CircleIntegrable (fun z => z ^ 2 * g z) 0 r :=
    ((continuousOn_id.pow 2).mul hs).circleIntegrable'
  have hmean : Real.circleAverage (fun z => (z ^ 2 * g z).re) 0 r = 0 := by
    calc
      _ = (Real.circleAverage (fun z => z ^ 2 * g z) 0 r).re :=
        Complex.reCLM.circleAverage_comp_comm hpc
      _ = 0 := by rw [hp.circleAverage]; simp
  have hc : ContinuousOn (fun z => (z ^ 2 * g z).re) (sphere 0 |r|) :=
    Complex.continuous_re.comp_continuousOn ((continuousOn_id.pow 2).mul hs)
  rw [Real.circleAverage_congr_sphere (fun z hz =>
    norm_sq_inverse_sq_sub hr (by simpa only [mem_sphere, dist_zero_right, abs_of_pos hr] using hz))]
  rw [Real.circleAverage_fun_sub, Real.circleAverage_fun_add, Real.circleAverage_const]
  · have hm : Real.circleAverage (fun z => 2 * r⁻¹ ^ 4 * (z ^ 2 * g z).re) 0 r = 0 := by
      change Real.circleAverage ((2 * r⁻¹ ^ 4) • (fun z => (z ^ 2 * g z).re)) 0 r = 0
      rw [Real.circleAverage_smul, hmean, smul_zero]
    rw [hm, sub_zero]
  · exact (hs.norm.pow 2).circleIntegrable'
  · exact circleIntegrable_const _ _ _
  · exact ((hs.norm.pow 2).add continuousOn_const).circleIntegrable'
  · exact (hc.const_mul _).circleIntegrable'

theorem circleAverage_norm_sq_pole_lower {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball 0 r)) :
    r⁻¹ ^ 4 + ‖g 0‖ ^ 2 ≤ Real.circleAverage (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) 0 r := by
  rw [circleAverage_norm_sq_pole hr hg]
  have hm := norm_sq_center_le_circleAverage (r := r) (by simpa only [abs_of_pos hr] using hg)
  linarith

lemma circleAverage_eq_integral_neg_pi {f : ℂ → ℝ} {c : ℂ} {r : ℝ} :
    Real.circleAverage f c r = (2 * Real.pi)⁻¹ *
      ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi), smul_eq_mul,
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ)) (-Real.pi)]
  congr 2 <;> ring

lemma lintegral_circle_eq {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hf : ContinuousOn f (sphere c |r|)) (hpos : ∀ z ∈ sphere c |r|, 0 ≤ f z) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (f (circleMap c r θ))) =
      ENNReal.ofReal (2 * Real.pi * Real.circleAverage f c r) := by
  have hi : IntervalIntegrable (fun θ => f (circleMap c r θ)) volume (-Real.pi) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    exact hf.comp (continuous_circleMap c r).continuousOn (fun θ _ => circleMap_mem_sphere' c r θ)
  rw [circleAverage_eq_integral_neg_pi]
  have he : 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ)) =
      ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
  rw [he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact hi.1.mono_set (Ioo_subset_Ioc_self)
  · filter_upwards with θ
    exact hpos _ (circleMap_mem_sphere' c r θ)

lemma annulus_lintegral_polar_lower {f : ℂ → ℝ≥0∞} {r R : ℝ} (hr : 0 < r) (hf : Measurable f) :
    (∫⁻ ρ in Icc r R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal ρ * f (circleMap 0 ρ θ)) ≤
    ∫⁻ z in {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}, f z := by
  let A : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hpolar (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ in Icc r R ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * f (circleMap 0 p.1 p.2) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      apply le_of_eq
      symm
      apply lintegral_prod
      exact (ENNReal.measurable_ofReal.comp measurable_fst |>.mul
        (hf.comp (by fun_prop [circleMap]))).aemeasurable
    _ = ∫⁻ p : ℝ × ℝ in Icc r R ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * A.indicator f (Complex.polarCoord.symm p) := by
      apply setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [indicator_of_mem, hpolar]
      change r ≤ ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ ≤ R
      rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_of_lt_of_le hr hp.1.1)]
      exact hp.1
    _ ≤ ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * A.indicator f (Complex.polarCoord.symm p) := by
      apply lintegral_mono_set
      exact prod_mono (fun ρ hρ => lt_of_lt_of_le hr hρ.1) Subset.rfl
    _ = ∫⁻ z in A, f z := by
      rw [← lintegral_indicator hA]
      exact Complex.lintegral_comp_polarCoord_symm _
    _ = _ := rfl

lemma radial_pole_integral {r R B : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    (∫ ρ in r..R, 2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + B ^ 2)) =
      Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) + Real.pi * B ^ 2 * (R ^ 2 - r ^ 2) := by
  have hz : (0 : ℝ) ∉ uIcc r R := notMem_uIcc_of_lt hr (hr.trans_le hR)
  have hi₁ := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := (-3 : ℤ)) (Or.inr hz)
  have hi₂ : IntervalIntegrable (fun ρ : ℝ => ρ) volume r R := continuous_id.intervalIntegrable _ _
  have he : (∫ ρ in r..R, 2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + B ^ 2)) =
      ∫ ρ in r..R, 2 * Real.pi * (ρ ^ (-3 : ℤ) + B ^ 2 * ρ) := by
    apply intervalIntegral.integral_congr
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := by intro he; subst ρ; exact hz hρ
    simp only [zpow_neg, zpow_ofNat]
    field_simp
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi₁ (hi₂.const_mul _), intervalIntegral.integral_const_mul,
    integral_zpow (Or.inr ⟨by norm_num, hz⟩), integral_id]
  norm_num
  ring

lemma pole_circle_density_lower {g : ℂ → ℂ} {ρ : ℝ} (hρpos : 0 < ρ)
    (hgd : DiffContOnCl ℂ g (ball 0 ρ)) :
    ENNReal.ofReal (2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2)) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal ρ *
        ENNReal.ofReal (‖g (circleMap 0 ρ θ) - (circleMap 0 ρ θ)⁻¹ ^ 2‖ ^ 2) := by
  have hs : ContinuousOn g (sphere 0 |ρ|) := by
    rw [abs_of_pos hρpos]
    exact hgd.2.mono (sphere_subset_closedBall.trans (by rw [closure_ball _ hρpos.ne']))
  have hsi : ContinuousOn (fun z : ℂ => z⁻¹ ^ 2) (sphere 0 |ρ|) :=
    (continuousOn_id.inv₀ (fun z hz => by
      intro he; change z = 0 at he; subst z; simp only [mem_sphere, dist_self, abs_of_pos hρpos] at hz; linarith)).pow 2
  have hsc : ContinuousOn (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) (sphere 0 |ρ|) :=
    (hs.sub hsi).norm.pow 2
  have he := lintegral_circle_eq hsc (fun _ _ => sq_nonneg _)
  rw [lintegral_const_mul' _ _ (by simp), he]
  rw [← ENNReal.ofReal_mul hρpos.le]
  apply ENNReal.ofReal_le_ofReal
  have hm := circleAverage_norm_sq_pole_lower hρpos hgd
  calc
    _ ≤ (2 * Real.pi * ρ) * Real.circleAverage (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) 0 ρ :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem annulus_pole_area_lower {g : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : r ≤ R)
    (hg : DiffContOnCl ℂ g (ball 0 R)) :
    ENNReal.ofReal (Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) +
      Real.pi * ‖g 0‖ ^ 2 * (R ^ 2 - r ^ 2)) ≤
    ∫⁻ z in {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R},
      ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2) := by
  let A : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hgc : ContinuousOn g A := by
    apply hg.2.mono
    rw [closure_ball _ (hr.trans_le hR).ne']
    exact fun z hz => by simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hic : ContinuousOn (fun z : ℂ => z⁻¹ ^ 2) A :=
    (continuousOn_id.inv₀ (fun z hz => by intro he; change z = 0 at he; subst z; have hh : r ≤ ‖(0 : ℂ)‖ := hz.1; simpa using (hr.not_ge (by simpa using hh)))).pow 2
  let f : ℂ → ℝ≥0∞ := A.indicator (fun z => ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2))
  have hfc : ContinuousOn (fun z => ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2)) A :=
    ENNReal.continuous_ofReal.comp_continuousOn ((hgc.sub hic).norm.pow 2)
  have hfm : Measurable f := by
    have he : f = A.piecewise (fun z => ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2)) (fun _ => 0) := by
      funext z
      by_cases hz : z ∈ A <;> simp [f, hz]
    rw [he]
    exact hfc.measurable_piecewise continuousOn_const hA
  have hp := annulus_lintegral_polar_lower (R := R) hr hfm
  have hpolar : (∫⁻ ρ in Icc r R, ENNReal.ofReal
      (2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2))) ≤
      ∫⁻ ρ in Icc r R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ρ * f (circleMap 0 ρ θ) := by
    apply setLIntegral_mono' measurableSet_Icc
    intro ρ hρ
    have hρpos : 0 < ρ := hr.trans_le hρ.1
    have hgd : DiffContOnCl ℂ g (ball 0 ρ) := hg.mono (ball_subset_ball hρ.2)
    have he (θ : ℝ) : f (circleMap 0 ρ θ) = ENNReal.ofReal (‖g (circleMap 0 ρ θ) - (circleMap 0 ρ θ)⁻¹ ^ 2‖ ^ 2) := by
      apply indicator_of_mem
      change r ≤ ‖circleMap 0 ρ θ‖ ∧ ‖circleMap 0 ρ θ‖ ≤ R
      rw [circleMap_zero, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos hρpos]
      exact hρ
    simp_rw [he]
    exact pole_circle_density_lower hρpos hgd
  have hintegrable : IntegrableOn (fun ρ : ℝ => 2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2)) (Icc r R) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_const.mul continuousOn_id).mul
      (((continuousOn_id.inv₀ (fun ρ hρ => (hr.trans_le hρ.1).ne')).pow 4).add continuousOn_const)
  have hid : (∫⁻ ρ in Icc r R, ENNReal.ofReal
      (2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2))) =
      ENNReal.ofReal (Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) +
        Real.pi * ‖g 0‖ ^ 2 * (R ^ 2 - r ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR, radial_pole_integral hr hR]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
      have hρpos : 0 < ρ := hr.trans_le hρ.1
      positivity
  rw [hid] at hpolar
  calc
    _ ≤ _ := hpolar.trans hp
    _ = _ := by
      apply setLIntegral_congr_fun hA
      exact fun z hz => indicator_of_mem hz _

theorem re_le_of_forall_mem_frontier_re_le {U : Set ℂ} {f : ℂ → ℂ} {C : ℝ}
    (hb : Bornology.IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hc : ∀ z ∈ frontier U, (f z).re ≤ C) {z : ℂ} (hz : z ∈ closure U) :
    (f z).re ≤ C := by
  have he := Complex.differentiable_exp.comp_diffContOnCl hf
  have hn : ‖Complex.exp (f z)‖ ≤ Real.exp C :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hb he
      (fun w hw => by simpa only [Function.comp_apply, Complex.norm_exp] using Real.exp_le_exp.mpr (hc w hw)) hz
  simpa only [Complex.norm_exp, Real.exp_le_exp] using hn

theorem norm_realLinear_le_of_frontier {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {C : ℝ}
    (hb : Bornology.IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hc : ∀ z ∈ frontier U, ‖f z - c * conj (f z)‖ ≤ C)
    {z : ℂ} (hz : z ∈ closure U) (hC : 0 ≤ C) :
    ‖f z - c * conj (f z)‖ ≤ C := by
  let t := f z - c * conj (f z)
  let a := conj t - conj c * t
  have ident (w : ℂ) : (a * w).re = (conj t * (w - c * conj w)).re := by
    simp only [a, sub_mul, mul_sub, sub_re, mul_re, mul_im, conj_re, conj_im]
    ring
  have hbd : ∀ w ∈ frontier U, (a * f w).re ≤ ‖t‖ * C := by
    intro w hw
    rw [ident]
    calc
      (conj t * (f w - c * conj (f w))).re ≤ ‖conj t * (f w - c * conj (f w))‖ :=
        Complex.re_le_norm _
      _ = ‖t‖ * ‖f w - c * conj (f w)‖ := by rw [norm_mul, norm_conj]
      _ ≤ ‖t‖ * C := mul_le_mul_of_nonneg_left (hc w hw) (norm_nonneg _)
  have hd : DiffContOnCl ℂ (fun w => a * f w) U := ⟨fun w hw => (hf.1 w hw).const_mul a, hf.2.const_mul a⟩
  have hh := re_le_of_forall_mem_frontier_re_le hb hd hbd hz
  rw [ident] at hh
  change (conj t * t).re ≤ ‖t‖ * C at hh
  have he : (conj t * t).re = ‖t‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re]
  rw [he] at hh
  change ‖t‖ ≤ C
  nlinarith [norm_nonneg t]

theorem det_complexDerivative (a : ℂ) :
    (a • (1 : ℂ →L[ℝ] ℂ)).det = ‖a‖ ^ 2 := by
  change LinearMap.det (a • (1 : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two,
    ← Complex.normSq_eq_norm_sq]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Complex.normSq_apply]

theorem holomorphic_area {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ f z) (hi : InjOn f s) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖ ^ 2)) = volume (f '' s) := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  have h := lintegral_abs_det_fderiv_eq_addHaar_image volume hs hreal hi
  simpa only [det_complexDerivative, abs_sq] using h

lemma det_ellipseLinear (c : ℂ) :
    (ellipseLinear c).det = 1 - ‖c‖ ^ 2 := by
  change LinearMap.det (ellipseLinear c : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two,
    ← Complex.normSq_eq_norm_sq]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ellipseLinear_apply, Complex.normSq_apply]
  ring

lemma norm_ellipseLinear_lower (c z : ℂ) :
    (1 - ‖c‖) * ‖z‖ ≤ ‖ellipseLinear c z‖ := by
  have hn := norm_sub_le (ellipseLinear c z) (c * conj z)
  rw [ellipseLinear_apply, add_sub_cancel_right, norm_mul, norm_conj] at hn
  rw [ellipseLinear_apply]
  nlinarith

lemma ellipseLinear_inverse {c : ℂ} (hc : ‖c‖ < 1) (z : ℂ) :
    ellipseLinear c (ellipseInverse c z) = z := by
  have hd : (1 - ‖c‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg c]
  have hd' : ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hcconj : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [ellipseLinear_apply, ellipseInverse, map_div₀, map_sub, map_mul,
    Complex.conj_conj, Complex.conj_ofReal]
  field_simp [hd']
  push_cast at hcconj ⊢
  linear_combination -z * hcconj

lemma norm_ellipseInverse_le_two {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) (z : ℂ) :
    ‖ellipseInverse c z‖ ≤ 2 * ‖z‖ := by
  have hn := norm_ellipseLinear_lower c (ellipseInverse c z)
  rw [ellipseLinear_inverse (by linarith) z] at hn
  have hnonneg := norm_nonneg (ellipseInverse c z)
  nlinarith

lemma ellipseInverse_add (c z w : ℂ) :
    ellipseInverse c (z + w) = ellipseInverse c z + ellipseInverse c w := by
  simp only [ellipseInverse, map_add]
  ring

lemma ellipseInverse_linear {c : ℂ} (hc : ‖c‖ < 1) (z : ℂ) :
    ellipseInverse c (ellipseLinear c z) = z := by
  have h := ellipseLinear_inverse hc (ellipseLinear c z)
  have hn := norm_ellipseLinear_lower c (ellipseInverse c (ellipseLinear c z) - z)
  rw [map_sub, h, sub_self, norm_zero] at hn
  have hpos : 0 < 1 - ‖c‖ := sub_pos.mpr hc
  have he : ‖ellipseInverse c (ellipseLinear c z) - z‖ = 0 := by
    nlinarith [norm_nonneg (ellipseInverse c (ellipseLinear c z) - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma volume_ellipse_le {c : ℂ} (hc : ‖c‖ ≤ 1) (s : Set ℂ) :
    volume (ellipseLinear c '' s) ≤ volume s := by
  rw [Measure.addHaar_image_continuousLinearMap]
  have hd : LinearMap.det (ellipseLinear c : ℂ →ₗ[ℝ] ℂ) = 1 - ‖c‖ ^ 2 := det_ellipseLinear c
  rw [hd, abs_of_nonneg (by nlinarith [norm_nonneg c])]
  calc
    ENNReal.ofReal (1 - ‖c‖ ^ 2) * volume s ≤ 1 * volume s := by
      gcongr
      exact_mod_cast (by nlinarith [sq_nonneg ‖c‖] : 1 - ‖c‖ ^ 2 ≤ 1)
    _ = _ := one_mul _

lemma norm_ellipseInverse_eq {c : ℂ} (hc : ‖c‖ < 1) (z : ℂ) :
    ‖ellipseInverse c z‖ = ‖z - c * conj z‖ / (1 - ‖c‖ ^ 2) := by
  have hd : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  simp only [ellipseInverse, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hd]

theorem ellipse_max_annulus {f : ℂ → ℂ} {r R C : ℝ} {c : ℂ}
    (hc : ‖c‖ < 1) (hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f {z | r < ‖z‖ ∧ ‖z‖ < R})
    (hfc : ContinuousOn f {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R → ‖ellipseInverse c (f z)‖ ≤ C)
    {z : ℂ} (hz : r ≤ ‖z‖ ∧ ‖z‖ ≤ R) : ‖ellipseInverse c (f z)‖ ≤ C := by
  by_cases hi : r < ‖z‖ ∧ ‖z‖ < R
  · let U : Set ℂ := {z | r < ‖z‖ ∧ ‖z‖ < R}
    have hcl : closure U ⊆ {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} :=
      closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩)
        ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    have hb : Bornology.IsBounded U :=
      (isBounded_ball (x := (0 : ℂ)) (r := R)).subset (fun w hw => by
        simpa only [mem_ball, dist_zero_right] using hw.2)
    have hfront : ∀ w ∈ frontier U, ‖w‖ = r ∨ ‖w‖ = R := by
      intro w hw
      rcases frontier_inter_subset {w : ℂ | r < ‖w‖} {w : ℂ | ‖w‖ < R} hw with hw | hw
      · exact Or.inl ((frontier_lt_subset_eq continuous_const continuous_norm hw.1).symm)
      · exact Or.inr (frontier_lt_subset_eq continuous_norm continuous_const hw.2)
    have hD : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
    have hm := norm_realLinear_le_of_frontier hb (⟨hf, hfc.mono hcl⟩ : DiffContOnCl ℂ f U)
      (c := c) (C := C * (1 - ‖c‖ ^ 2)) (fun w hw => ?_)
      (subset_closure hi) (mul_nonneg hC hD.le)
    · rw [norm_ellipseInverse_eq hc]
      exact (div_le_iff₀ hD).mpr hm
    · exact (div_le_iff₀ hD).mp (by simpa only [norm_ellipseInverse_eq hc] using hbd w (hfront w hw))
  · apply hbd z
    push Not at hi
    by_cases he : ‖z‖ = r
    · exact Or.inl he
    · exact Or.inr (le_antisymm hz.2 (hi (lt_of_le_of_ne hz.1 (Ne.symm he))))

theorem volume_image_annulus_le {f : ℂ → ℂ} {r R C : ℝ} {c : ℂ}
    (hc : ‖c‖ < 1) (hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f {z | r < ‖z‖ ∧ ‖z‖ < R})
    (hfc : ContinuousOn f {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R → ‖ellipseInverse c (f z)‖ ≤ C) :
    volume (f '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}) ≤ ENNReal.ofReal (Real.pi * C ^ 2) := by
  have hs : f '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} ⊆ ellipseLinear c '' closedBall 0 C := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨ellipseInverse c (f z), ?_, ellipseLinear_inverse hc _⟩
    simpa only [mem_closedBall, dist_zero_right] using ellipse_max_annulus hc hC hf hfc hbd hz
  calc
    _ ≤ volume (ellipseLinear c '' closedBall 0 C) := measure_mono hs
    _ ≤ volume (closedBall 0 C) := volume_ellipse_le hc.le _
    _ = ENNReal.ofReal (Real.pi * C ^ 2) := by
      rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hC]
      have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
        rw [← NNReal.coe_real_pi]
        simp only [ENNReal.ofReal_coe_nnreal]
      rw [hpi, mul_comm]

lemma ellipse_pole_identity {z b : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    ellipseLinear (b * (r : ℂ) ^ 2) z⁻¹ = z⁻¹ + b * z := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; linarith
  have hc0 : conj z ≠ 0 := by simpa using hz0
  have hn : conj z * z = (r : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz, Complex.ofReal_pow]
  rw [ellipseLinear_apply, map_inv₀, ← hn]
  field_simp

lemma ellipse_pole_boundary {h : ℂ → ℂ} {b z : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hz : ‖z‖ = r) (hc : ‖b * (r : ℂ) ^ 2‖ ≤ 1 / 2)
    (hh : ‖h z - b * z‖ ≤ ε * r) :
    ‖ellipseInverse (b * (r : ℂ) ^ 2) (z⁻¹ + h z)‖ ≤ r⁻¹ + 2 * ε * r := by
  have he : z⁻¹ + h z = ellipseLinear (b * (r : ℂ) ^ 2) z⁻¹ + (h z - b * z) := by
    rw [ellipse_pole_identity hr hz]
    ring
  rw [he, ellipseInverse_add, ellipseInverse_linear (by linarith)]
  calc
    _ ≤ ‖z⁻¹‖ + ‖ellipseInverse (b * (r : ℂ) ^ 2) (h z - b * z)‖ := norm_add_le _ _
    _ ≤ r⁻¹ + 2 * ‖h z - b * z‖ := by
      rw [norm_inv, hz]
      exact add_le_add (le_refl _) (norm_ellipseInverse_le_two hc _)
    _ ≤ _ := by linarith

lemma deriv_diffContOnCl_inner {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h (ball 0 1))
    {R : ℝ} (hR : R < 1) : DiffContOnCl ℂ (deriv h) (ball 0 R) := by
  have ha := (hd.analyticOnNhd isOpen_ball).deriv
  refine ⟨ha.differentiableOn.mono (ball_subset_ball hR.le), ha.continuousOn.mono ?_⟩
  exact (closure_ball_subset_closedBall).trans (closedBall_subset_ball hR)

lemma pole_annulus_comparison {h : ℂ → ℂ} {r R C : ℝ} {c : ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    (hr : 0 < r) (hrR : r ≤ R) (hR : R < 1) (hc : ‖c‖ < 1) (hC : 0 ≤ C)
    (hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R →
      ‖ellipseInverse c (z⁻¹ + h z)‖ ≤ C) :
    Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) + Real.pi * ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2) ≤
      Real.pi * C ^ 2 := by
  let A : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hsub : A ⊆ ball 0 1 \ {0} := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using hz.2.trans_lt hR
    · intro he
      have he' : z = 0 := he
      have hh := hz.1
      rw [he', norm_zero] at hh
      linarith
  have hder (z : ℂ) (hz : z ∈ A) :
      HasDerivAt (fun z => z⁻¹ + h z) (deriv h z - z⁻¹ ^ 2) z := by
    have hd' := (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hz).1)).hasDerivAt
    have hn : z ≠ 0 := fun he => (hsub hz).2 he
    have hsum : HasDerivAt (fun w : ℂ => w⁻¹ + h w) (-(z ^ 2)⁻¹ + deriv h z) z :=
      (hasDerivAt_inv hn).add hd'
    convert hsum using 1; simp [inv_pow, sub_eq_add_neg, add_comm]
  have hdG : ∀ z ∈ A, DifferentiableAt ℂ (fun z => z⁻¹ + h z) z :=
    fun z hz => (hder z hz).differentiableAt
  have hU : {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} ⊆ A := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hv := volume_image_annulus_le hc hC
    (fun z hz => (hdG z (hU hz)).differentiableWithinAt)
    (fun z hz => (hdG z hz).continuousAt.continuousWithinAt) hbd
  have hl := annulus_pole_area_lower hr hrR (deriv_diffContOnCl_inner hd hR)
  have he : (∫⁻ z in A, ENNReal.ofReal (‖deriv h z - z⁻¹ ^ 2‖ ^ 2)) =
      volume ((fun z => z⁻¹ + h z) '' A) := by
    rw [← holomorphic_area hA hdG (hi.mono hsub)]
    apply setLIntegral_congr_fun hA
    intro z hz
    dsimp only
    rw [(hder z hz).deriv]
  rw [he] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hl.trans hv)

lemma pole_area_small_radius {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    {R ε : ℝ} (hRpos : 0 < R) (hR : R < 1) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2) ≤ R⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2 := by
  have hd0 := hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), ‖h z - deriv h 0 * z‖ ≤ ε * ‖z‖ := by
    simpa only [h0, sub_zero, smul_eq_mul, mul_comm] using hd0.hasDerivAt.isLittleO.bound hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp he
  have hcont : ContinuousOn (fun z => z⁻¹ + h z) (sphere 0 R) := by
    intro z hz
    have hzR : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hzR; linarith
    exact ((continuousAt_inv₀ hz0).add
      (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa [mem_ball, dist_zero_right, hzR] using hR))).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hcont
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id'.mpr nhdsWithin_le_nhds
  have hts : Tendsto (fun r : ℝ => ‖deriv h 0‖ * r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert ht.pow 2 |>.const_mul ‖deriv h 0‖ using 1; simp
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖deriv h 0‖ * r ^ 2 < 1 / 2 :=
    hts.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have houter : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * M ≤ r⁻¹ :=
    tendsto_inv_nhdsGT_zero.eventually_ge_atTop _
  filter_upwards [eventually_mem_nhdsWithin, ht.eventually (gt_mem_nhds hRpos),
    ht.eventually (gt_mem_nhds hδ), hsmall, houter] with r hr hrR hrδ hsmall houter
  have hrpos : 0 < r := hr
  let c : ℂ := deriv h 0 * (r : ℂ) ^ 2
  have hc : ‖c‖ ≤ 1 / 2 := by
    dsimp [c]
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    exact hsmall.le
  have hC : 0 ≤ r⁻¹ + 2 * ε * r := by positivity
  have hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R →
      ‖ellipseInverse c (z⁻¹ + h z)‖ ≤ r⁻¹ + 2 * ε * r := by
    intro z hz
    rcases hz with hz | hz
    · apply ellipse_pole_boundary hrpos hz hc
      have hb := hδbound (y := z) (by simpa only [dist_zero_right, hz] using hrδ)
      simpa only [hz] using hb
    · calc
        _ ≤ 2 * ‖z⁻¹ + h z‖ := norm_ellipseInverse_le_two hc _
        _ ≤ 2 * M := by
          gcongr
          exact hM z (by simpa only [mem_sphere, dist_zero_right] using hz)
        _ ≤ r⁻¹ + 2 * ε * r := by nlinarith
  have harea := pole_annulus_comparison hd hi hrpos hrR.le hR (by linarith : ‖c‖ < 1) hC hbd
  have hsq : (r⁻¹ + 2 * ε * r) ^ 2 = r⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2 := by
    field_simp
    ring
  rw [hsq] at harea
  have hm : Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2 + ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2)) ≤
      Real.pi * (r⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2) := by
    nlinarith only [harea]
  have hm' := (mul_le_mul_iff_right₀ Real.pi_pos).mp hm
  linarith

lemma pole_coefficient_radius {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    {R : ℝ} (hRpos : 0 < R) (hR : R < 1) :
    ‖deriv h 0‖ ^ 2 * R ^ 2 ≤ R⁻¹ ^ 2 := by
  have hb (ε : ℝ) (hε : 0 < ε) : ‖deriv h 0‖ ^ 2 * R ^ 2 ≤ R⁻¹ ^ 2 + 4 * ε := by
    have hl : Tendsto (fun r : ℝ => ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2)) (𝓝[>] (0 : ℝ))
        (𝓝 (‖deriv h 0‖ ^ 2 * R ^ 2)) := by
      have hc : ContinuousAt (fun r : ℝ => ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2)) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hu : Tendsto (fun r : ℝ => R⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (R⁻¹ ^ 2 + 4 * ε)) := by
      have hc : ContinuousAt (fun r : ℝ => R⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hl hu (pole_area_small_radius hd h0 hi hRpos hR hε)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh := hb (ε / 4) (by positivity)
  linarith

theorem pole_coefficient_le_one_disk {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) :
    ‖deriv h 0‖ ≤ 1 := by
  have hl : Tendsto (fun R : ℝ => ‖deriv h 0‖ ^ 2 * R ^ 2) (𝓝[<] (1 : ℝ))
      (𝓝 (‖deriv h 0‖ ^ 2)) := by
    have hc : ContinuousAt (fun R : ℝ => ‖deriv h 0‖ ^ 2 * R ^ 2) 1 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun R : ℝ => R⁻¹ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun R : ℝ => R⁻¹ ^ 2) 1 :=
      (continuousAt_id.inv₀ one_ne_zero).pow 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ R in 𝓝[<] (1 : ℝ), ‖deriv h 0‖ ^ 2 * R ^ 2 ≤ R⁻¹ ^ 2 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with R hR hRpos
    exact pole_coefficient_radius hd h0 hi hRpos hR
  have hh := le_of_tendsto_of_tendsto hl hu he
  nlinarith [norm_nonneg (deriv h 0)]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RootTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

open Set Filter Metric Complex
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

theorem hasDerivAt_continuous_squareRoot {f g : ℂ → ℂ} {z d : ℂ}
    (hf : HasDerivAt f d z) (hg : ContinuousAt g z) (hg0 : g z ≠ 0)
    (hsq : ∀ᶠ w in 𝓝 z, g w ^ 2 = f w) :
    HasDerivAt g (d / (2 * g z)) z := by
  have hden : g z + g z ≠ 0 := by simpa only [← two_mul] using mul_ne_zero two_ne_zero hg0
  have hd : ∀ᶠ w in 𝓝 z, g w + g z ≠ 0 := (hg.add_const _).eventually_ne hden
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := (hasDerivAt_iff_tendsto_slope.mp hf).div
    ((hg.add_const _).tendsto.mono_left nhdsWithin_le_nhds) hden
  have he : (fun w => slope f z w / (g w + g z)) =ᶠ[𝓝[≠] z] slope g z := by
    filter_upwards [hsq.filter_mono nhdsWithin_le_nhds, hd.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with w hw hwd hwz
    rw [slope_def_field, slope_def_field, ← hw, ← hsq.self_of_nhds]
    field_simp
    ring
  simpa only [← two_mul] using ht.congr' he

theorem exists_holomorphic_squareRoot {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ 2 = f z := by
  have hz : 0 ∉ f '' U := by
    rintro ⟨z, hz, he⟩
    exact hzero z hz he
  obtain ⟨g, hg, hsq⟩ := Complex.exists_continuousOn_pow_eq hc hU hf.continuousOn hz (by decide : 2 ≠ 0)
  refine ⟨g, fun z hz => ?_, fun z _ => hsq z⟩
  have hgn : g z ≠ 0 := by
    intro he
    apply hzero z hz
    rw [← hsq z, he, zero_pow (by decide : 2 ≠ 0)]
  exact (hasDerivAt_continuous_squareRoot (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    (hg.continuousAt (hU.mem_nhds hz)) hgn (Filter.Eventually.of_forall hsq)).differentiableAt.differentiableWithinAt

theorem exists_normalized_holomorphic_squareRoot {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z ∈ U, f z ≠ 0) (ha : a ∈ U) (hfa : f a = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, g z ^ 2 = f z) ∧ g a = 1 := by
  obtain ⟨g, hg, hsq⟩ := exists_holomorphic_squareRoot hU hc hf hzero
  have hga : g a ^ 2 = 1 := (hsq a ha).trans hfa
  have hgn : g a ≠ 0 := by intro he; simp [he] at hga
  refine ⟨fun w => g w / g a, hg.div_const _, ?_, div_self hgn⟩
  intro w hw
  rw [div_pow, hsq w hw, hga, div_one]

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma simplyConnected_disk : IsSimplyConnected (ball (0 : ℂ) 1) := by
  let := (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, by simp⟩
  change SimplyConnectedSpace (ball (0 : ℂ) 1)
  exact inferInstance

lemma sq_mem_disk {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : z ^ 2 ∈ ball (0 : ℂ) 1 := by
  simp only [mem_ball, dist_zero_right, norm_pow] at *
  nlinarith [norm_nonneg z]

lemma mul_dslope_zero (f : ℂ → ℂ) (hf0 : f 0 = 0) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa [hf0, smul_eq_mul] using sub_smul_dslope f (0 : ℂ) z

theorem exists_odd_root_transform {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ^ 2 = dslope f 0 z) ∧
      InjOn (fun z => z * g (z ^ 2)) (ball 0 1) := by
  have hdU : DifferentiableOn ℂ (dslope f 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hd
  have hu0 : dslope f 0 0 = 1 := by simpa using h1
  have hun (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : dslope f 0 z ≠ 0 := by
    intro he
    by_cases hz0 : z = 0
    · simp [hz0, h1] at he
    · apply hz0
      apply hi hz (by simp)
      rw [← mul_dslope_zero f h0 z, he, mul_zero, h0]
  obtain ⟨g, hg, hgsq, hg0⟩ := exists_normalized_holomorphic_squareRoot
    isOpen_ball simplyConnected_disk hdU hun (by simp) hu0
  have hgn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : g z ≠ 0 := by
    intro he
    apply hun z hz
    rw [← hgsq z hz, he, zero_pow (by decide : 2 ≠ 0)]
  refine ⟨g, hg, hg0, hgn, hgsq, ?_⟩
  intro z hz w hw he
  have he2 : z ^ 2 = w ^ 2 := by
    apply hi (sq_mem_disk hz) (sq_mem_disk hw)
    calc f (z ^ 2) = (z * g (z ^ 2)) ^ 2 := by
          rw [mul_pow, hgsq _ (sq_mem_disk hz), mul_dslope_zero f h0]
         _ = (w * g (w ^ 2)) ^ 2 := congrArg (· ^ 2) he
         _ = f (w ^ 2) := by
          rw [mul_pow, hgsq _ (sq_mem_disk hw), mul_dslope_zero f h0]
  dsimp only at he
  rw [he2] at he
  exact mul_right_cancel₀ (hgn _ (sq_mem_disk hw)) he

theorem second_coefficient_le_two_disk {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (dslope f 0) 0‖ ≤ 2 := by
  obtain ⟨g, hg, hg0, hgn, hgsq, hqi⟩ := exists_odd_root_transform hd hi h0 h1
  let v : ℂ → ℂ := fun z => (g z)⁻¹
  have hv : DifferentiableOn ℂ v (ball 0 1) := hg.inv hgn
  have hv0 : v 0 = 1 := by simp [v, hg0]
  let H : ℂ → ℂ := fun z => z * dslope v 0 (z ^ 2)
  have hds : DifferentiableOn ℂ (dslope v 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hv
  have hH : DifferentiableOn ℂ H (ball 0 1) := differentiableOn_id.mul
    (hds.comp (differentiableOn_id.pow 2) (fun _ hz => sq_mem_disk hz))
  have hH0 : H 0 = 0 := by simp [H]
  have hG (z : ℂ) (hz : z ≠ 0) : z⁻¹ + H z = (z * g (z ^ 2))⁻¹ := by
    have hs := sub_smul_dslope v (0 : ℂ) (z ^ 2)
    simp only [sub_zero, smul_eq_mul, hv0] at hs
    dsimp only [H]
    rw [mul_inv_rev]
    dsimp only [v] at hs
    field_simp
    linear_combination hs
  have hGi : InjOn (fun z => z⁻¹ + H z) (ball 0 1 \ {0}) := by
    intro z hz w hw he
    dsimp only at he
    rw [hG z hz.2, hG w hw.2, inv_inj] at he
    exact hqi hz.1 hw.1 he
  have ha := pole_coefficient_le_one_disk hH hH0 hGi
  have hd0 := hg.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hvd : HasDerivAt v (-deriv g 0) 0 := by
    convert hd0.hasDerivAt.inv (hgn 0 (by simp)) using 1
    all_goals first | rfl | simp [hg0]
  have hHd : deriv H 0 = -deriv g 0 := by
    have hp : HasDerivAt (fun z : ℂ => z ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℂ)).pow 2 using 1 <;> first | rfl | norm_num
    have hdss : HasDerivAt (dslope v 0) (deriv (dslope v 0) (0 ^ 2)) (0 ^ 2) :=
      (hds.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ^ 2 ∈ ball 0 1))).hasDerivAt
    have he := (hasDerivAt_id (0 : ℂ)).mul (hdss.comp (0 : ℂ) hp)
    convert he.deriv using 1 <;> first | rfl | simp [hvd.deriv]
  have hud : deriv (dslope f 0) 0 = 2 * deriv g 0 := by
    have he : (fun z => g z ^ 2) =ᶠ[𝓝 (0 : ℂ)] dslope f 0 := by
      filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
      exact hgsq z hz
    have hp : HasDerivAt (fun z => g z ^ 2) (2 * deriv g 0) 0 := by
      convert hd0.hasDerivAt.pow 2 using 1
      all_goals first | rfl | simp [hg0]
    exact (hp.congr_of_eventuallyEq he.symm).deriv
  rw [hHd, norm_neg] at ha
  rw [hud, norm_mul]
  norm_num
  linarith

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DiskAutomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower

noncomputable section

lemma not_eventually_constant_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) :
    ¬ ∀ᶠ w in 𝓝 z, f w = f z := by
  intro h
  have hz := mem_of_mem_nhds hs
  have hh : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hs,
      eventually_mem_nhdsWithin] with w hw hws hwz
    exact hwz (hi hws hz hw)
  exact Filter.Eventually.exists hh |>.elim (fun _ h => h)

lemma analytic_injOn_map_nhds {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) (hf : AnalyticAt ℂ f z) :
    map f (𝓝 z) = 𝓝 (f z) := by
  exact le_antisymm hf.continuousAt
    (hf.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn hs hi))

lemma invFunOn_continuousAt {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) (hf : AnalyticAt ℂ f z) :
    ContinuousAt (invFunOn f s) (f z) := by
  have hz := mem_of_mem_nhds hs
  rw [ContinuousAt, hi.leftInvOn_invFunOn hz, ← analytic_injOn_map_nhds hs hi hf]
  change map (invFunOn f s) (map f (𝓝 z)) ≤ 𝓝 z
  rw [Filter.map_map]
  have hh : (invFunOn f s ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hs] with w hw
    exact hi.leftInvOn_invFunOn hw
  exact (tendsto_congr' hh).mpr tendsto_id

lemma deriv_eventually_ne_zero_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : IsOpen s) (hz : z ∈ s) (hi : InjOn f s) (hf : DifferentiableOn ℂ f s) :
    ∀ᶠ w in 𝓝[≠] z, deriv f w ≠ 0 := by
  have hfa : AnalyticAt ℂ (deriv f) z := (hf.deriv hs).analyticAt (hs.mem_nhds hz)
  refine hfa.eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
  intro hzero
  have he : ∀ᶠ w in 𝓝 z, w ∈ s ∧ deriv f w = 0 :=
    Filter.Eventually.and (hs.mem_nhds hz) hzero
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff.mp he
  have hdiff : DifferentiableOn ℂ f (ball z r) := hf.mono (fun w hw => (hrsub hw).1)
  have hc : ∀ᶠ w in 𝓝 z, f w = f z := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected hdiff
      (fun w hw => (hrsub hw).2) hw (mem_ball_self hr)
  exact not_eventually_constant_of_injOn (hs.mem_nhds hz) hi hc

theorem deriv_ne_zero_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : IsOpen s) (hz : z ∈ s) (hi : InjOn f s) (hf : DifferentiableOn ℂ f s) :
    deriv f z ≠ 0 := by
  let g := invFunOn f s
  have hfa : AnalyticAt ℂ f z := hf.analyticAt (hs.mem_nhds hz)
  have hg : ContinuousAt g (f z) := invFunOn_continuousAt (hs.mem_nhds hz) hi hfa
  have hgz : g (f z) = z := hi.leftInvOn_invFunOn hz
  have himage : f '' s ∈ 𝓝 (f z) := by
    rw [← analytic_injOn_map_nhds (hs.mem_nhds hz) hi hfa]
    exact image_mem_map (hs.mem_nhds hz)
  have hder := deriv_eventually_ne_zero_of_injOn hs hz hi hf
  have hder' : ∀ᶠ w in 𝓝 (f z), g w ≠ z → deriv f (g w) ≠ 0 := by
    have hh := hg.tendsto
    rw [hgz] at hh
    exact hh.eventually (eventually_nhdsWithin_iff.mp hder)
  have hgd : ∀ᶠ w in 𝓝[≠] (f z), DifferentiableAt ℂ g w := by
    filter_upwards [hder'.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds himage, eventually_mem_nhdsWithin]
      with w hd hw hwz
    have hgw : g w ∈ s := invFunOn_mem hw
    have hfg : f (g w) = w := invFunOn_eq hw
    have hgne : g w ≠ z := by
      intro he
      apply hwz
      change w = f z
      rw [← hfg, he]
    have hleft : ∀ᶠ x in 𝓝 (g w), g (f x) = x := by
      filter_upwards [hs.mem_nhds hgw] with x hx
      exact hi.leftInvOn_invFunOn hx
    have hh := (hf.analyticAt (hs.mem_nhds hgw)).hasStrictDerivAt.to_local_left_inverse
      (hd hgne) hleft
    simpa only [hfg] using hh.hasDerivAt.differentiableAt
  have hga := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hg
  have hcomp := hga.differentiableAt.hasDerivAt.comp z (hf.differentiableAt (hs.mem_nhds hz)).hasDerivAt
  have hleft : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hs.mem_nhds hz] with x hx
    exact hi.leftInvOn_invFunOn hx
  have hid : HasDerivAt (g ∘ f) 1 z := (hasDerivAt_id z).congr_of_eventuallyEq hleft
  have he := hcomp.unique hid
  intro hzero
  simp only [hzero, mul_zero] at he
  exact zero_ne_one he

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma second_deriv_eq_twice_dslope {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) :
    deriv (deriv f) 0 = 2 * deriv (dslope f 0) 0 := by
  let u := dslope f 0
  have hu : DifferentiableOn ℂ u (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hd
  have he (z : ℂ) : f z = z * u z + f 0 := by
    have hh := sub_smul_dslope f (0 : ℂ) z
    simp only [sub_zero, smul_eq_mul] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm
  have hder : deriv f =ᶠ[𝓝 (0 : ℂ)] (fun z => u z + z * deriv u z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    have hzU := hu.differentiableAt (isOpen_ball.mem_nhds hz)
    have hp := ((hasDerivAt_id z).mul hzU.hasDerivAt).add_const (f 0)
    have hpf : HasDerivAt f (u z + z * deriv u z) z := by
      convert hp using 1
      all_goals first | rfl | exact funext he | simp
    exact hpf.deriv
  have hu0 := hu.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hu'0 := (hu.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hp := hu0.hasDerivAt.add ((hasDerivAt_id (0 : ℂ)).mul hu'0.hasDerivAt)
  have hpf : HasDerivAt (deriv f) (2 * deriv u 0) 0 := by
    convert hp.congr_of_eventuallyEq hder using 1
    all_goals first | rfl | simp [two_mul]
  exact hpf.deriv

lemma second_deriv_norm_le_four {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (deriv f) 0‖ ≤ 4 := by
  rw [second_deriv_eq_twice_dslope hd, norm_mul]
  have hh := second_coefficient_le_two_disk hd hi h0 h1
  norm_num
  linarith

lemma diskAutomorphism_den_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 + conj a * z ≠ 0 := by
  have hl : ‖conj a * z‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  intro he
  have he' : conj a * z = -1 := by linear_combination he
  rw [he'] at hl
  norm_num at hl

lemma diskAutomorphism_norm_identity (a z : ℂ) :
    ‖1 + conj a * z‖ ^ 2 - ‖a + z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, mul_re, mul_im,
    conj_re, conj_im, one_re, one_im]
  ring

lemma diskAutomorphism_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskAutomorphism a) (ball 0 1) (ball 0 1) := by
  intro z hz
  simp only [mem_ball, dist_zero_right] at *
  have hn := diskAutomorphism_norm_identity a z
  have hp : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hl : ‖a + z‖ < ‖1 + conj a * z‖ := by
    nlinarith [norm_nonneg (a + z), norm_nonneg (1 + conj a * z)]
  dsimp only [diskAutomorphism]
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (diskAutomorphism_den_ne ha hz))]
  exact hl

lemma diskAutomorphism_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskAutomorphism a) (ball 0 1) := by
  intro z hz w hw he
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have haN : 1 - conj a * a ≠ 0 := by
    rw [← normSq_eq_conj_mul_self, ← ofReal_one, ← ofReal_sub, ne_eq, ofReal_eq_zero]
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have he' := (div_eq_div_iff (diskAutomorphism_den_ne ha hz') (diskAutomorphism_den_ne ha hw')).mp he
  have he'' : (1 - conj a * a) * (z - w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp he'').resolve_left haN)

lemma diskAutomorphism_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskAutomorphism a)
      ((1 - conj a * a) / (1 + conj a * z) ^ 2) z := by
  have hh := ((hasDerivAt_id z).const_add a).div
    (((hasDerivAt_id z).const_mul (conj a)).const_add 1) (diskAutomorphism_den_ne ha hz)
  convert hh using 1
  all_goals first | rfl | (dsimp only [id_eq, Function.comp_apply]; ring)

lemma diskAutomorphism_differentiableOn {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (diskAutomorphism a) (ball 0 1) := by
  intro z hz
  exact (diskAutomorphism_hasDerivAt ha (by simpa [mem_ball, dist_zero_right] using hz)).differentiableAt.differentiableWithinAt

lemma diskAutomorphism_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (diskAutomorphism a) 0 = 1 - conj a * a := by
  simpa using (diskAutomorphism_hasDerivAt (z := 0) ha (by simp)).deriv

lemma diskAutomorphism_second_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (deriv (diskAutomorphism a)) 0 = -2 * conj a * (1 - conj a * a) := by
  have he : deriv (diskAutomorphism a) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (1 - conj a * a) / (1 + conj a * z) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    exact (diskAutomorphism_hasDerivAt ha (by simpa [mem_ball, dist_zero_right] using hz)).deriv
  have hn : (1 + conj a * (0 : ℂ)) ^ 2 ≠ 0 := by simp
  have hp := (hasDerivAt_const (0 : ℂ) (1 - conj a * a)).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_add 1).pow 2) hn
  have hpf : HasDerivAt (deriv (diskAutomorphism a)) (-2 * conj a * (1 - conj a * a)) 0 := by
    convert hp.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (simp; ring)
  exact hpf.deriv

lemma second_deriv_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z) :
    deriv (deriv (f ∘ g)) z = deriv (deriv f) (g z) * deriv g z ^ 2 +
      deriv f (g z) * deriv (deriv g) z := by
  have he : deriv (f ∘ g) =ᶠ[𝓝 z] (fun w => deriv f (g w) * deriv g w) := by
    filter_upwards [hg.eventually_analyticAt,
      hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt] with w hgw hfw
    exact deriv_comp w hfw.differentiableAt hgw.differentiableAt
  have hp := (hf.deriv.differentiableAt.hasDerivAt.comp z hg.differentiableAt.hasDerivAt).mul
    hg.deriv.differentiableAt.hasDerivAt
  have hpf : HasDerivAt (deriv (f ∘ g))
      (deriv (deriv f) (g z) * deriv g z ^ 2 + deriv f (g z) * deriv (deriv g) z) z := by
    convert hp.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (dsimp only [id_eq, Function.comp_apply]; ring)
  exact hpf.deriv

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DerivativeDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma second_deriv_normalize {f : ℂ → ℂ} {z b c : ℂ} (hf : AnalyticAt ℂ f z) :
    deriv (deriv (fun w => (f w - b) / c)) z = deriv (deriv f) z / c := by
  have he : deriv (fun w => (f w - b) / c) =ᶠ[𝓝 z] (fun w => deriv f w / c) := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact ((hw.differentiableAt.hasDerivAt.sub_const b).div_const c).deriv
  have hp := hf.deriv.differentiableAt.hasDerivAt.div_const c
  exact (hp.congr_of_eventuallyEq he).deriv

theorem preSchwarzian_bound {f : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : ‖a‖ < 1) :
    ‖(1 - (‖a‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) a / deriv f a) - 2 * conj a‖ ≤ 4 := by
  have ha' : a ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using ha
  have hfn := deriv_ne_zero_of_injOn isOpen_ball ha' hi hd
  let δ : ℂ := 1 - conj a * a
  have hδ : δ ≠ 0 := by
    dsimp only [δ]
    rw [← normSq_eq_conj_mul_self, ← ofReal_one, ← ofReal_sub, ne_eq, ofReal_eq_zero,
      normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  let g : ℂ → ℂ := fun w => (f (diskAutomorphism a w) - f a) / (δ * deriv f a)
  have hφd := diskAutomorphism_differentiableOn ha
  have hφm := diskAutomorphism_mapsTo ha
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    ((hd.comp hφd hφm).sub_const _).div_const _
  have hgi : InjOn g (ball 0 1) := by
    intro z hz w hw he
    apply diskAutomorphism_injOn ha hz hw
    apply hi (hφm hz) (hφm hw)
    exact sub_left_inj.mp ((div_left_inj' (mul_ne_zero hδ hfn)).mp he)
  have hg0 : g 0 = 0 := by simp [g]
  have hφ0 : HasDerivAt (diskAutomorphism a) δ 0 := by
    convert diskAutomorphism_hasDerivAt (z := 0) ha (by simp) using 1; simp [δ]
  have hfa := hd.analyticAt (isOpen_ball.mem_nhds ha')
  have hfac : HasDerivAt f (deriv f a) (diskAutomorphism a 0) := by
    simpa using hfa.differentiableAt.hasDerivAt
  have hg1 : deriv g 0 = 1 := by
    have hp := ((hfac.comp 0 hφ0).sub_const (f a)).div_const (δ * deriv f a)
    convert hp.deriv using 1
    all_goals first | rfl | field_simp
  have hφa := hφd.analyticAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hF : AnalyticAt ℂ (f ∘ diskAutomorphism a) 0 :=
    (show AnalyticAt ℂ f (diskAutomorphism a 0) by simpa using hfa).comp hφa
  have hg2 : deriv (deriv g) 0 = δ * (deriv (deriv f) a / deriv f a) - 2 * conj a := by
    change deriv (deriv (fun w => ((f ∘ diskAutomorphism a) w - f a) /
      (δ * deriv f a))) 0 = _
    rw [second_deriv_normalize hF]
    rw [second_deriv_comp (by simpa using hfa) hφa]
    simp only [diskAutomorphism_zero, diskAutomorphism_deriv_zero ha,
      diskAutomorphism_second_deriv_zero ha]
    dsimp only [δ]
    dsimp only [δ] at hδ
    field_simp
    ring
  have hb := second_deriv_norm_le_four hgd hgi hg0 hg1
  rw [hg2] at hb
  simpa only [δ, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, ofReal_sub, ofReal_pow,
    ofReal_one] using hb

lemma hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}
    (hg : HasDerivAt g g' t) (hn : g t ≠ 0) :
    HasDerivAt (fun s => Real.log ‖g s‖) (g' / g t).re t := by
  have hp := (hg.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).div_const 2
  have he : (fun s => Real.log (‖g s‖ ^ 2) / 2) = (fun s => Real.log ‖g s‖) := by
    funext s
    rw [Real.log_pow]
    ring
  have hv : (2 * inner ℝ (g t) g' / ‖g t‖ ^ 2) / 2 = (g' / g t).re := by
    rw [Complex.inner, Complex.div_re, ← normSq_eq_norm_sq]
    simp only [mul_re, conj_re, conj_im]
    ring
  convert hp using 1
  all_goals first | rfl | exact he.symm | exact hv.symm

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma radial_preSchwarzian_bounds {f : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hu : ‖u‖ = 1) (ht : 0 ≤ t) (ht1 : t < 1) :
    (2 * t - 4) / (1 - t ^ 2) ≤
        (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re ∧
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re ≤
        (2 * t + 4) / (1 - t ^ 2) := by
  have hnorm : ‖(t : ℂ) * u‖ = t := by simp [hu, abs_of_nonneg ht]
  have hsu : conj u * u = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hu]
    norm_num
  have hb := preSchwarzian_bound hd hi (a := (t : ℂ) * u) (by rwa [hnorm])
  rw [hnorm] at hb
  let p : ℂ := deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)
  have he : ((1 - (t ^ 2 : ℝ) : ℂ) * p - 2 * conj ((t : ℂ) * u)) * u =
      (1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ) := by
    simp only [map_mul, conj_ofReal, sub_mul]
    calc
      _ = (1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ) * (conj u * u) := by ring
      _ = _ := by rw [hsu, mul_one]; ring
  have hb' : ‖(1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ)‖ ≤ 4 := by
    rw [← he, norm_mul, hu, mul_one]
    exact hb
  have hh := (Complex.abs_re_le_norm _).trans hb'
  have hh' : |(1 - t ^ 2) * (p * u).re - 2 * t| ≤ 4 := by
    simpa [← ofReal_pow, Complex.mul_re] using hh
  have hp : 0 < 1 - t ^ 2 := by nlinarith
  have hlo := (abs_le.mp hh').1
  have hhi := (abs_le.mp hh').2
  have hval : (p * u).re =
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re := by
    congr 1
    dsimp only [p]
    ring
  rw [← hval]
  constructor
  · exact (div_le_iff₀ hp).mpr (by nlinarith)
  · exact (le_div_iff₀ hp).mpr (by nlinarith)

lemma hasDerivAt_radial_log_deriv {f : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun s : ℝ => Real.log ‖deriv f ((s : ℂ) * u)‖)
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re t := by
  have hdf := (hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hmem)
  have hp := (hdf.hasDerivAt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const u)).comp_ofReal
  apply hasDerivAt_log_norm _ (deriv_ne_zero_of_injOn isOpen_ball hmem hi hd)
  simpa only [Function.comp_apply, id_eq, one_mul] using hp

lemma log_derivative_distortion_radial {f : ℂ → ℂ} {u : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hu : ‖u‖ = 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log (1 - r) - 3 * Real.log (1 + r) ≤ Real.log ‖deriv f ((r : ℂ) * u)‖ ∧
      Real.log ‖deriv f ((r : ℂ) * u)‖ ≤ Real.log (1 + r) - 3 * Real.log (1 - r) := by
  let A : ℝ → ℝ := fun t => Real.log ‖deriv f ((t : ℂ) * u)‖
  let D : ℝ → ℝ := fun t =>
    (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re
  have hrad (t : ℝ) (ht : t ∈ Icc 0 r) : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_zero_right, hu, abs_of_nonneg ht.1] using ht.2.trans_lt hr1
  have hA (t : ℝ) (ht : t ∈ Icc 0 r) : HasDerivAt A (D t) t :=
    hasDerivAt_radial_log_deriv hd hi (hrad t ht)
  have hL (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ => Real.log (1 - s) - 3 * Real.log (1 + s))
        ((2 * t - 4) / (1 - t ^ 2)) t := by
    have hm : 1 - t ≠ 0 := by linarith [ht.2]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hdminus : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hdplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h := (hdminus.log hm).sub ((hdplus.log hp).const_mul 3)
    convert! h using 1
    field_simp
    ring
  have hU (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ => Real.log (1 + s) - 3 * Real.log (1 - s))
        ((2 * t + 4) / (1 - t ^ 2)) t := by
    have hm : 1 - t ≠ 0 := by linarith [ht.2]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hdminus : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hdplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h := (hdplus.log hp).sub ((hdminus.log hm).const_mul 3)
    convert! h using 1
    field_simp
    ring
  have hbounds (t : ℝ) (ht : t ∈ Icc 0 r) :=
    radial_preSchwarzian_bounds hd hi hu ht.1 (ht.2.trans_lt hr1)
  have hmonoL : MonotoneOn (fun t => A t -
      (Real.log (1 - t) - 3 * Real.log (1 + t))) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · exact fun t ht => ((hA t ht).sub (hL t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hA t (interior_subset ht)).sub
        (hL t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (A - (fun s => Real.log (1 - s) - 3 * Real.log (1 + s))) t
      rw [((hA t (interior_subset ht)).sub (hL t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hbounds t (interior_subset ht)).1
  have hmonoU : MonotoneOn (fun t =>
      (Real.log (1 + t) - 3 * Real.log (1 - t)) - A t) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · exact fun t ht => ((hU t ht).sub (hA t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hU t (interior_subset ht)).sub
        (hA t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv ((fun s => Real.log (1 + s) - 3 * Real.log (1 - s)) - A) t
      rw [((hU t (interior_subset ht)).sub (hA t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hbounds t (interior_subset ht)).2
  have hlo := hmonoL (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hhi := hmonoU (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  simp only [A, ofReal_zero, zero_mul, h1, norm_one, Real.log_one, sub_zero, add_zero,
    mul_zero, sub_self] at hlo hhi
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

theorem derivative_distortion_disk {f : ℂ → ℂ} {z : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hz : ‖z‖ < 1) :
    (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  by_cases hz0 : z = 0
  · subst z
    simp [h1]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  let u : ℂ := z / (‖z‖ : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, hr.ne']
  have he : (‖z‖ : ℂ) * u = z := by
    dsimp only [u]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  have hb := log_derivative_distortion_radial hd hi h1 hu hr.le hz
  rw [he] at hb
  have hm : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have hp : 0 < 1 + ‖z‖ := by positivity
  have hdf : 0 < ‖deriv f z‖ := norm_pos_iff.mpr
    (deriv_ne_zero_of_injOn isOpen_ball (by simpa using hz) hi hd)
  have expL : Real.exp (Real.log (1 - ‖z‖) - 3 * Real.log (1 + ‖z‖)) =
      (1 - ‖z‖) / (1 + ‖z‖) ^ 3 := by
    rw [show 3 * Real.log (1 + ‖z‖) = Real.log ((1 + ‖z‖) ^ 3) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_sub, Real.exp_log hm, Real.exp_log (pow_pos hp 3)]
  have expU : Real.exp (Real.log (1 + ‖z‖) - 3 * Real.log (1 - ‖z‖)) =
      (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
    rw [show 3 * Real.log (1 - ‖z‖) = Real.log ((1 - ‖z‖) ^ 3) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_sub, Real.exp_log hp, Real.exp_log (pow_pos hm 3)]
  constructor
  · simpa only [expL, Real.exp_log hdf] using Real.exp_le_exp.mpr hb.1
  · simpa only [expU, Real.exp_log hdf] using Real.exp_le_exp.mpr hb.2

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CompactFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

theorem locallyUniformLimit_zero_eventually {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hzero : ∀ᶠ n in l, ∀ w ∈ U, F n w ≠ 0)
    (hfz : f z = 0) : ∀ᶠ w in 𝓝 z, f w = 0 := by
  have hfd := hlim.differentiableOn hF hU
  have hfa := hfd.analyticAt (hU.mem_nhds hz)
  by_contra hn
  have hnz := hfa.eventually_eq_zero_or_eventually_ne_zero.resolve_left hn
  have hne : ∀ᶠ w in 𝓝 z, w ∈ U ∧ (w ≠ z → f w ≠ 0) :=
    Filter.Eventually.and (hU.mem_nhds hz) (eventually_nhdsWithin_iff.mp hnz)
  obtain ⟨R, hR, hRi⟩ := Metric.eventually_nhds_iff.mp hne
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hc : closedBall z r ⊆ U := fun w hw => (hRi (closedBall_subset_ball hrR hw)).1
  have hsne : ∀ w ∈ sphere z r, f w ≠ 0 := by
    intro w hw
    exact (hRi (closedBall_subset_ball hrR (sphere_subset_closedBall hw))).2
      (ne_of_mem_sphere hw hr.ne')
  have hcont : ContinuousOn (fun w => ‖f w‖) (sphere z r) :=
    (hfd.continuousOn.mono (sphere_subset_closedBall.trans hc)).norm
  obtain ⟨a, ha, hamin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hcont
  let δ := ‖f a‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hsne a ha)
  have hb : ∀ w ∈ sphere z r, δ ≤ ‖f w‖ := fun w hw => hamin hw
  have hu : TendstoUniformlyOn F f l (sphere z r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _
      (sphere_subset_closedBall.trans hc) (isCompact_sphere z r)
  have he1 : ∀ᶠ n in l, ∀ w ∈ sphere z r, dist (f w) (F n w) < δ / 2 :=
    tendstoUniformlyOn_iff.mp hu (δ / 2) (half_pos hδ)
  have hc0 : Tendsto (fun n => ‖F n z‖) l (𝓝 0) := by
    simpa only [hfz, norm_zero] using (hlim.tendsto_at hz).norm
  have he2 : ∀ᶠ n in l, ‖F n z‖ < δ / 2 :=
    hc0.eventually (eventually_lt_nhds (half_pos hδ))
  obtain ⟨n, hfn, hnzero, hnsph, hnz⟩ := (hF.and (hzero.and (he1.and he2))).exists
  have hginv : DifferentiableOn ℂ (fun w => (F n w)⁻¹) U := hfn.inv hnzero
  have hmax : ‖(F n z)⁻¹‖ ≤ 2 / δ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hginv.diffContOnCl_ball hc)
    · intro w hw
      rw [frontier_ball _ hr.ne'] at hw
      have htri := norm_le_norm_add_norm_sub (F n w) (f w)
      rw [norm_sub_rev (F n w) (f w)] at htri
      have hclose : ‖f w - F n w‖ < δ / 2 := by simpa only [dist_eq_norm] using hnsph w hw
      have hl : δ / 2 ≤ ‖F n w‖ := by linarith [hb w hw]
      rw [norm_inv]
      calc
        ‖F n w‖⁻¹ ≤ (δ / 2)⁻¹ := inv_anti₀ (half_pos hδ) hl
        _ = 2 / δ := by field_simp
    · exact subset_closure (mem_ball_self hr)
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (norm_pos_iff.mpr (hnzero z hz)) hδ] at hmax
  linarith

theorem locallyUniformLimit_injOn_or_constant {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ᶠ n in l, InjOn (F n) U) :
    InjOn f U ∨ ∃ c : ℂ, EqOn f (fun _ => c) U := by
  classical
  by_cases hi : InjOn f U
  · exact Or.inl hi
  right
  rw [Set.InjOn] at hi
  push Not at hi
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hi
  have hconst : TendstoUniformlyOn (fun n (_ : ℂ) => F n a) (fun _ => f a) l U := by
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (hlim.tendsto_at ha) ε hε] with n hn w _
    simpa only [dist_comm] using hn
  have hsub : TendstoLocallyUniformlyOn (fun n w => F n w - F n a)
      (fun w => f w - f a) l U :=
    (uniformContinuous_fst.sub uniformContinuous_snd).comp_tendstoLocallyUniformlyOn
      (hlim.prodMk hconst.tendstoLocallyUniformlyOn)
  have hopen : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
  have hb' : b ∈ U \ {a} := ⟨hb, by simpa only [mem_singleton_iff] using hne.symm⟩
  have hd : ∀ᶠ n in l, DifferentiableOn ℂ (fun w => F n w - F n a) (U \ {a}) := by
    filter_upwards [hF] with n hn
    exact (hn.sub_const _).mono sdiff_subset
  have hnonzero : ∀ᶠ n in l, ∀ w ∈ U \ {a}, F n w - F n a ≠ 0 := by
    filter_upwards [hinj] with n hn w hw
    exact sub_ne_zero.mpr (fun he => hw.2 (hn hw.1 ha he))
  have he := locallyUniformLimit_zero_eventually hopen hb' (hsub.mono sdiff_subset)
    hd hnonzero (sub_eq_zero.mpr hab.symm)
  have hfd := hlim.differentiableOn hF hU
  have han : AnalyticOnNhd ℂ (fun w => f w - f a) U :=
    (hfd.analyticOnNhd hU).sub analyticOnNhd_const
  have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hb he
  exact ⟨f a, fun w hw => sub_eq_zero.mp (hz hw)⟩

theorem locallyUniformLimit_injOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hz : z ∈ U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ᶠ n in l, InjOn (F n) U) (hderiv : deriv f z ≠ 0) : InjOn f U := by
  obtain hi | ⟨c, hc⟩ := locallyUniformLimit_injOn_or_constant hU hconn hlim hF hinj
  · exact hi
  exfalso
  have he : f =ᶠ[𝓝 z] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hz) hc
  exact hderiv (he.deriv_eq.trans (deriv_const _ _))

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

abbrev UnitDisk := ball (0 : ℂ) 1

instance instLocallyCompactSpaceElemComplexUnitDisk : LocallyCompactSpace UnitDisk := isOpen_ball.locallyCompactSpace

def diskExtension (f : C(UnitDisk, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ ball (0 : ℂ) 1 then f ⟨z, h⟩ else 0

@[simp] lemma diskExtension_coe (f : C(UnitDisk, ℂ)) (z : UnitDisk) :
    diskExtension f z = f z := by simp [diskExtension]

def DiskNormalized (f : C(UnitDisk, ℂ)) : Prop :=
  DifferentiableOn ℂ (diskExtension f) (ball 0 1) ∧
  InjOn (diskExtension f) (ball 0 1) ∧
  diskExtension f 0 = 0 ∧ deriv (diskExtension f) 0 = 1

abbrev DiskFamily := {f : C(UnitDisk, ℂ) // DiskNormalized f}

lemma diskExtension_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → C(UnitDisk, ℂ)} {f : C(UnitDisk, ℂ)} (h : Tendsto F l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun n => diskExtension (F n)) (diskExtension f) l
      (ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def, diskExtension_coe] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

lemma disk_derivative_bound {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) (h1 : deriv f 0 = 1) {r : ℝ} (hr : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ r) : ‖deriv f z‖ ≤ (1 + r) / (1 - r) ^ 3 := by
  have hzr := hz.trans_lt hr
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hb := (derivative_distortion_disk hd hi h1 hzr).2
  have hp : 0 < 1 - r := sub_pos.mpr hr
  have hden : 0 < (1 - r) ^ 3 := pow_pos hp _
  refine hb.trans (div_le_div₀ (by positivity) (by linarith) hden ?_)
  exact pow_le_pow_left₀ hp.le (by linarith) 3

lemma disk_lipschitz_bound {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) (h1 : deriv f 0 = 1) {r : ℝ} (hr : r < 1)
    {z w : ℂ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖f w - f z‖ ≤ ((1 + r) / (1 - r) ^ 3) * ‖w - z‖ := by
  apply (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
      (fun a ha => hd.differentiableAt (isOpen_ball.mem_nhds (by
        simpa only [mem_ball, dist_zero_right] using
          (show ‖a‖ ≤ r from by simpa only [mem_closedBall, dist_zero_right] using ha).trans_lt hr)))
      (fun a ha => disk_derivative_bound hd hi h1 hr (by
        simpa only [mem_closedBall, dist_zero_right] using ha))
  · simpa using hz
  · simpa using hw

lemma disk_family_pointwise_bounded (z : UnitDisk) :
    ∃ R : ℝ, ∀ f : DiskFamily, ‖f.val z‖ ≤ R := by
  refine ⟨((1 + ‖(z : ℂ)‖) / (1 - ‖(z : ℂ)‖) ^ 3) * ‖(z : ℂ)‖, ?_⟩
  intro f
  have h := disk_lipschitz_bound f.property.1 f.property.2.1 f.property.2.2.2
    (show ‖(z : ℂ)‖ < 1 by simpa only [mem_ball, dist_zero_right] using z.property)
    (z := 0) (w := z) (by simp) (le_refl _)
  simpa only [f.property.2.2.1, diskExtension_coe, sub_zero] using h

lemma disk_family_equicontinuous : Equicontinuous (fun f : DiskFamily => (f.val : UnitDisk → ℂ)) := by
  intro z
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let r := (1 + ‖(z : ℂ)‖) / 2
  have hz : ‖(z : ℂ)‖ < 1 := by simpa only [mem_ball, dist_zero_right] using z.property
  have hzr : ‖(z : ℂ)‖ < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hr0 : 0 < r := (norm_nonneg _).trans_lt hzr
  let C := (1 + r) / (1 - r) ^ 3
  have hC : 0 < C := div_pos (by linarith) (pow_pos (sub_pos.mpr hr) _)
  refine ⟨min (r - ‖(z : ℂ)‖) (ε / C), lt_min (sub_pos.mpr hzr) (div_pos hε hC), ?_⟩
  intro w hw f
  have hw' : ‖(w : ℂ) - z‖ < min (r - ‖(z : ℂ)‖) (ε / C) := by simpa only [Subtype.dist_eq, dist_eq_norm] using hw
  have hwr : ‖(w : ℂ)‖ ≤ r := by
    have ht := norm_le_norm_add_norm_sub (z : ℂ) (w : ℂ)
    rw [norm_sub_rev (z : ℂ) (w : ℂ)] at ht
    linarith [hw'.trans_le (min_le_left _ _)]
  have h := disk_lipschitz_bound f.property.1 f.property.2.1 f.property.2.2.2 hr hzr.le hwr
  rw [diskExtension_coe, diskExtension_coe] at h
  rw [dist_eq_norm, norm_sub_rev]
  refine h.trans_lt ?_
  change C * ‖(w : ℂ) - z‖ < ε
  simpa only [mul_comm] using (lt_div_iff₀ hC).mp (hw'.trans_le (min_le_right _ _))

lemma isClosed_diskNormalized : IsClosed {f : C(UnitDisk, ℂ) | DiskNormalized f} := by
  rw [isClosed_iff_forall_filter]
  intro f l hl hs ht
  let : l.NeBot := hl
  have hlim := diskExtension_tendsto (show Tendsto id l (𝓝 f) from ht)
  have hn : ∀ᶠ g in l, DiskNormalized g := le_principal_iff.mp hs
  have hd : ∀ᶠ g in l, DifferentiableOn ℂ (diskExtension g) (ball 0 1) :=
    hn.mono (fun _ hg => hg.1)
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have h0 : diskExtension f 0 = 0 := by
    apply tendsto_nhds_unique (hlim.tendsto_at hz)
    exact tendsto_const_nhds.congr' (hn.mono fun _ hg => hg.2.2.1.symm)
  have h1 : deriv (diskExtension f) 0 = 1 := by
    apply tendsto_nhds_unique ((hlim.deriv hd isOpen_ball).tendsto_at hz)
    exact tendsto_const_nhds.congr' (hn.mono fun _ hg => hg.2.2.2.symm)
  refine ⟨hlim.differentiableOn hd isOpen_ball, ?_, h0, h1⟩
  apply locallyUniformLimit_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    hz hlim hd (hn.mono fun _ hg => hg.2.1)
  simp only [h1, ne_eq, one_ne_zero, not_false_eq_true]

lemma isCompact_diskNormalized : IsCompact {f : C(UnitDisk, ℂ) | DiskNormalized f} := by
  let : T2Space (UniformOnFun UnitDisk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (Set.eq_univ_iff_forall.mpr fun z =>
      mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have he : Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
      C(UnitDisk, ℂ) → UniformOnFun UnitDisk ℂ {K | IsCompact K}) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(UnitDisk, ℂ) => (f : UnitDisk → ℂ))
    (𝔖 := {K | IsCompact K}) (fun _ hK => hK) he
    (s := {f | DiskNormalized f})
    (fun K _ => disk_family_equicontinuous.equicontinuousOn K)
    (by
      intro K _ z _
      obtain ⟨R, hR⟩ := disk_family_pointwise_bounded z
      refine ⟨closedBall 0 R, isCompact_closedBall _ _, ?_⟩
      intro f hf
      simpa only [mem_closedBall, dist_zero_right] using hR ⟨f, hf⟩)
  rwa [isClosed_diskNormalized.closure_eq] at hc

instance instCompactSpaceDiskFamily : CompactSpace DiskFamily := isCompact_iff_compactSpace.mp isCompact_diskNormalized

instance instMetrizableSpaceDiskFamily : TopologicalSpace.MetrizableSpace DiskFamily :=
  TopologicalSpace.MetrizableSpace.subtype {f : C(UnitDisk, ℂ) | DiskNormalized f}

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

abbrev DiskHolomorphic := {f : C(UnitDisk, ℂ) //
  DifferentiableOn ℂ (diskExtension f) (ball 0 1)}

def diskDerivative (f : DiskHolomorphic) : C(UnitDisk, ℂ) :=
  ⟨fun z => deriv (diskExtension f.val) z,
    (f.property.deriv isOpen_ball).continuousOn.comp_continuous
      continuous_subtype_val (fun z => z.property)⟩

lemma continuous_diskDerivative : Continuous diskDerivative := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
  have h := diskExtension_tendsto (continuous_subtype_val.tendsto f)
  have hd := h.deriv (Eventually.of_forall fun g : DiskHolomorphic => g.property) isOpen_ball
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hd
  exact hd

lemma continuous_diskDerivative_eval :
    Continuous (fun p : DiskHolomorphic × UnitDisk => deriv (diskExtension p.1.val) p.2) := by
  exact continuous_diskDerivative.comp continuous_fst |>.eval continuous_snd

lemma continuous_diskFamily_derivative :
    Continuous (fun p : DiskFamily × UnitDisk => deriv (diskExtension p.1.val) p.2) := by
  exact continuous_diskDerivative_eval.comp
    ((continuous_subtype_val.subtype_mk (fun f => f.property.1)).comp continuous_fst |>.prodMk continuous_snd)

lemma diskFamily_derivative_ne_zero (f : DiskFamily) (z : UnitDisk) :
    deriv (diskExtension f.val) z ≠ 0 := by
  exact deriv_ne_zero_of_injOn isOpen_ball z.property f.property.2.1 f.property.1

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def cayleyToHalfPlane (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem one_sub_ne_zero_of_mem_disk {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    1 - w ≠ 0 := by
  intro h
  have : w = 1 := (sub_eq_zero.mp h).symm
  simp [this] at hw

theorem cayley_im_mul_norm_sq {w : ℂ} (hw : 1 - w ≠ 0) :
    (cayleyToHalfPlane w).im * ‖1 - w‖ ^ 2 = 1 - ‖w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [cayleyToHalfPlane, Complex.div_im]
  have hsq : Complex.normSq (1 - w) ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
  field_simp
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem cayley_mem_halfPlane {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    0 < (cayleyToHalfPlane w).im := by
  have hn : ‖w‖ < 1 := by simpa using hw
  have h := cayley_im_mul_norm_sq (one_sub_ne_zero_of_mem_disk hw)
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hp := lt_of_lt_of_eq hpos h.symm
  exact (mul_pos_iff.mp hp).resolve_right (by
    rintro ⟨_, hs⟩
    exact (not_lt_of_ge (sq_nonneg ‖1 - w‖)) hs) |>.1

theorem cayley_differentiableOn :
    DifferentiableOn ℂ cayleyToHalfPlane (ball 0 1) := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · exact fun w hw => one_sub_ne_zero_of_mem_disk hw

def cayleyToDisk (z : ℂ) : ℂ := (z - I) / (z + I)

lemma add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

lemma cayleyToDisk_mem {z : ℂ} (hz : 0 < z.im) :
    cayleyToDisk z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right, cayleyToDisk, norm_div,
    div_lt_one (norm_pos_iff.mpr (add_I_ne_zero hz))]
  have hsq : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [normSq_apply, add_re, I_re, add_zero, add_im, I_im,
      sub_re, sub_zero, sub_im]
    ring
  nlinarith [norm_nonneg (z + I), norm_nonneg (z - I)]

@[simp] lemma cayleyToDisk_I : cayleyToDisk I = 0 := by simp [cayleyToDisk]
@[simp] lemma cayleyToHalfPlane_zero : cayleyToHalfPlane 0 = I := by simp [cayleyToHalfPlane]

lemma cayleyToHalfPlane_toDisk {z : ℂ} (hz : 0 < z.im) :
    cayleyToHalfPlane (cayleyToDisk z) = z := by
  have hd := add_I_ne_zero hz
  have hi := one_sub_ne_zero_of_mem_disk (cayleyToDisk_mem hz)
  dsimp only [cayleyToHalfPlane, cayleyToDisk] at hi ⊢
  field_simp
  ring

lemma cayleyToDisk_toHalfPlane {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    cayleyToDisk (cayleyToHalfPlane w) = w := by
  have hd := one_sub_ne_zero_of_mem_disk hw
  have hi := add_I_ne_zero (cayley_mem_halfPlane hw)
  dsimp only [cayleyToDisk, cayleyToHalfPlane] at hi ⊢
  field_simp
  ring

lemma cayleyToDisk_hasDerivAt {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt cayleyToDisk (2 * I / (z + I) ^ 2) z := by
  convert! ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I)
    (add_I_ne_zero hz) using 1; simp
  ring

lemma cayleyToHalfPlane_hasDerivAt {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasDerivAt cayleyToHalfPlane (2 * I / (1 - w) ^ 2) w := by
  convert! (((hasDerivAt_id w).const_add 1).const_mul I).div
    ((hasDerivAt_id w).const_sub 1) (one_sub_ne_zero_of_mem_disk hw) using 1;
    simp
  ring

lemma cayleyToDisk_differentiableOn :
    DifferentiableOn ℂ cayleyToDisk {z : ℂ | 0 < z.im} :=
  fun _ hz => (cayleyToDisk_hasDerivAt hz).differentiableAt.differentiableWithinAt

lemma cayleyToDisk_injOn : InjOn cayleyToDisk {z : ℂ | 0 < z.im} := by
  intro z hz w hw h
  have := congrArg cayleyToHalfPlane h
  simpa only [cayleyToHalfPlane_toDisk hz, cayleyToHalfPlane_toDisk hw] using this

lemma cayleyToHalfPlane_injOn : InjOn cayleyToHalfPlane (ball 0 1) := by
  intro z hz w hw h
  have := congrArg cayleyToDisk h
  simpa only [cayleyToDisk_toHalfPlane hz, cayleyToDisk_toHalfPlane hw] using this

def affineAt (z : UpperHalfPlane) (w : ℂ) : ℂ := z.re + (z.im : ℂ) * w

@[simp] lemma affineAt_im (z : UpperHalfPlane) (w : ℂ) :
    (affineAt z w).im = z.im * w.im := by simp [affineAt]

@[simp] lemma affineAt_re (z : UpperHalfPlane) (w : ℂ) :
    (affineAt z w).re = z.re + z.im * w.re := by simp [affineAt]

lemma affineAt_mapsTo (z : UpperHalfPlane) :
    MapsTo (affineAt z) {w : ℂ | 0 < w.im} {w : ℂ | 0 < w.im} := by
  intro w hw
  simpa only [mem_ofPred_eq, affineAt_im] using mul_pos z.im_pos hw

lemma affineAt_injective (z : UpperHalfPlane) : Injective (affineAt z) := by
  intro a b hab
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr z.im_ne_zero) (add_left_cancel hab)

lemma affineAt_hasDerivAt (z : UpperHalfPlane) (w : ℂ) :
    HasDerivAt (affineAt z) (z.im : ℂ) w := by
  convert! ((hasDerivAt_id w).const_mul (z.im : ℂ)).const_add (z.re : ℂ) using 1
  simp

@[simp] lemma affineAt_I (z : UpperHalfPlane) : affineAt z I = z := z.re_add_im

@[simp] lemma affineAt_one (w : ℂ) : affineAt UpperHalfPlane.I w = w := by
  simp [affineAt]

def affineProduct (z w : UpperHalfPlane) : UpperHalfPlane :=
  ⟨affineAt z w, affineAt_mapsTo z w.im_pos⟩

@[simp] lemma coe_affineProduct (z w : UpperHalfPlane) :
    (affineProduct z w : ℂ) = affineAt z w := rfl

def affineInverse (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(-(z.re : ℂ) + I) / (z.im : ℂ), by
    simpa [Complex.div_im, pow_two] using
      (div_pos z.im_pos (sq_pos_of_pos z.im_pos))⟩

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def halfPlaneFunction (f : DiskFamily) (z : ℂ) : ℂ :=
  2 * I * diskExtension f.val (cayleyToDisk z)

lemma halfPlaneFunction_differentiableOn (f : DiskFamily) :
    DifferentiableOn ℂ (halfPlaneFunction f) {z : ℂ | 0 < z.im} := by
  exact (f.property.1.comp cayleyToDisk_differentiableOn
    (fun _ hz => cayleyToDisk_mem hz)).const_mul (2 * I)

lemma halfPlaneFunction_injOn (f : DiskFamily) :
    InjOn (halfPlaneFunction f) {z : ℂ | 0 < z.im} := by
  intro z hz w hw h
  apply cayleyToDisk_injOn hz hw
  apply f.property.2.1 (cayleyToDisk_mem hz) (cayleyToDisk_mem hw)
  exact mul_left_cancel₀ (by simp : (2 : ℂ) * I ≠ 0) h

@[simp] lemma halfPlaneFunction_I (f : DiskFamily) : halfPlaneFunction f I = 0 := by
  simp [halfPlaneFunction, f.property.2.2.1]

lemma halfPlaneFunction_hasDerivAt (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (halfPlaneFunction f)
      (2 * I * (deriv (diskExtension f.val) (cayleyToDisk z) *
        (2 * I / (z + I) ^ 2))) z := by
  exact ((f.property.1.differentiableAt
    (isOpen_ball.mem_nhds (cayleyToDisk_mem hz))).hasDerivAt.comp z
      (cayleyToDisk_hasDerivAt hz)).const_mul (2 * I)

lemma halfPlaneFunction_deriv (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    deriv (halfPlaneFunction f) z =
      2 * I * (deriv (diskExtension f.val) (cayleyToDisk z) *
        (2 * I / (z + I) ^ 2)) :=
  (halfPlaneFunction_hasDerivAt f hz).deriv

@[simp] lemma halfPlaneFunction_deriv_I (f : DiskFamily) :
    deriv (halfPlaneFunction f) I = 1 := by
  rw [halfPlaneFunction_deriv f (by simp), cayleyToDisk_I, f.property.2.2.2]
  field_simp
  norm_num [Complex.I_sq]

lemma halfPlaneFunction_deriv_ne_zero (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    deriv (halfPlaneFunction f) z ≠ 0 := by
  rw [halfPlaneFunction_deriv f hz]
  exact mul_ne_zero (by simp) (mul_ne_zero
    (diskFamily_derivative_ne_zero f ⟨_, cayleyToDisk_mem hz⟩)
    (div_ne_zero (by simp) (pow_ne_zero _ (add_I_ne_zero hz))))

def cayleyDiskMap : C(UpperHalfPlane, UnitDisk) :=
  ⟨fun z => ⟨cayleyToDisk z, cayleyToDisk_mem z.im_pos⟩,
    ((cayleyToDisk_differentiableOn.continuousOn.comp_continuous
      UpperHalfPlane.continuous_coe (fun z => z.im_pos))).subtype_mk _⟩

lemma continuous_halfPlaneFunction :
    Continuous (fun p : DiskFamily × UpperHalfPlane => halfPlaneFunction p.1 p.2) := by
  have h : Continuous (fun p : DiskFamily × UpperHalfPlane =>
      2 * I * p.1.val (cayleyDiskMap p.2)) :=
    continuous_const.mul ((continuous_subtype_val.comp continuous_fst).eval
      (cayleyDiskMap.continuous.comp continuous_snd))
  exact h.congr (fun p => by
    simp only [halfPlaneFunction, cayleyDiskMap, ContinuousMap.coe_mk,
      diskExtension, dite_eq_left (cayleyToDisk_mem p.2.im_pos)])

lemma continuous_halfPlaneFunction_deriv :
    Continuous (fun p : DiskFamily × UpperHalfPlane => deriv (halfPlaneFunction p.1) p.2) := by
  have hh : (fun p : DiskFamily × UpperHalfPlane => deriv (halfPlaneFunction p.1) p.2) =
      fun p => 2 * I * (deriv (diskExtension p.1.val) (cayleyToDisk p.2) *
        (2 * I / ((p.2 : ℂ) + I) ^ 2)) := by
    funext p
    exact halfPlaneFunction_deriv p.1 p.2.im_pos
  rw [hh]
  apply Continuous.mul continuous_const
  apply Continuous.mul
  · exact continuous_diskFamily_derivative.comp
      (continuous_fst.prodMk (cayleyDiskMap.continuous.comp continuous_snd))
  · apply Continuous.div continuous_const
    · exact ((UpperHalfPlane.continuous_coe.comp continuous_snd).add continuous_const).pow 2
    · intro p
      exact pow_ne_zero _ (add_I_ne_zero p.2.im_pos)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Rebasing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isOpen_halfPlane : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

lemma halfPlaneFunction_hasDeriv (f : DiskFamily) (z : UpperHalfPlane) :
    HasDerivAt (halfPlaneFunction f) (deriv (halfPlaneFunction f) z) z :=
  ((halfPlaneFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds z.im_pos)).hasDerivAt

def rebaseDiskFunction (f : DiskFamily) (z : UpperHalfPlane) (w : ℂ) : ℂ :=
  (halfPlaneFunction f (affineAt z (cayleyToHalfPlane w)) - halfPlaneFunction f z) /
    (2 * I * z.im * deriv (halfPlaneFunction f) z)

lemma rebase_den_ne_zero (f : DiskFamily) (z : UpperHalfPlane) :
    2 * I * z.im * deriv (halfPlaneFunction f) z ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by simp) (Complex.ofReal_ne_zero.mpr z.im_ne_zero))
    (halfPlaneFunction_deriv_ne_zero f z.im_pos)

lemma rebaseDiskFunction_differentiableOn (f : DiskFamily) (z : UpperHalfPlane) :
    DifferentiableOn ℂ (rebaseDiskFunction f z) (ball 0 1) := by
  have ha : DifferentiableOn ℂ (fun w => affineAt z (cayleyToHalfPlane w)) (ball 0 1) :=
    (cayley_differentiableOn.const_mul (z.im : ℂ)).const_add (z.re : ℂ)
  exact ((halfPlaneFunction_differentiableOn f).comp ha
    (fun w hw => affineAt_mapsTo z (cayley_mem_halfPlane hw))).sub_const _ |>.div_const _

lemma rebaseDiskFunction_injOn (f : DiskFamily) (z : UpperHalfPlane) :
    InjOn (rebaseDiskFunction f z) (ball 0 1) := by
  intro a ha b hb hab
  apply cayleyToHalfPlane_injOn ha hb
  apply affineAt_injective z
  apply halfPlaneFunction_injOn f
    (affineAt_mapsTo z (cayley_mem_halfPlane ha))
    (affineAt_mapsTo z (cayley_mem_halfPlane hb))
  exact sub_left_injective
    ((div_left_inj' (rebase_den_ne_zero f z)).mp hab)

@[simp] lemma rebaseDiskFunction_zero (f : DiskFamily) (z : UpperHalfPlane) :
    rebaseDiskFunction f z 0 = 0 := by
  simp [rebaseDiskFunction]

lemma rebaseDiskFunction_hasDerivAt_zero (f : DiskFamily) (z : UpperHalfPlane) :
    HasDerivAt (rebaseDiskFunction f z) 1 0 := by
  have hc : HasDerivAt cayleyToHalfPlane (2 * I) 0 := by
    simpa using cayleyToHalfPlane_hasDerivAt (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  have ha : HasDerivAt (fun w : ℂ => affineAt z (cayleyToHalfPlane w))
      ((z.im : ℂ) * (2 * I)) 0 :=
    (affineAt_hasDerivAt z (cayleyToHalfPlane 0)).comp 0 hc
  have hf' : HasDerivAt (halfPlaneFunction f) (deriv (halfPlaneFunction f) z)
      (affineAt z (cayleyToHalfPlane 0)) := by simpa using halfPlaneFunction_hasDeriv f z
  have hf := hf'.comp (0 : ℂ) ha
  have hh : HasDerivAt (rebaseDiskFunction f z)
      ((deriv (halfPlaneFunction f) z * ((z.im : ℂ) * (2 * I))) /
        (2 * I * z.im * deriv (halfPlaneFunction f) z)) 0 :=
    (hf.sub_const (halfPlaneFunction f z)).div_const _
  convert! hh using 1
  field_simp [halfPlaneFunction_deriv_ne_zero f z.im_pos,
    Complex.ofReal_ne_zero.mpr z.im_ne_zero]

def rebaseDiskMap (f : DiskFamily) (z : UpperHalfPlane) : C(UnitDisk, ℂ) :=
  ⟨fun w => rebaseDiskFunction f z w,
    (rebaseDiskFunction_differentiableOn f z).continuousOn.comp_continuous
      continuous_subtype_val (fun w => w.property)⟩

lemma rebaseDiskMap_extension (f : DiskFamily) (z : UpperHalfPlane) {w : ℂ}
    (hw : w ∈ ball 0 1) :
    diskExtension (rebaseDiskMap f z) w = rebaseDiskFunction f z w := by
  simp only [diskExtension, dite_eq_left hw, rebaseDiskMap, ContinuousMap.coe_mk]

lemma rebaseDiskMap_normalized (f : DiskFamily) (z : UpperHalfPlane) :
    DiskNormalized (rebaseDiskMap f z) := by
  have he : EqOn (diskExtension (rebaseDiskMap f z)) (rebaseDiskFunction f z) (ball 0 1) :=
    fun _ hw => rebaseDiskMap_extension f z hw
  refine ⟨(rebaseDiskFunction_differentiableOn f z).congr he,
    fun a ha b hb hab => rebaseDiskFunction_injOn f z ha hb ?_, ?_, ?_⟩
  · simpa only [he ha, he hb] using hab
  · rw [he (mem_ball_self zero_lt_one), rebaseDiskFunction_zero]
  · exact ((rebaseDiskFunction_hasDerivAt_zero f z).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)) he)).deriv

def rebase (f : DiskFamily) (z : UpperHalfPlane) : DiskFamily :=
  ⟨rebaseDiskMap f z, rebaseDiskMap_normalized f z⟩

lemma halfPlaneFunction_rebase (f : DiskFamily) (z : UpperHalfPlane) {w : ℂ}
    (hw : 0 < w.im) :
    halfPlaneFunction (rebase f z) w =
      (halfPlaneFunction f (affineAt z w) - halfPlaneFunction f z) /
        ((z.im : ℂ) * deriv (halfPlaneFunction f) z) := by
  change 2 * I * diskExtension (rebaseDiskMap f z) (cayleyToDisk w) = _
  rw [rebaseDiskMap_extension f z (cayleyToDisk_mem hw)]
  unfold rebaseDiskFunction
  rw [cayleyToHalfPlane_toDisk hw]
  field_simp

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def cayleyHalfPlaneMap : C(UnitDisk, UpperHalfPlane) :=
  ⟨fun w => ⟨cayleyToHalfPlane w, cayley_mem_halfPlane w.property⟩,
    (cayley_differentiableOn.continuousOn.comp_continuous continuous_subtype_val
      (fun w => w.property)).upperHalfPlaneMk _⟩

lemma continuous_affineProduct :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane => affineProduct p.1 p.2) := by
  exact ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp continuous_fst)).add
    ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_fst)).mul
      (UpperHalfPlane.continuous_coe.comp continuous_snd))).upperHalfPlaneMk _

lemma continuous_rebaseDiskFunction :
    Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      rebaseDiskFunction p.1.1 p.1.2 p.2) := by
  have ht : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      affineProduct p.1.2 (cayleyHalfPlaneMap p.2)) :=
    continuous_affineProduct.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (cayleyHalfPlaneMap.continuous.comp continuous_snd))
  have hf := continuous_halfPlaneFunction.comp
    ((continuous_fst.comp continuous_fst).prodMk ht)
  have hz : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      halfPlaneFunction p.1.1 p.1.2) := continuous_halfPlaneFunction.comp continuous_fst
  have hd : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      deriv (halfPlaneFunction p.1.1) p.1.2) := continuous_halfPlaneFunction_deriv.comp continuous_fst
  have hy : Continuous (fun p : (DiskFamily × UpperHalfPlane) × UnitDisk =>
      (p.1.2.im : ℂ)) := Complex.continuous_ofReal.comp
    (UpperHalfPlane.continuous_im.comp (continuous_snd.comp continuous_fst))
  exact (hf.sub hz).div ((continuous_const.mul hy).mul hd)
    (fun p => rebase_den_ne_zero p.1.1 p.1.2)

lemma continuous_rebase :
    Continuous (fun p : DiskFamily × UpperHalfPlane => rebase p.1 p.2) := by
  exact (ContinuousMap.continuous_of_continuous_uncurry
    (fun p : DiskFamily × UpperHalfPlane => rebaseDiskMap p.1 p.2)
    continuous_rebaseDiskFunction).subtype_mk _

lemma halfPlaneFunction_of_cayley (f : DiskFamily) {w : ℂ} (hw : w ∈ ball 0 1) :
    halfPlaneFunction f (cayleyToHalfPlane w) = 2 * I * diskExtension f.val w := by
  simp only [halfPlaneFunction, cayleyToDisk_toHalfPlane hw]

lemma diskFamily_ext {f g : DiskFamily}
    (h : ∀ z : UpperHalfPlane, halfPlaneFunction f z = halfPlaneFunction g z) : f = g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  have he := h (cayleyHalfPlaneMap w)
  change halfPlaneFunction f (cayleyToHalfPlane w) =
    halfPlaneFunction g (cayleyToHalfPlane w) at he
  rw [halfPlaneFunction_of_cayley f w.property, halfPlaneFunction_of_cayley g w.property,
    diskExtension_coe, diskExtension_coe] at he
  exact mul_left_cancel₀ (by simp : (2 : ℂ) * I ≠ 0) he

lemma halfPlaneFunction_rebase_deriv (f : DiskFamily) (z w : UpperHalfPlane) :
    deriv (halfPlaneFunction (rebase f z)) w =
      deriv (halfPlaneFunction f) (affineProduct z w) / deriv (halfPlaneFunction f) z := by
  have hf := (halfPlaneFunction_hasDeriv f (affineProduct z w)).comp (w : ℂ)
    (affineAt_hasDerivAt z w)
  have hh := (hf.sub_const (halfPlaneFunction f z)).div_const
    ((z.im : ℂ) * deriv (halfPlaneFunction f) z)
  have he : halfPlaneFunction (rebase f z) =ᶠ[𝓝 (w : ℂ)]
      fun u => (halfPlaneFunction f (affineAt z u) - halfPlaneFunction f z) /
        ((z.im : ℂ) * deriv (halfPlaneFunction f) z) :=
    Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds w.im_pos)
      (fun u hu => halfPlaneFunction_rebase f z hu)
  rw [(hh.congr_of_eventuallyEq he).deriv]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]

def halfPlaneQ (f : DiskFamily) (z : UpperHalfPlane) : ℂ :=
  (deriv (halfPlaneFunction f) z)⁻¹

@[simp] lemma halfPlaneQ_I (f : DiskFamily) : halfPlaneQ f UpperHalfPlane.I = 1 := by
  simp [halfPlaneQ]

lemma halfPlaneQ_rebase (f : DiskFamily) (z w : UpperHalfPlane) :
    halfPlaneQ (rebase f z) w = halfPlaneQ f (affineProduct z w) / halfPlaneQ f z := by
  simp only [halfPlaneQ, halfPlaneFunction_rebase_deriv, inv_div, div_inv_eq_mul]
  ring

lemma continuous_halfPlaneQ :
    Continuous (fun p : DiskFamily × UpperHalfPlane => halfPlaneQ p.1 p.2) :=
  continuous_halfPlaneFunction_deriv.inv₀
    (fun p => halfPlaneFunction_deriv_ne_zero p.1 p.2.im_pos)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransferOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def affineDiskFunction (w : ℂ) : ℂ := w / (1 - w)

lemma affineDiskFunction_differentiableOn :
    DifferentiableOn ℂ affineDiskFunction (ball 0 1) :=
  differentiableOn_id.div (differentiableOn_id.const_sub 1)
    (fun _ hw => one_sub_ne_zero_of_mem_disk hw)

lemma affineDiskFunction_injOn : InjOn affineDiskFunction (ball 0 1) := by
  intro a ha b hb hab
  have h := (div_eq_div_iff (one_sub_ne_zero_of_mem_disk ha)
    (one_sub_ne_zero_of_mem_disk hb)).mp hab
  linear_combination h

lemma affineDiskFunction_hasDerivAt_zero : HasDerivAt affineDiskFunction 1 0 := by
  convert! (hasDerivAt_id (0 : ℂ)).div
    ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by norm_num : (1 : ℂ) - 0 ≠ 0) using 1
  simp

def affineDiskMap : C(UnitDisk, ℂ) :=
  ⟨fun w => affineDiskFunction w,
    affineDiskFunction_differentiableOn.continuousOn.comp_continuous
      continuous_subtype_val (fun w => w.property)⟩

lemma affineDiskMap_extension {w : ℂ} (hw : w ∈ ball 0 1) :
    diskExtension affineDiskMap w = affineDiskFunction w := by
  simp only [diskExtension, dite_eq_left hw, affineDiskMap, ContinuousMap.coe_mk]

lemma affineDiskMap_normalized : DiskNormalized affineDiskMap := by
  have he : EqOn (diskExtension affineDiskMap) affineDiskFunction (ball 0 1) :=
    fun _ hw => affineDiskMap_extension hw
  refine ⟨affineDiskFunction_differentiableOn.congr he,
    fun a ha b hb hab => affineDiskFunction_injOn ha hb ?_, ?_, ?_⟩
  · simpa only [he ha, he hb] using hab
  · rw [he (mem_ball_self zero_lt_one)]
    simp [affineDiskFunction]
  · exact (affineDiskFunction_hasDerivAt_zero.congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)) he)).deriv

def affineFamily : DiskFamily := ⟨affineDiskMap, affineDiskMap_normalized⟩

instance instNonemptyDiskFamily : Nonempty DiskFamily := ⟨affineFamily⟩

lemma halfPlaneFunction_affineFamily {z : ℂ} (hz : 0 < z.im) :
    halfPlaneFunction affineFamily z = z - I := by
  change 2 * I * diskExtension affineDiskMap (cayleyToDisk z) = _
  rw [affineDiskMap_extension (cayleyToDisk_mem hz)]
  dsimp only [affineDiskFunction, cayleyToDisk]
  have hd := add_I_ne_zero hz
  have he : 1 - (z - I) / (z + I) = 2 * I / (z + I) := by
    field_simp
    ring
  rw [he]
  field_simp

lemma halfPlaneFunction_affineFamily_deriv (z : UpperHalfPlane) :
    deriv (halfPlaneFunction affineFamily) z = 1 := by
  apply HasDerivAt.deriv
  exact ((hasDerivAt_id (z : ℂ)).sub_const I).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds z.im_pos)
      (fun _ hw => halfPlaneFunction_affineFamily hw))

@[simp] lemma halfPlaneQ_affineFamily (z : UpperHalfPlane) : halfPlaneQ affineFamily z = 1 := by
  simp only [halfPlaneQ, halfPlaneFunction_affineFamily_deriv, inv_one]

@[simp] lemma rebase_affineFamily (z : UpperHalfPlane) : rebase affineFamily z = affineFamily := by
  apply diskFamily_ext
  intro w
  rw [halfPlaneFunction_rebase affineFamily z w.im_pos,
    halfPlaneFunction_affineFamily (affineAt_mapsTo z w.im_pos),
    halfPlaneFunction_affineFamily z.im_pos, halfPlaneFunction_affineFamily w.im_pos,
    halfPlaneFunction_affineFamily_deriv]
  dsimp only [affineAt]
  rw [← z.re_add_im]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  ring

def rebaseUncurried : C(DiskFamily × UpperHalfPlane, DiskFamily) :=
  ⟨fun p => rebase p.1 p.2, continuous_rebase⟩

def rebaseMap (z : UpperHalfPlane) : C(DiskFamily, DiskFamily) :=
  rebaseUncurried.comp ((ContinuousMap.id DiskFamily).prodMk (ContinuousMap.const DiskFamily z))

def weightMap (z : UpperHalfPlane) : C(DiskFamily, ℝ) :=
  ⟨fun f => ‖halfPlaneQ f z‖,
    (continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).norm⟩

def affineOperator (z : UpperHalfPlane) : C(DiskFamily, ℝ) →L[ℝ] C(DiskFamily, ℝ) :=
  (ContinuousLinearMap.mul ℝ C(DiskFamily, ℝ) (weightMap z)).comp
    (ContinuousMap.compCLM ℝ ℝ (rebaseMap z))

@[simp] lemma affineOperator_apply (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)) (f : DiskFamily) :
    affineOperator z φ f = ‖halfPlaneQ f z‖ * φ (rebase f z) := rfl

@[simp] lemma affineOperator_affineFamily (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)) :
    affineOperator z φ affineFamily = φ affineFamily := by simp

lemma continuous_affineOperator_apply (φ : C(DiskFamily, ℝ)) :
    Continuous (fun p : UpperHalfPlane × DiskFamily => affineOperator p.1 φ p.2) := by
  exact (continuous_halfPlaneQ.comp continuous_swap).norm.mul
    (φ.continuous.comp (continuous_rebase.comp continuous_swap))

lemma continuous_affineOperator_strong (φ : C(DiskFamily, ℝ)) :
    Continuous (fun z : UpperHalfPlane => affineOperator z φ) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_affineOperator_apply φ)

def dyadicLeft : UpperHalfPlane := ⟨-(1 / 2 : ℂ) + I / 2, by norm_num⟩
def dyadicRight : UpperHalfPlane := ⟨(1 / 2 : ℂ) + I / 2, by norm_num⟩

def dyadicOperator : C(DiskFamily, ℝ) →L[ℝ] C(DiskFamily, ℝ) :=
  (1 / 2 : ℝ) • (affineOperator dyadicLeft + affineOperator dyadicRight)

@[simp] lemma dyadicOperator_affineFamily (φ : C(DiskFamily, ℝ)) :
    dyadicOperator φ affineFamily = φ affineFamily := by
  change (1 / 2 : ℝ) * (affineOperator dyadicLeft φ affineFamily +
    affineOperator dyadicRight φ affineFamily) = _
  simp
  ring

lemma dyadicOperator_pow_affineFamily (n : ℕ) :
    (dyadicOperator ^ n) (1 : C(DiskFamily, ℝ)) affineFamily = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, dyadicOperator_affineFamily, ih]

lemma dyadicOperator_pow_norm_ge_one (n : ℕ) : 1 ≤ ‖dyadicOperator ^ n‖ := by
  have he := ((dyadicOperator ^ n) (1 : C(DiskFamily, ℝ))).norm_coe_le_norm affineFamily
  rw [dyadicOperator_pow_affineFamily, norm_one] at he
  exact he.trans (by simpa using (dyadicOperator ^ n).le_opNorm (1 : C(DiskFamily, ℝ)))

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DyadicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def xyPoint (x y : ℝ) (hy : 0 < y) : UpperHalfPlane := ⟨x + y * I, by simpa⟩
@[simp] lemma xyPoint_re (x y : ℝ) (hy : 0 < y) : (xyPoint x y hy).re = x := by simp [xyPoint]
@[simp] lemma xyPoint_im (x y : ℝ) (hy : 0 < y) : (xyPoint x y hy).im = y := by simp [xyPoint]

def horizontalPoint (x : ℝ) : UpperHalfPlane := xyPoint x 1 zero_lt_one

def dyadicHeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
lemma dyadicHeight_pos (n : ℕ) : 0 < dyadicHeight n := pow_pos (by norm_num) _

def gridStart (n : ℕ) : UpperHalfPlane :=
  xyPoint (-1 + dyadicHeight n) (dyadicHeight n) (dyadicHeight_pos n)
def gridEnd (n : ℕ) : UpperHalfPlane :=
  xyPoint (1 + dyadicHeight n) (dyadicHeight n) (dyadicHeight_pos n)

lemma affineOperator_norm_bound {z : UpperHalfPlane} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : DiskFamily, ‖halfPlaneQ f z‖ ≤ C) : ‖affineOperator z‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro φ
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr
  intro f
  rw [affineOperator_apply, norm_mul, norm_norm]
  exact mul_le_mul (h f) (φ.norm_coe_le_norm _) (norm_nonneg _) hC

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SpectralGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

open Set Filter
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {A : Type*} [NormedRing A]

lemma logNormPower_subadditive (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    Subadditive (fun n => Real.log ‖a ^ n‖) := by
  intro m n
  have hm : 0 < ‖a ^ m‖ := lt_of_lt_of_le zero_lt_one (h m)
  have hn : 0 < ‖a ^ n‖ := lt_of_lt_of_le zero_lt_one (h n)
  calc
    Real.log ‖a ^ (m + n)‖ ≤ Real.log (‖a ^ m‖ * ‖a ^ n‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (h _)) (by rw [pow_add]; exact norm_mul_le _ _)
    _ = Real.log ‖a ^ m‖ + Real.log ‖a ^ n‖ := Real.log_mul hm.ne' hn.ne'

def logNormGrowth (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) : ℝ :=
  (logNormPower_subadditive a h).lim

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PositiveFunctionals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

def compactTestFunctional (Λ : C(X, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) :
    CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := Λ f.toContinuousMap
  map_add' f g := by exact Λ.map_add f.toContinuousMap g.toContinuousMap
  map_smul' c f := by exact Λ.map_smul c f.toContinuousMap
  monotone' := fun _ _ h => hΛ h

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Eigenmeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def growthResolvent (a : A) (τ : ℝ) : A := ∑' n : ℕ, (τ⁻¹ • a) ^ n

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HorizontalAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma compactTest_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℝ)) :
    Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def probabilityFunctional (μ : ProbabilityMeasure X) : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂(μ : Measure X)
      map_add' := fun f g => integral_add (compactTest_integrable _ f) (compactTest_integrable _ g)
      map_smul' := fun c f => integral_smul c f }
    1 (fun f => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (μ : Measure X)) (Filter.Eventually.of_forall f.norm_coe_le_norm))

@[simp] lemma probabilityFunctional_apply (μ : ProbabilityMeasure X) (f : C(X, ℝ)) :
    probabilityFunctional μ f = ∫ x, f x ∂(μ : Measure X) := rfl

@[simp] lemma probabilityFunctional_one (μ : ProbabilityMeasure X) : probabilityFunctional μ 1 = 1 := by
  simp [probabilityFunctional]

instance diskFamilyMeasurableSpace : MeasurableSpace DiskFamily := borel _
instance instBorelSpaceDiskFamily : BorelSpace DiskFamily := ⟨rfl⟩

def dyadicLogGrowth : ℝ := logNormGrowth dyadicOperator dyadicOperator_pow_norm_ge_one
def dyadicRadius : ℝ := Real.exp dyadicLogGrowth
def dyadicExponent : ℝ := dyadicLogGrowth / Real.log 2

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_xyPoint {x y : ℝ → ℝ} (hx : Continuous x) (hy : Continuous y)
    (hp : ∀ t, 0 < y t) : Continuous (fun t => xyPoint (x t) (y t) (hp t)) :=
  ((Complex.continuous_ofReal.comp hx).add
    ((Complex.continuous_ofReal.comp hy).mul_const Complex.I)).upperHalfPlaneMk _

lemma continuous_horizontalPoint : Continuous horizontalPoint :=
  continuous_xyPoint continuous_id continuous_const _

lemma affineOperator_compact_bound (z : ℝ → UpperHalfPlane) (hz : Continuous z) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ uIcc a b, ‖affineOperator (z t)‖ ≤ C := by
  let Y := (uIcc a b) × DiskFamily
  let : CompactSpace (uIcc a b) := isCompact_iff_compactSpace.mp isCompact_uIcc
  let W : C(Y, ℝ) := ⟨fun p => ‖halfPlaneQ p.2 (z p.1)‖,
    (continuous_halfPlaneQ.comp (continuous_snd.prodMk
      (hz.comp (continuous_subtype_val.comp continuous_fst)))).norm⟩
  refine ⟨‖W‖, norm_nonneg _, fun t ht => affineOperator_norm_bound (norm_nonneg _) ?_⟩
  intro f
  simpa only [W, ContinuousMap.coe_mk, norm_norm] using W.norm_coe_le_norm (⟨t, ht⟩, f)

section WeakIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : E →L[ℝ] ℝ) (A : ℝ → E →L[ℝ] E)
  (hA : ∀ f : E, Continuous (fun t => A t f)) (a b : ℝ)
  (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ uIcc a b, ‖A t‖ ≤ C)

def intervalFunctional : E →L[ℝ] ℝ :=
  let C := hbound.choose
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in a..b, Λ (A t f)
      map_add' := fun f g => by
        simp only [map_add]
        exact intervalIntegral.integral_add
          ((Λ.continuous.comp (hA f)).intervalIntegrable _ _)
          ((Λ.continuous.comp (hA g)).intervalIntegrable _ _)
      map_smul' := fun c f => by
        simp only [map_smul]
        exact intervalIntegral.integral_smul c _ }
    (‖Λ‖ * C * |b - a|) (fun f => by
      have hb := hbound.choose_spec
      calc
        ‖∫ t in a..b, Λ (A t f)‖ ≤ (‖Λ‖ * (C * ‖f‖)) * |b - a| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          exact (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (((A t).le_opNorm f).trans
              (mul_le_mul_of_nonneg_right (hb.2 t (uIoc_subset_uIcc ht)) (norm_nonneg f)))
            (norm_nonneg Λ))
        _ = (‖Λ‖ * C * |b - a|) * ‖f‖ := by ring)

@[simp] lemma intervalFunctional_apply (f : E) :
    intervalFunctional Λ A hA a b hbound f = ∫ t in a..b, Λ (A t f) := rfl
end WeakIntegral

def affineIntervalFunctional (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (z : ℝ → UpperHalfPlane) (hz : Continuous z) (a b : ℝ) : C(DiskFamily, ℝ) →L[ℝ] ℝ :=
  intervalFunctional Λ (fun t => affineOperator (z t))
    (fun φ => (continuous_affineOperator_strong φ).comp hz) a b
    (affineOperator_compact_bound z hz a b)

@[simp] lemma affineIntervalFunctional_apply (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (z : ℝ → UpperHalfPlane) (hz : Continuous z) (a b : ℝ) (φ : C(DiskFamily, ℝ)) :
    affineIntervalFunctional Λ z hz a b φ = ∫ t in a..b, Λ (affineOperator (z t) φ) := rfl

def horizontalAverage (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) : C(DiskFamily, ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • affineIntervalFunctional Λ horizontalPoint continuous_horizontalPoint 0 2

@[simp] lemma horizontalAverage_apply (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ φ = (1 / 2 : ℝ) * ∫ t in 0..2, Λ (affineOperator (horizontalPoint t) φ) := rfl

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def halfScalePoint : UpperHalfPlane := xyPoint 0 (1 / 2) (by norm_num)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AffineAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def expScalePoint (t : ℝ) : UpperHalfPlane := xyPoint 0 (Real.exp t) (Real.exp_pos t)

lemma continuous_expScalePoint : Continuous expScalePoint :=
  continuous_xyPoint continuous_const Real.continuous_exp _

lemma weighted_scale_bound (β a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ uIcc a b,
      ‖Real.exp (β * t) • affineOperator (expScalePoint t)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := affineOperator_compact_bound expScalePoint continuous_expScalePoint a b
  let : CompactSpace (uIcc a b) := isCompact_iff_compactSpace.mp isCompact_uIcc
  let W : C(uIcc a b, ℝ) := ⟨fun t => Real.exp (β * t),
    Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)⟩
  refine ⟨‖W‖ * C, mul_nonneg (norm_nonneg _) hC, fun t ht => ?_⟩
  calc
    ‖Real.exp (β * t) • affineOperator (expScalePoint t)‖ ≤
        ‖Real.exp (β * t)‖ * ‖affineOperator (expScalePoint t)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖W‖ * C := mul_le_mul (W.norm_coe_le_norm ⟨t, ht⟩) (hbound t ht)
      (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _)

def scaleAverage (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β : ℝ) : C(DiskFamily, ℝ) →L[ℝ] ℝ :=
  intervalFunctional Λ (fun t => Real.exp (β * t) • affineOperator (expScalePoint t))
    (fun φ => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((continuous_affineOperator_strong φ).comp continuous_expScalePoint))
    0 (Real.log 2) (weighted_scale_bound β 0 (Real.log 2))

@[simp] lemma scaleAverage_apply (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β : ℝ)
    (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β φ = ∫ t in 0..Real.log 2,
      Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ) := by
  simp only [scaleAverage, intervalFunctional_apply, smul_apply, map_smul,
    smul_eq_mul]

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

namespace StrictInverseFirstPower
noncomputable section

def weightedRebaseMeasure (μ : Measure DiskFamily) (z : UpperHalfPlane) : Measure DiskFamily :=
  (μ.withDensity (fun f => ‖halfPlaneQ f z‖₊)).map (fun f => rebase f z)

instance weightedRebaseMeasure_isFinite (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (z : UpperHalfPlane) : IsFiniteMeasure (weightedRebaseMeasure μ z) := by
  have hi : Integrable (fun f => halfPlaneQ f z) μ :=
    (continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have : IsFiniteMeasure (μ.withDensity (fun f => ‖halfPlaneQ f z‖₊)) :=
    isFiniteMeasure_withDensity hi.hasFiniteIntegral.ne
  unfold weightedRebaseMeasure
  infer_instance

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.ReciprocalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

abbrev HalfPlaneSet := {z : ℂ // 0 < z.im}

def reciprocalFunction (f : DiskFamily) (z : ℂ) : ℂ :=
  (deriv (halfPlaneFunction f) z)⁻¹

@[simp] lemma reciprocalFunction_I (f : DiskFamily) : reciprocalFunction f I = 1 := by
  simp [reciprocalFunction]

lemma reciprocalFunction_ne_zero (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    reciprocalFunction f z ≠ 0 :=
  inv_ne_zero (halfPlaneFunction_deriv_ne_zero f hz)

lemma reciprocalFunction_differentiableOn (f : DiskFamily) :
    DifferentiableOn ℂ (reciprocalFunction f) {z : ℂ | 0 < z.im} :=
  ((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).inv
    (fun _ hz => halfPlaneFunction_deriv_ne_zero f hz)

abbrev MomentInterval := Set.Icc (-(1 / 2) : ℝ) (1 / 2)

def sourcePath (v : ℂ) (t : ℝ) : ℂ := I + (t : ℂ) * v

@[simp] lemma sourcePath_zero (v : ℂ) : sourcePath v 0 = I := by simp [sourcePath]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

def normPathFirst (f : DiskFamily) (v : ℂ) (t : ℝ) : ℝ :=
  (conj (reciprocalFunction f (sourcePath v t)) *
    (deriv (reciprocalFunction f) (sourcePath v t) * v)).re /
    ‖reciprocalFunction f (sourcePath v t)‖

def normPathSecond (f : DiskFamily) (v : ℂ) (t : ℝ) : ℝ :=
  ((conj (deriv (reciprocalFunction f) (sourcePath v t) * v) *
    (deriv (reciprocalFunction f) (sourcePath v t) * v) +
    conj (reciprocalFunction f (sourcePath v t)) *
    (deriv (deriv (reciprocalFunction f)) (sourcePath v t) * v ^ 2)).re) /
    ‖reciprocalFunction f (sourcePath v t)‖ -
  ((conj (reciprocalFunction f (sourcePath v t)) *
    (deriv (reciprocalFunction f) (sourcePath v t) * v)).re) ^ 2 /
    ‖reciprocalFunction f (sourcePath v t)‖ ^ 3

@[simp] lemma normPathFirst_zero (f : DiskFamily) (v : ℂ) :
    normPathFirst f v 0 = (deriv (reciprocalFunction f) I * v).re := by
  simp [normPathFirst]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

def ReciprocalMeanLaw (μ : Measure DiskFamily) (β : ℝ) : Prop :=
  ∀ z : UpperHalfPlane, (∫ f, ‖reciprocalFunction f z‖ ∂μ) = z.im ^ (-β)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.JacobianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Complex
open scoped Topology

noncomputable section

namespace StrictInverseFirstPower

theorem real_det_eq (L : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det L = (L 1).re * (L I).im - (L I).re * (L 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

def criticalMap (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z - I * (z.im : ℂ) * deriv F z / (k : ℂ)

def normalizedJacobian (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ (criticalMap k F) z).det / ‖deriv F z‖ ^ 2

theorem criticalMap_fderiv {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z) :
    fderiv ℝ (criticalMap k F) z =
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ -
        (I / (k : ℂ)) •
          ((z.im : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv F) z)).restrictScalars ℝ +
            deriv F z • (Complex.ofRealCLM.comp Complex.imCLM)) := by
  have h1 := hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have h2 := hF'.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hi := (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt (x := z)
  have hh := h1.sub ((hi.mul h2).const_mul (I / (k : ℂ)))
  convert hh.fderiv using 1
  · congr 1
    funext w
    simp only [criticalMap, Pi.mul_apply, Pi.sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Complex.ofRealCLM_apply, Complex.imCLM_apply]
    ring
  · ext w
    simp [smul_eq_mul]

def logarithmicDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  -I * (z.im : ℂ) * (deriv (deriv F) z / deriv F z)

def jacobianExpression (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (k * (k - 1) + (2 * k - 1) * (logarithmicDerivative F z).re +
    ‖logarithmicDerivative F z‖ ^ 2) / k ^ 2

theorem determinant_columns_factor (a q : ℂ) (k : ℝ) :
    (a * ((k : ℂ) + q)).re * (I * a * ((k : ℂ) - 1 + q)).im -
    (I * a * ((k : ℂ) - 1 + q)).re * (a * ((k : ℂ) + q)).im =
      ‖a‖ ^ 2 * (k * (k - 1) + (2 * k - 1) * q.re + ‖q‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, add_re, add_im,
    sub_re, sub_im, mul_re, mul_im, I_re, I_im, one_re, one_im, ofReal_re, ofReal_im]
  ring

theorem criticalMap_fderiv_one {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z)
    (hne : deriv F z ≠ 0) :
    fderiv ℝ (criticalMap k F) z 1 =
      (deriv F z / (k : ℂ)) * ((k : ℂ) + logarithmicDerivative F z) := by
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [criticalMap_fderiv hF hF']
  simp [smul_eq_mul, logarithmicDerivative]
  field_simp [hk', hne]
  ring

theorem criticalMap_fderiv_I {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z)
    (hne : deriv F z ≠ 0) :
    fderiv ℝ (criticalMap k F) z I =
      I * (deriv F z / (k : ℂ)) * ((k : ℂ) - 1 + logarithmicDerivative F z) := by
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [criticalMap_fderiv hF hF']
  simp [smul_eq_mul, logarithmicDerivative]
  field_simp [hk', hne]
  ring

theorem normalizedJacobian_eq {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hF : DifferentiableAt ℂ F z) (hF' : DifferentiableAt ℂ (deriv F) z)
    (hne : deriv F z ≠ 0) :
    normalizedJacobian k F z = jacobianExpression k F z := by
  unfold normalizedJacobian
  change LinearMap.det (fderiv ℝ (criticalMap k F) z : ℂ →ₗ[ℝ] ℂ) / ‖deriv F z‖ ^ 2 = _
  rw [real_det_eq]
  change ( (fderiv ℝ (criticalMap k F) z 1).re * (fderiv ℝ (criticalMap k F) z I).im -
    (fderiv ℝ (criticalMap k F) z I).re * (fderiv ℝ (criticalMap k F) z 1).im) /
    ‖deriv F z‖ ^ 2 = _
  rw [criticalMap_fderiv_one hk hF hF' hne, criticalMap_fderiv_I hk hF hF' hne,
    determinant_columns_factor]
  unfold jacobianExpression
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

end StrictInverseFirstPower

end

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def affineInversePlane (z : ℂ) : ℂ := (-(z.re : ℂ) + I) / (z.im : ℂ)

def outsideCenter : Set ℂ := {z | 0 < z.im ∧ 1 / 2 ≤ ‖cayleyToDisk z‖}

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def halfPlaneProjection : ℂ → UpperHalfPlane :=
  UpperHalfPlane.measurableEmbedding_coe.invFun

@[simp] lemma halfPlaneProjection_coe (z : UpperHalfPlane) : halfPlaneProjection z = z :=
  UpperHalfPlane.measurableEmbedding_coe.leftInverse_invFun z

def inverseCubeValue (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖halfPlaneFunction f z‖⁻¹ ^ 3)

def conformalAreaCube (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖deriv (halfPlaneFunction f) z‖ ^ 2) * inverseCubeValue f z

def weightedAreaTail (β : ℝ) (f : DiskFamily) : ℝ≥0∞ :=
  ∫⁻ z in outsideCenter, ENNReal.ofReal (z.im ^ β) * inverseCubeValue f (halfPlaneProjection z)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GreenIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

def realPlanePartial (v : ℝ × ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ g p v

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def planePartial (v : ℂ) (g : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ g z v

def planeLaplacian (g : ℂ → ℝ) (z : ℂ) : ℝ :=
  planePartial 1 (planePartial 1 g) z + planePartial I (planePartial I g) z

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HorizontalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

def horizontalCutoff (f : DiskFamily) (ψ : ℂ → ℝ) (s : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (4 * z.im / s - 2) * ψ (halfPlaneFunction f z)

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoundaryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def cellRectangle : Set UpperHalfPlane :=
  {z | |z.re| ≤ 1 ∧ 1/2 ≤ z.im ∧ z.im ≤ 1}

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def boundaryWitness (f : DiskFamily) (k R δ h : ℝ) (ξ : ℂ) (z : UpperHalfPlane) : Prop :=
  ξ ∉ halfPlaneFunction f '' {w : ℂ | 0 < w.im} ∧ ‖ξ‖ ≤ R ∧
  h ≤ z.im ∧ z.im ≤ 2*h ∧ ‖halfPlaneFunction f z-ξ‖ ≤ z.im^k/δ

def boundaryBadScale (f : DiskFamily) (k R δ h : ℝ) : Set ℂ :=
  {ξ | ∃ z, boundaryWitness f k R δ h ξ z}

def boundaryMarkedCells (f : DiskFamily) (k R δ h : ℝ) : Set ℤ :=
  {j | ∃ ξ z, boundaryWitness f k R δ h ξ z ∧ z.re ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h)}

def cellMidpointImage (f : DiskFamily) (h : ℝ) (j : ℤ) : ℂ :=
  halfPlaneFunction f ((((j:ℝ)+1/2)*h : ℝ) + (h:ℂ)*I)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoundaryEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def boundaryEscape (k : ℝ) (F : ℂ → ℂ) (ξ : ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ z : UpperHalfPlane,
    z.im < ε → z.im^k/δ < ‖F z-ξ‖

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def potentialSuperlevel (k : ℝ) (F : ℂ → ℂ) (ξ : ℂ) (h : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ ‖F z - ξ‖ ≤ z.im ^ k / h}

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def logPotential (k : ℝ) (F : ℂ → ℂ) (ξ z : ℂ) : ℝ :=
  k * Real.log z.im - Real.log ‖F z - ξ‖

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def criticalHeight (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  k * z.im ^ (k-1) * ‖(deriv F z)⁻¹‖

lemma criticalMap_ne_image {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : deriv F z ≠ 0) :
    criticalMap k F z ≠ F z := by
  intro h
  have hh : I * (z.im : ℂ) * deriv F z / (k : ℂ) = 0 := by
    have := sub_eq_self.mp h
    exact this
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero
    (Complex.ofReal_ne_zero.mpr hz.ne')) hF) (Complex.ofReal_ne_zero.mpr hk)) hh

lemma criticalMap_sub_image {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hg : criticalMap k F z = ξ) :
    F z - ξ = I * (z.im : ℂ) * deriv F z / (k : ℂ) := by
  dsimp [criticalMap] at hg
  linear_combination hg

lemma criticalHeight_value {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hg : criticalMap k F z = ξ) :
    z.im ^ k / ‖F z - ξ‖ = criticalHeight k F z := by
  rw [criticalMap_sub_image hg]
  simp only [norm_div, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hz, abs_of_pos hk, criticalHeight, norm_inv]
  rw [Real.rpow_sub hz, Real.rpow_one]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma criticalHeight_superlevel {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ} {h : ℝ}
    (hk : 0 < k) (hz : 0 < z.im) (hF : deriv F z ≠ 0) (hh : 0 < h)
    (hg : criticalMap k F z = ξ) :
    z ∈ potentialSuperlevel k F ξ h ↔ h ≤ criticalHeight k F z := by
  have hn : 0 < ‖F z - ξ‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro he
    exact criticalMap_ne_image hk.ne' hz hF (hg.trans he.symm)
  rw [← criticalHeight_value hk hz hg]
  change (0 < z.im ∧ ‖F z - ξ‖ ≤ z.im ^ k / h) ↔ _
  rw [and_iff_right hz, le_div_iff₀ hh, le_div_iff₀ hn]
  rw [mul_comm]

lemma criticalMap_contDiffAt (k : ℝ) (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ⊤ (criticalMap k (halfPlaneFunction f)) z := by
  have ha : AnalyticAt ℂ (halfPlaneFunction f) z :=
    (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  exact (ha.restrictScalars (𝕜 := ℝ)).contDiffAt.sub
    ((contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).contDiffAt)).mul
      (ha.deriv.restrictScalars (𝕜 := ℝ)).contDiffAt |>.div_const _)

lemma jacobianExpression_zero_iff (k : ℝ) (hk : k ≠ 0) (f : DiskFamily)
    {z : ℂ} (hz : 0 < z.im) :
    jacobianExpression k (halfPlaneFunction f) z = 0 ↔
      (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det = 0 := by
  have ha : AnalyticAt ℂ (halfPlaneFunction f) z :=
    (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  rw [← normalizedJacobian_eq hk ha.differentiableAt ha.deriv.differentiableAt
    (halfPlaneFunction_deriv_ne_zero f hz), normalizedJacobian]
  rw [div_eq_zero_iff]
  simp [halfPlaneFunction_deriv_ne_zero f hz]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.MeasurableGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma reciprocalFunction_deriv (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    deriv (reciprocalFunction f) z =
      -deriv (deriv (halfPlaneFunction f)) z / (deriv (halfPlaneFunction f) z) ^ 2 := by
  have h := (((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds hz)).hasDerivAt
  change deriv (fun z => (deriv (halfPlaneFunction f) z)⁻¹) z = _
  exact (h.inv (halfPlaneFunction_deriv_ne_zero f hz)).deriv

lemma logarithmicDerivative_eq_reciprocal (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    logarithmicDerivative (halfPlaneFunction f) z =
      I * z.im * (deriv (reciprocalFunction f) z / reciprocalFunction f z) := by
  rw [reciprocalFunction_deriv f hz]
  unfold logarithmicDerivative reciprocalFunction
  field_simp [halfPlaneFunction_deriv_ne_zero f hz]

lemma reciprocalFunction_rebase (f : DiskFamily) (z : UpperHalfPlane) {w : ℂ} (hw : 0 < w.im) :
    reciprocalFunction (rebase f z) w =
      reciprocalFunction f (affineAt z w) / reciprocalFunction f z :=
  halfPlaneQ_rebase f z ⟨w, hw⟩

lemma reciprocalFunction_rebase_deriv (f : DiskFamily) (z w : UpperHalfPlane) :
    deriv (reciprocalFunction (rebase f z)) w =
      (deriv (reciprocalFunction f) (affineAt z w) * z.im) / reciprocalFunction f z := by
  have hf := ((reciprocalFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds (affineAt_mapsTo z w.im_pos))).hasDerivAt
  have hh := (hf.comp (w : ℂ) (affineAt_hasDerivAt z w)).div_const (reciprocalFunction f z)
  have he : reciprocalFunction (rebase f z) =ᶠ[𝓝 (w : ℂ)]
      fun u => reciprocalFunction f (affineAt z u) / reciprocalFunction f z :=
    Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds w.im_pos)
      (fun u hu => reciprocalFunction_rebase f z hu)
  exact (hh.congr_of_eventuallyEq he).deriv

lemma logarithmicDerivative_rebase (f : DiskFamily) (z w : UpperHalfPlane) :
    logarithmicDerivative (halfPlaneFunction (rebase f z)) w =
      logarithmicDerivative (halfPlaneFunction f) (affineAt z w) := by
  rw [logarithmicDerivative_eq_reciprocal _ w.im_pos,
    logarithmicDerivative_eq_reciprocal _ (affineAt_mapsTo z w.im_pos),
    reciprocalFunction_rebase_deriv, reciprocalFunction_rebase f z w.im_pos]
  simp only [affineAt, add_im, ofReal_im, mul_im, ofReal_re, zero_mul, zero_add]
  field_simp [reciprocalFunction_ne_zero f z.im_pos,
    reciprocalFunction_ne_zero f (affineAt_mapsTo z w.im_pos)]
  push_cast
  ring

lemma jacobianExpression_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) :
    jacobianExpression k (halfPlaneFunction (rebase f z)) w =
      jacobianExpression k (halfPlaneFunction f) (affineAt z w) := by
  simp only [jacobianExpression, logarithmicDerivative_rebase]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def reciprocalPotential (k : ℝ) (p : DiskFamily × ℂ) (z : UpperHalfPlane) : ℝ :=
  ‖halfPlaneFunction p.1 z-p.2‖ / z.im ^ k

lemma reciprocalPotential_sublevel_image (k : ℝ) (p : DiskFamily × ℂ) {r : ℝ} (hr : 0 < r) :
    UpperHalfPlane.coe '' {z : UpperHalfPlane | reciprocalPotential k p z ≤ r} =
      potentialSuperlevel k (halfPlaneFunction p.1) p.2 (1/r) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨w.im_pos, ?_⟩
    change ‖halfPlaneFunction p.1 w - p.2‖ / w.im^k ≤ r at hw
    rw [le_div_iff₀ (one_div_pos.mpr hr)]
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos w.im_pos k)).mp hw
    simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
      (div_le_iff₀ hr).mpr (by simpa only [mul_comm, UpperHalfPlane.coe_im] using hh)
  · intro hz
    refine ⟨⟨z,hz.1⟩, ?_, rfl⟩
    change ‖halfPlaneFunction p.1 z-p.2‖/z.im^k ≤ r
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hz.1 k)]
    have hh := hz.2
    simpa only [one_div, div_eq_mul_inv, inv_inv, one_mul, mul_one, mul_comm] using hh

lemma compactPotential_iff (k : ℝ) (p : DiskFamily × ℂ) :
    (∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)) ↔
    (∀ r : ℝ, 0 < r → IsCompact {z : UpperHalfPlane | reciprocalPotential k p z ≤ r}) := by
  constructor
  · intro hp r hr
    apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
    rw [reciprocalPotential_sublevel_image k p hr]
    exact hp _ (one_div_pos.mpr hr)
  · intro hp h hh
    have he := reciprocalPotential_sublevel_image k p (one_div_pos.mpr hh)
    rw [one_div_one_div] at he
    rw [← he]
    exact (hp _ (one_div_pos.mpr hh)).image UpperHalfPlane.continuous_coe

def GoodPair (k : ℝ) (p : DiskFamily × ℂ) : Prop :=
  (∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)) ∧
  (∀ z : UpperHalfPlane, criticalMap k (halfPlaneFunction p.1) z = p.2 →
    jacobianExpression k (halfPlaneFunction p.1) z ≠ 0) ∧
  (∀ z w : UpperHalfPlane, criticalMap k (halfPlaneFunction p.1) z = p.2 →
    criticalMap k (halfPlaneFunction p.1) w = p.2 →
    criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma nonsingular_locally_injective {G : ℂ → ℂ} {z : ℂ}
    (hG : ContDiffAt ℝ 1 G z) (hdet : (fderiv ℝ G z).det ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ InjOn G U := by
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfDetNeZero (fderiv ℝ G z).toLinearMap hdet).toContinuousLinearEquiv
  have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ G z := by
    ext w
    simp [e, LinearMap.equivOfDetNeZero, LinearEquiv.ofIsUnitDet_apply]
  have hs : HasStrictFDerivAt G (e : ℂ →L[ℝ] ℂ) z := by
    rw [he]
    exact hG.hasStrictFDerivAt one_ne_zero
  let E := hs.toOpenPartialHomeomorph G
  exact ⟨E.source, E.open_source, hs.mem_toOpenPartialHomeomorph_source, E.injOn⟩

lemma compact_level_regular_fiber_finite {G : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hG : ContinuousOn G K) (ξ : ℂ)
    (hregular : ∀ z ∈ K, G z = ξ → ContDiffAt ℝ 1 G z ∧ (fderiv ℝ G z).det ≠ 0) :
    (K ∩ G ⁻¹' {ξ}).Finite := by
  let S := K ∩ G ⁻¹' {ξ}
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosed {x : K | G x = ξ} :=
    isClosed_eq hG.domRestrict continuous_const
  have hc : IsCompact S := by
    convert hclosed.isCompact.image continuous_subtype_val using 1
    ext x
    simp only [S, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, mem_ofPred_eq,
      Subtype.exists, exists_and_right, exists_eq_right]
    tauto
  have : DiscreteTopology S := discreteTopology_subtype_iff'.mpr (by
    intro z hz
    obtain ⟨ho, hd⟩ := hregular z hz.1 hz.2
    obtain ⟨U, hU, hzU, hi⟩ := nonsingular_locally_injective ho hd
    refine ⟨U, hU, ?_⟩
    ext w
    constructor
    · intro hw
      exact mem_singleton_iff.mpr (hi hw.1 hzU (hw.2.2.trans hz.2.symm))
    · rintro rfl
      exact ⟨hzU, hz⟩)
  have : CompactSpace S := isCompact_iff_compactSpace.mp hc
  have : Finite S := finite_of_compact_of_discrete
  exact Set.toFinite S

def criticalCut (k : ℝ) (f : DiskFamily) (ξ : ℂ) (h : ℝ) : Set UpperHalfPlane :=
  {z | criticalMap k (halfPlaneFunction f) z = ξ ∧ h ≤ criticalHeight k (halfPlaneFunction f) z}

lemma goodPair_criticalCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0 < h) : (criticalCut k f ξ h).Finite := by
  let K := potentialSuperlevel k (halfPlaneFunction f) ξ h
  have hcont : ContinuousOn (criticalMap k (halfPlaneFunction f)) K := by
    intro z hz
    exact (criticalMap_contDiffAt k f hz.1).continuousAt.continuousWithinAt
  have hf := compact_level_regular_fiber_finite (hg.1 h hh) hcont ξ (by
    intro z hz he
    refine ⟨(criticalMap_contDiffAt k f hz.1).of_le (by norm_num), ?_⟩
    exact (not_congr (jacobianExpression_zero_iff k hk.ne' f hz.1)).mp
      (hg.2.1 ⟨z,hz.1⟩ he))
  have hs : criticalCut k f ξ h ⊆ (fun z : UpperHalfPlane => (z:ℂ)) ⁻¹' (K ∩ criticalMap k (halfPlaneFunction f) ⁻¹' {ξ}) := by
    intro z hz
    exact ⟨(criticalHeight_superlevel hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos) hh hz.1).mpr hz.2,hz.1⟩
  exact (hf.preimage UpperHalfPlane.coe_injective.injOn).subset hs

def maximaCut (k : ℝ) (f : DiskFamily) (ξ : ℂ) (h : ℝ) : Set UpperHalfPlane :=
  {z ∈ criticalCut k f ξ h | jacobianExpression k (halfPlaneFunction f) z < 0}

def saddleCut (k : ℝ) (f : DiskFamily) (ξ : ℂ) (h : ℝ) : Set UpperHalfPlane :=
  {z ∈ criticalCut k f ξ h | 0 < jacobianExpression k (halfPlaneFunction f) z}

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def realHessian (u : ℂ → ℝ) (z v w : ℂ) : ℝ :=
  fderiv ℝ (fun t => fderiv ℝ u t w) z v

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SquaredPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def squaredReciprocalPotential (k : ℝ) (F : ℂ → ℂ) (ξ z : ℂ) : ℝ :=
  ‖F z - ξ‖ ^ 2 * z.im ^ (-2*k)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.QuadraticHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def quadratic (a b c : ℝ) (z : ℂ) : ℝ :=
  (a*z.re^2+2*b*z.re*z.im+c*z.im^2)/2

def quadraticFamily (A B C : ℝ → ℝ) (p : ℂ) (q : ℝ × ℂ) : ℝ :=
  quadratic (A q.1) (B q.1) (C q.1) (q.2-p)

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HessianLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def planeCLM (a b : ℝ) : ℂ →L[ℝ] ℝ := a•Complex.reCLM+b•Complex.imCLM

@[simp] lemma planeCLM_apply (a b : ℝ) (z : ℂ) : planeCLM a b z=a*z.re+b*z.im := by
  simp [planeCLM]

def hessianCLM (a b c : ℝ) : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  Complex.reCLM.smulRight (planeCLM a b)+Complex.imCLM.smulRight (planeCLM b c)

def affinePotential (u v : ℂ → ℝ) (q : ℝ × ℂ) : ℝ := (1-q.1)*u q.2+q.1*v q.2

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridLink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower.Grid

def bit (b : Bool) : ℤ := if b then 1 else 0

def linkIndex (b₀ b₁ b₂ b₃ b₄ b₅ : Bool) : ℤ :=
  1 - (bit b₀+bit b₁+bit b₂+bit b₃+bit b₄+bit b₅) +
    (bit b₀*bit b₁+bit b₁*bit b₂+bit b₂*bit b₃+
      bit b₃*bit b₄+bit b₄*bit b₅+bit b₅*bit b₀)

def signBound (b : Bool) (t e : ℝ) : Prop := if b then t ≤ e else -e ≤ t

end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TriangularIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower.Grid
noncomputable section

variable {V L : Type*} [LinearOrder L]

def rankBit (r : V → L) (a b : V) : ℤ := if r a < r b then 1 else 0

def topBit (r : V → L) (a b c : V) : ℤ := rankBit r b a * rankBit r c a

variable [AddCommGroup V]

def edgeFlag (r : V → L) (s v : V) : ℤ := rankBit r (v+s) v

def lowerTop₀ (r : V → L) (x y v : V) : ℤ := topBit r v (v+x) (v+x+y)
def lowerTop₁ (r : V → L) (x y v : V) : ℤ := topBit r (v+x) (v+x+y) v
def lowerTop₂ (r : V → L) (x y v : V) : ℤ := topBit r (v+x+y) v (v+x)
def upperTop₀ (r : V → L) (x y v : V) : ℤ := topBit r v (v+y) (v+x+y)
def upperTop₁ (r : V → L) (x y v : V) : ℤ := topBit r (v+y) (v+x+y) v
def upperTop₂ (r : V → L) (x y v : V) : ℤ := topBit r (v+x+y) v (v+y)

def meshIndex (r : V → L) (x y v : V) : ℤ :=
  1 - (edgeFlag r x v + rankBit r (v-x) v +
      edgeFlag r y v + rankBit r (v-y) v +
      edgeFlag r (x+y) v + rankBit r (v-(x+y)) v) +
    (lowerTop₀ r x y v + lowerTop₁ r x y (v-x) + lowerTop₂ r x y (v-(x+y)) +
      upperTop₀ r x y v + upperTop₁ r x y (v-y) + upperTop₂ r x y (v-(x+y)))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V L : Type*} [AddCommGroup V] [LinearOrder L]

def discreteDivergence (s : V) (f : V → ℤ) (v : V) : ℤ := f (v-s)-f v

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HeightIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V]

def heightRank (u : V → ℝ) (v : V) : Lex (ℝ × V) := toLex (u v,v)

variable [AddCommGroup V]

def heightIndex (u : V → ℝ) (x y v : V) : ℤ := meshIndex (heightRank u) x y v

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V] [AddCommGroup V]

def meshStar (x y v : V) : Finset V := {v,v+x,v+x+y,v+y,v-x,v-(x+y),v-y}

def meshBoundary (x y : V) (S : Finset V) : Finset V :=
  (S.biUnion (meshStar x y)).filter (fun v => ¬ meshStar x y v ⊆ S)

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LatticeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section

abbrev Lattice := Lex (ℤ × ℤ)
def ex : Lattice := toLex (1,0)
def ey : Lattice := toLex (0,1)

def latticeHeight (p q : ℤ → ℝ) (v : Lattice) : ℝ := p (ofLex v).1 + q (ofLex v).2

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.QuadraticLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower.Grid
noncomputable section

def lineIndex (p : ℤ → ℝ) (i : ℤ) : ℤ :=
  1-bit (decide (p (i+1)<p i))-bit (decide (p (i-1)≤p i))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V] [AddCommGroup V]

def RegularStar (u : V → ℝ) (x y v : V) : Prop :=
  ∃ gx gy e : ℝ, 0 < e ∧ (4*e < |gx| ∨ 4*e < |gy|) ∧
    |u (v+x)-u v-gx| ≤ e ∧ |u (v+x+y)-u v-(gx+gy)| ≤ e ∧
    |u (v+y)-u v-gy| ≤ e ∧ |u (v-x)-u v-(-gx)| ≤ e ∧
    |u (v-(x+y))-u v-(-gx-gy)| ≤ e ∧ |u (v-y)-u v-(-gy)| ≤ e

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothGridRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def StarCertificate (u : E → ℝ) (p dx dy : E) (s : ℝ) : Prop :=
  ∃ gx gy e : ℝ, 0 < e ∧ (4*e < |gx| ∨ 4*e < |gy|) ∧
    |u (p+s•dx)-u p-gx| ≤ e ∧ |u (p+s•(dx+dy))-u p-(gx+gy)| ≤ e ∧
    |u (p+s•dy)-u p-gy| ≤ e ∧ |u (p-s•dx)-u p-(-gx)| ≤ e ∧
    |u (p-s•(dx+dy))-u p-(-gx-gy)| ≤ e ∧ |u (p-s•dy)-u p-(-gy)| ≤ e

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def latticeCoord : Lattice →+ ℂ where
  toFun v := ((ofLex v).1:ℂ)+((ofLex v).2:ℂ)*Complex.I
  map_zero' := by simp
  map_add' v w := by simp [add_mul]; ring

@[simp] lemma latticeCoord_ex : latticeCoord ex = 1 := by simp [latticeCoord,ex]
@[simp] lemma latticeCoord_ey : latticeCoord ey = Complex.I := by simp [latticeCoord,ey]
@[simp] lemma latticeCoord_re (v : Lattice) : (latticeCoord v).re = (ofLex v).1 := by simp [latticeCoord]
@[simp] lemma latticeCoord_im (v : Lattice) : (latticeCoord v).im = (ofLex v).2 := by simp [latticeCoord]

def meshPoint (o : ℂ) (s : ℝ) (v : Lattice) : ℂ := o+s•latticeCoord v

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DiagonalIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def signedVertex (a c x y : ℝ) : Lattice :=
  toLex ((if 0<a then ⌈x-1/2⌉ else ⌊x+1/2⌋),(if 0<c then ⌈y-1/2⌉ else ⌊y+1/2⌋))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothIndexHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def indexAnnulus (p : ℂ) (r : ℝ) : Set ℂ :=
  Metric.closedBall p (3*r/2) \ Metric.ball p (r/2)

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothMorseIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def second (u : ℂ → ℝ) (p v w : ℂ) : ℝ := fderiv ℝ (fderiv ℝ u) p v w

def hessianDet (u : ℂ → ℝ) (p : ℂ) : ℝ := second u p 1 1*second u p Complex.I Complex.I-(second u p 1 Complex.I)^2

def morseSign (u : ℂ → ℝ) (p : ℂ) : ℤ := if 0<hessianDet u p then 1 else -1

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PlaneRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def planeRectangle (o : ℂ) (A B : ℝ) : Set ℂ :=
  {z | |z.re-o.re|≤A ∧ |z.im-o.im|≤B}

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial
namespace StrictInverseFirstPower.Grid
noncomputable section

abbrev Chain := Polynomial (Polynomial ℚ)

def x : Chain := C X
def y : Chain := X

def boundary₁ (h v d : Chain) : Chain := (x-1)*h + (y-1)*v + (x*y-1)*d

def faceH (a b : Chain) : Chain := a-y*b
def faceV (a b : Chain) : Chain := x*a-b
def faceD (a b : Chain) : Chain := b-a

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set
namespace StrictInverseFirstPower.Grid
noncomputable section

def coeff (p : Chain) (i j : ℕ) : ℚ := (p.coeff j).coeff i

@[simp] lemma coeff_sub (p q : Chain) (i j : ℕ) :
    coeff (p-q) i j = coeff p i j - coeff q i j := by simp [coeff]

@[simp] lemma coeff_x_zero (p : Chain) (j : ℕ) : coeff (x*p) 0 j = 0 := by
  simp [coeff,x,coeff_C_mul]
@[simp] lemma coeff_x_succ (p : Chain) (i j : ℕ) : coeff (x*p) (i+1) j = coeff p i j := by
  simp [coeff,x,coeff_C_mul,coeff_X_mul]
@[simp] lemma coeff_y_zero (p : Chain) (i : ℕ) : coeff (y*p) i 0 = 0 := by
  simp [coeff,y]
@[simp] lemma coeff_y_succ (p : Chain) (i j : ℕ) : coeff (y*p) i (j+1) = coeff p i j := by
  simp [coeff,y,coeff_X_mul]

structure BoundarySupported (S : Set (ℕ × ℕ)) (a b : Chain) : Prop where
  horizontal : ∀ i j, (i,j) ∉ S ∨ (i+1,j) ∉ S → coeff (faceH a b) i j = 0
  vertical : ∀ i j, (i,j) ∉ S ∨ (i,j+1) ∉ S → coeff (faceV a b) i j = 0
  diagonal : ∀ i j, (i,j) ∉ S ∨ (i+1,j+1) ∉ S → coeff (faceD a b) i j = 0

structure FaceSupported (S : Set (ℕ × ℕ)) (a b : Chain) : Prop where
  lower : ∀ i j, coeff a i j ≠ 0 → (i,j) ∈ S ∧ (i+1,j) ∈ S ∧ (i+1,j+1) ∈ S
  upper : ∀ i j, coeff b i j ≠ 0 → (i,j) ∈ S ∧ (i,j+1) ∈ S ∧ (i+1,j+1) ∈ S

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

def polyCoefficients (R : Type*) [Semiring R] : Polynomial R ≃ₗ[R] (ℕ →₀ R) :=
  (Polynomial.toFinsuppIsoLinear R).trans (AddMonoidAlgebra.coeffLinearEquiv R)

def coefficients : Chain ≃ₗ[ℚ] (ℕ × ℕ →₀ ℚ) :=
  (((polyCoefficients (Polynomial ℚ)).restrictScalars ℚ).trans
    (Finsupp.mapRange.linearEquiv (polyCoefficients ℚ))).trans
    ((Finsupp.curryLinearEquiv ℚ).symm.trans
      (Finsupp.domLCongr (Equiv.prodComm ℕ ℕ)))

@[simp] lemma coefficients_apply (p : Chain) (i j : ℕ) : coefficients p (i,j) = coeff p i j := rfl

def chainSpace (S : Set (ℕ × ℕ)) : Submodule ℚ Chain :=
  (Finsupp.supported ℚ ℚ S).comap coefficients.toLinearMap

lemma mem_chainSpace (S : Set (ℕ × ℕ)) (p : Chain) :
    p ∈ chainSpace S ↔ ∀ i j, (i,j) ∉ S → coeff p i j = 0 := by
  simp only [chainSpace,Submodule.mem_comap,Finsupp.mem_supported]
  simp only [Set.subset_def,Finset.mem_coe,Finsupp.mem_support_iff]
  constructor
  · intro h i j hi
    by_contra hn
    exact hi (h (i,j) hn)
  · intro h v hv
    by_contra he
    exact hv (h v.1 v.2 he)

def chainSpaceEquiv (S : Set (ℕ × ℕ)) : chainSpace S ≃ₗ[ℚ] (S →₀ ℚ) :=
  (coefficients.ofSubmodule' (Finsupp.supported ℚ ℚ S)).trans
    (Finsupp.supportedEquivFinsupp S)

instance finite_chainSpace (S : Set (ℕ × ℕ)) [Finite S] : FiniteDimensional ℚ (chainSpace S) :=
  (chainSpaceEquiv S).symm.finiteDimensional

def horizontalSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1+1,v.2) ∈ S}
def verticalSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1,v.2+1) ∈ S}
def diagonalSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1+1,v.2+1) ∈ S}
def lowerSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1+1,v.2) ∈ S ∧ (v.1+1,v.2+1) ∈ S}
def upperSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1,v.2+1) ∈ S ∧ (v.1+1,v.2+1) ∈ S}

abbrev EdgeSpace (S : Set (ℕ × ℕ)) := chainSpace (horizontalSet S) × chainSpace (verticalSet S) × chainSpace (diagonalSet S)
abbrev FaceSpace (S : Set (ℕ × ℕ)) := chainSpace (lowerSet S) × chainSpace (upperSet S)

def fullBoundary₁ : (Chain × Chain × Chain) →ₗ[ℚ] Chain where
  toFun p := boundary₁ p.1 p.2.1 p.2.2
  map_add' := by intros; simp only [boundary₁,Prod.fst_add,Prod.snd_add]; ring
  map_smul' := by
    intro r p
    change (x-1)*(r • p.1)+(y-1)*(r • p.2.1)+(x*y-1)*(r • p.2.2) = r • _
    simp only [mul_smul_comm,boundary₁,smul_add]

def fullBoundary₂ : (Chain × Chain) →ₗ[ℚ] (Chain × Chain × Chain) where
  toFun p := (faceH p.1 p.2,faceV p.1 p.2,faceD p.1 p.2)
  map_add' := by intros; ext <;> simp [faceH,faceV,faceD,mul_add] <;> ring
  map_smul' := by intros; ext <;> simp [faceH,faceV,faceD] <;> ring

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma chainSpace_mono {S T : Set (ℕ × ℕ)} (hST : S ⊆ T) : chainSpace S ≤ chainSpace T := by
  intro p hp
  rw [mem_chainSpace] at hp ⊢
  exact fun i j ht => hp i j (fun hs => ht (hST hs))

lemma chainSpace_shift_x {S T : Set (ℕ × ℕ)} (hST : ∀ i j, (i,j) ∈ S → (i+1,j) ∈ T)
    {p : Chain} (hp : p ∈ chainSpace S) : x*p ∈ chainSpace T := by
  rw [mem_chainSpace] at hp ⊢
  intro i j ht
  cases i with
  | zero => exact coeff_x_zero p j
  | succ i =>
    rw [coeff_x_succ]
    exact hp i j (fun hs => ht (hST i j hs))

lemma chainSpace_shift_y {S T : Set (ℕ × ℕ)} (hST : ∀ i j, (i,j) ∈ S → (i,j+1) ∈ T)
    {p : Chain} (hp : p ∈ chainSpace S) : y*p ∈ chainSpace T := by
  rw [mem_chainSpace] at hp ⊢
  intro i j ht
  cases j with
  | zero => exact coeff_y_zero p i
  | succ j =>
    rw [coeff_y_succ]
    exact hp i j (fun hs => ht (hST i j hs))

lemma chainSpace_shift_xy {S T : Set (ℕ × ℕ)} (hST : ∀ i j, (i,j) ∈ S → (i+1,j+1) ∈ T)
    {p : Chain} (hp : p ∈ chainSpace S) : x*y*p ∈ chainSpace T := by
  rw [mul_assoc]
  apply chainSpace_shift_x (S := {v | ∃ j, (v.1,j) ∈ S ∧ v.2=j+1})
  · rintro i r ⟨j,hj,rfl⟩
    exact hST i j hj
  · exact chainSpace_shift_y (S := S) (T := {v | ∃ j, (v.1,j) ∈ S ∧ v.2=j+1}) (fun i j h => ⟨j,h,rfl⟩) hp

lemma boundary₁_mem (S : Set (ℕ × ℕ)) (e : EdgeSpace S) :
    boundary₁ e.1.1 e.2.1.1 e.2.2.1 ∈ chainSpace S := by
  unfold boundary₁
  simp only [sub_mul,one_mul]
  apply (chainSpace S).add_mem
  · apply (chainSpace S).add_mem
    · exact (chainSpace S).sub_mem (chainSpace_shift_x (fun _ _ h => h.2) e.1.2)
        (chainSpace_mono (fun _ h => h.1) e.1.2)
    · exact (chainSpace S).sub_mem (chainSpace_shift_y (fun _ _ h => h.2) e.2.1.2)
        (chainSpace_mono (fun _ h => h.1) e.2.1.2)
  · exact (chainSpace S).sub_mem (chainSpace_shift_xy (fun _ _ h => h.2) e.2.2.2)
      (chainSpace_mono (fun _ h => h.1) e.2.2.2)

lemma faceH_mem (S : Set (ℕ × ℕ)) (f : FaceSpace S) :
    faceH f.1.1 f.2.1 ∈ chainSpace (horizontalSet S) := by
  exact (chainSpace _).sub_mem (chainSpace_mono (S := lowerSet S) (T := horizontalSet S) (fun _ h => ⟨h.1,h.2.1⟩) f.1.2)
    (chainSpace_shift_y (S := upperSet S) (T := horizontalSet S) (fun _ _ h => ⟨h.2.1,h.2.2⟩) f.2.2)
lemma faceV_mem (S : Set (ℕ × ℕ)) (f : FaceSpace S) :
    faceV f.1.1 f.2.1 ∈ chainSpace (verticalSet S) := by
  exact (chainSpace _).sub_mem (chainSpace_shift_x (S := lowerSet S) (T := verticalSet S) (fun _ _ h => ⟨h.2.1,h.2.2⟩) f.1.2)
    (chainSpace_mono (S := upperSet S) (T := verticalSet S) (fun _ h => ⟨h.1,h.2.1⟩) f.2.2)
lemma faceD_mem (S : Set (ℕ × ℕ)) (f : FaceSpace S) :
    faceD f.1.1 f.2.1 ∈ chainSpace (diagonalSet S) := by
  exact (chainSpace _).sub_mem (chainSpace_mono (S := upperSet S) (T := diagonalSet S) (fun _ h => ⟨h.1,h.2.2⟩) f.2.2)
    (chainSpace_mono (S := lowerSet S) (T := diagonalSet S) (fun _ h => ⟨h.1,h.2.2⟩) f.1.2)

def edgeBoundary (S : Set (ℕ × ℕ)) : EdgeSpace S →ₗ[ℚ] chainSpace S where
  toFun e := ⟨_,boundary₁_mem S e⟩
  map_add' e f := by
    apply Subtype.ext
    exact fullBoundary₁.map_add (e.1.1,e.2.1.1,e.2.2.1) (f.1.1,f.2.1.1,f.2.2.1)
  map_smul' r e := by
    apply Subtype.ext
    exact fullBoundary₁.map_smul r (e.1.1,e.2.1.1,e.2.2.1)

def faceBoundary (S : Set (ℕ × ℕ)) : FaceSpace S →ₗ[ℚ] EdgeSpace S where
  toFun f := (⟨_,faceH_mem S f⟩,⟨_,faceV_mem S f⟩,⟨_,faceD_mem S f⟩)
  map_add' f g := by
    have he := fullBoundary₂.map_add (f.1.1,f.2.1) (g.1.1,g.2.1)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Prod.ext (Subtype.ext (congrArg (fun e => e.2.1) he)) (Subtype.ext (congrArg (fun e => e.2.2) he)))
  map_smul' r f := by
    have he := fullBoundary₂.map_smul r (f.1.1,f.2.1)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Prod.ext (Subtype.ext (congrArg (fun e => e.2.1) he)) (Subtype.ext (congrArg (fun e => e.2.2) he)))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

def augmentation : Chain →ₗ[ℚ] ℚ where
  toFun p := eval 1 (eval 1 p)
  map_add' := by intros; simp
  map_smul' := by intros; simp

def vertexAugmentation (S : Set (ℕ × ℕ)) : chainSpace S →ₗ[ℚ] ℚ :=
  augmentation.comp (chainSpace S).subtype

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V L : Type*} [AddCommGroup V] [DecidableEq V] [LinearOrder L]

def vertexMass (S : Finset V) (v : V) : ℤ := if v∈S then 1 else 0

def meshEdges (S : Finset V) (x : V) : Finset V := S.filter (fun v => v+x∈S)
def meshLower (S : Finset V) (x y : V) : Finset V := S.filter (fun v => v+x∈S ∧ v+x+y∈S)
def meshUpper (S : Finset V) (x y : V) : Finset V := S.filter (fun v => v+y∈S ∧ v+x+y∈S)

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LatticeEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def natEmbed (M : ℤ) (v : ℕ × ℕ) : Lattice := toLex ((v.1:ℤ)+M,(v.2:ℤ)+M)

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoxExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def latticeBox (N M : ℕ) : Set Lattice := {v | |(ofLex v).1|≤(N:ℤ) ∧ |(ofLex v).2|≤(M:ℤ)}

def latticeTaxicab (v : Lattice) : ℝ := |((ofLex v).1:ℝ)|+|((ofLex v).2:ℝ)|

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DescendingRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set

namespace StrictInverseFirstPower
noncomputable section

def descendingRank {X : Type*} (v : X → ℝ) (S : Set X) (x : X) : ℕ :=
  {y | y ∈ S ∧ v x < v y}.ncard

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def signedCriticalFiber (k : ℝ) (f : DiskFamily) (ξ : ℂ) (positive : Bool) : Set UpperHalfPlane :=
  {z | criticalMap k (halfPlaneFunction f) z = ξ ∧
    if positive then 0 < jacobianExpression k (halfPlaneFunction f) z
    else jacobianExpression k (halfPlaneFunction f) z < 0}

def criticalRank (k : ℝ) (f : DiskFamily) (ξ : ℂ) (positive : Bool) (z : UpperHalfPlane) : ℕ :=
  descendingRank (fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w)
    (signedCriticalFiber k f ξ positive) z

abbrev RankParameters (k : ℝ) := {p : (DiskFamily × ℂ) × UpperHalfPlane | GoodPair k p.1}

def rankClosedRelation (k : ℝ) : Set (RankParameters k × UpperHalfPlane) :=
  {q | criticalMap k (halfPlaneFunction q.1.1.1.1) q.2 = q.1.1.1.2}

def rankOpenRelation (k : ℝ) (positive : Bool) : Set (RankParameters k × UpperHalfPlane) :=
  {q | (if positive then 0 < jacobianExpression k (halfPlaneFunction q.1.1.1.1) q.2
    else jacobianExpression k (halfPlaneFunction q.1.1.1.1) q.2 < 0) ∧
    criticalHeight k (halfPlaneFunction q.1.1.1.1) q.1.1.2 <
      criticalHeight k (halfPlaneFunction q.1.1.1.1) q.2}

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RankPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

instance diskFamily_standardBorel : StandardBorelSpace DiskFamily := by
  let := TopologicalSpace.metrizableSpaceMetric DiskFamily
  infer_instance

def RankPairRelation (k : ℝ) (p : RankParameters k) (w : UpperHalfPlane) : Prop :=
  p.1.2 ∈ signedCriticalFiber k p.1.1.1 p.1.1.2 true ∧
  w ∈ signedCriticalFiber k p.1.1.1 p.1.1.2 false ∧
  criticalRank k p.1.1.1 p.1.1.2 false w = criticalRank k p.1.1.1 p.1.1.2 true p.1.2 ∧
  criticalHeight k (halfPlaneFunction p.1.1.1) p.1.2 <
    criticalHeight k (halfPlaneFunction p.1.1.1) w

def rankPairingDomain (k : ℝ) : Set (RankParameters k) :=
  {p | ∃ w, RankPairRelation k p w}

abbrev AvailableRankPair (k : ℝ) := rankPairingDomain k

def availableRankPartner (k : ℝ) (p : AvailableRankPair k) : UpperHalfPlane :=
  Classical.choose p.2

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def affineUpperHomeomorph (z : UpperHalfPlane) : UpperHalfPlane ≃ₜ UpperHalfPlane where
  toFun := affineProduct z
  invFun w := ⟨((w:ℂ) - (z.re:ℂ)) / (z.im:ℂ), by
    simpa [Complex.div_ofReal_im] using div_pos w.im_pos z.im_pos⟩
  left_inv w := by
    apply UpperHalfPlane.ext
    change ((affineAt z w) - (z.re:ℂ)) / (z.im:ℂ) = w
    simp [affineAt, z.im_ne_zero]
  right_inv w := by
    apply UpperHalfPlane.ext
    change (z.re:ℂ) + (z.im:ℂ) * (((w:ℂ) - (z.re:ℂ)) / (z.im:ℂ)) = w
    field_simp [z.im_ne_zero]
    ring
  continuous_toFun :=
    (continuous_const.add (continuous_const.mul UpperHalfPlane.continuous_coe)).upperHalfPlaneMk _
  continuous_invFun :=
    ((UpperHalfPlane.continuous_coe.sub continuous_const).div_const _).upperHalfPlaneMk _

@[simp] lemma affineUpperHomeomorph_apply (z w : UpperHalfPlane) :
    affineUpperHomeomorph z w = affineProduct z w := rfl

def targetRebase (f : DiskFamily) (z : UpperHalfPlane) (ξ : ℂ) : ℂ :=
  (ξ - halfPlaneFunction f z) / ((z.im:ℂ) * deriv (halfPlaneFunction f) z)

lemma targetRebase_injective (f : DiskFamily) (z : UpperHalfPlane) :
    Function.Injective (targetRebase f z) := by
  intro ξ η he
  have hd : (z.im:ℂ) * deriv (halfPlaneFunction f) z ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr z.im_ne_zero)
      (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  simpa using ((div_left_inj' hd).mp he)

lemma criticalMap_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) :
    criticalMap k (halfPlaneFunction (rebase f z)) w =
      targetRebase f z (criticalMap k (halfPlaneFunction f) (affineProduct z w)) := by
  unfold criticalMap targetRebase
  rw [halfPlaneFunction_rebase f z w.im_pos, halfPlaneFunction_rebase_deriv]
  simp only [coe_affineProduct,affineAt_im,Complex.ofReal_mul]
  by_cases hk : k = 0
  · simp [hk]
  · field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero,
      halfPlaneFunction_deriv_ne_zero f z.im_pos,Complex.ofReal_ne_zero.mpr hk]
    ring

lemma criticalMap_rebase_eq_iff (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) (ξ : ℂ) :
    criticalMap k (halfPlaneFunction (rebase f z)) w = targetRebase f z ξ ↔
      criticalMap k (halfPlaneFunction f) (affineProduct z w) = ξ := by
  rw [criticalMap_rebase, (targetRebase_injective f z).eq_iff]

@[simp] lemma affineProduct_im (z w : UpperHalfPlane) :
    (affineProduct z w).im = z.im * w.im := affineAt_im z w

def heightRebaseScale (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) : ℝ :=
  ‖deriv (halfPlaneFunction f) z‖ / z.im^(k-1)

lemma heightRebaseScale_pos (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    0 < heightRebaseScale k f z :=
  div_pos (norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos))
    (Real.rpow_pos_of_pos z.im_pos _)

lemma criticalHeight_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) :
    criticalHeight k (halfPlaneFunction (rebase f z)) w =
      heightRebaseScale k f z * criticalHeight k (halfPlaneFunction f) (affineProduct z w) := by
  unfold criticalHeight heightRebaseScale
  rw [halfPlaneFunction_rebase_deriv]
  simp only [coe_affineProduct,affineAt_im,UpperHalfPlane.coe_im,norm_inv,norm_div]
  rw [Real.mul_rpow z.im_pos.le w.im_pos.le]
  field_simp [(norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)).ne',
    (norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f (affineAt_mapsTo z w.im_pos))).ne',
    (Real.rpow_pos_of_pos z.im_pos (k-1)).ne']

lemma reciprocalPotential_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) (ξ : ℂ) :
    reciprocalPotential k (rebase f z,targetRebase f z ξ) w =
      reciprocalPotential k (f,ξ) (affineProduct z w) / heightRebaseScale k f z := by
  unfold reciprocalPotential targetRebase heightRebaseScale
  rw [halfPlaneFunction_rebase f z w.im_pos,← sub_div]
  simp only [sub_sub_sub_cancel_right,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos z.im_pos,affineProduct_im,coe_affineProduct]
  rw [Real.mul_rpow z.im_pos.le w.im_pos.le,
    Real.rpow_sub z.im_pos,Real.rpow_one]
  field_simp [z.im_ne_zero,(Real.rpow_pos_of_pos z.im_pos k).ne',
    (Real.rpow_pos_of_pos w.im_pos k).ne',
    (norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)).ne']

lemma goodPair_rebase {k : ℝ} {f : DiskFamily} {ξ : ℂ} (hg : GoodPair k (f,ξ))
    (z : UpperHalfPlane) : GoodPair k (rebase f z,targetRebase f z ξ) := by
  refine ⟨?_,?_,?_⟩
  · apply (compactPotential_iff _ _).mpr
    intro r hr
    have hc := (compactPotential_iff _ _).mp hg.1
      (r * heightRebaseScale k f z) (mul_pos hr (heightRebaseScale_pos k f z))
    convert (affineUpperHomeomorph z).isCompact_preimage.mpr hc using 1
    ext w
    simp only [mem_ofPred_eq,mem_preimage,affineUpperHomeomorph_apply]
    rw [reciprocalPotential_rebase,div_le_iff₀ (heightRebaseScale_pos k f z)]
  · intro w hw
    rw [jacobianExpression_rebase]
    exact hg.2.1 (affineProduct z w) ((criticalMap_rebase_eq_iff k f z w ξ).mp hw)
  · intro v w hv hw he
    apply (affineUpperHomeomorph z).injective
    apply hg.2.2 (affineProduct z v) (affineProduct z w)
      ((criticalMap_rebase_eq_iff k f z v ξ).mp hv)
      ((criticalMap_rebase_eq_iff k f z w ξ).mp hw)
    rw [criticalHeight_rebase,criticalHeight_rebase] at he
    exact mul_left_cancel₀ (heightRebaseScale_pos k f z).ne' he

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RankCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma signedCriticalFiber_rebase (k : ℝ) (f : DiskFamily) (ξ : ℂ)
    (z : UpperHalfPlane) (positive : Bool) :
    signedCriticalFiber k (rebase f z) (targetRebase f z ξ) positive =
      (affineUpperHomeomorph z) ⁻¹' signedCriticalFiber k f ξ positive := by
  ext w
  simp only [signedCriticalFiber,mem_ofPred_eq,mem_preimage,affineUpperHomeomorph_apply,
    criticalMap_rebase_eq_iff,jacobianExpression_rebase,coe_affineProduct]

lemma criticalRank_rebase (k : ℝ) (f : DiskFamily) (ξ : ℂ)
    (z w : UpperHalfPlane) (positive : Bool) :
    criticalRank k (rebase f z) (targetRebase f z ξ) positive w =
      criticalRank k f ξ positive (affineProduct z w) := by
  unfold criticalRank descendingRank
  have he : {v | v ∈ signedCriticalFiber k (rebase f z) (targetRebase f z ξ) positive ∧
      criticalHeight k (halfPlaneFunction (rebase f z)) w <
        criticalHeight k (halfPlaneFunction (rebase f z)) v} =
      (affineUpperHomeomorph z) ⁻¹' {v | v ∈ signedCriticalFiber k f ξ positive ∧
        criticalHeight k (halfPlaneFunction f) (affineProduct z w) <
          criticalHeight k (halfPlaneFunction f) v} := by
    ext v
    simp only [signedCriticalFiber_rebase,mem_ofPred_eq,mem_preimage,
      affineUpperHomeomorph_apply,criticalHeight_rebase,
      mul_lt_mul_iff_right₀ (heightRebaseScale_pos k f z)]
  rw [he]
  exact Set.ncard_preimage_of_injective_subset_range (affineUpperHomeomorph z).injective
    (by rw [(affineUpperHomeomorph z).surjective.range_eq]; exact subset_univ _)

lemma rankPairRelation_rebase_iff {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (z w v : UpperHalfPlane) :
    RankPairRelation k ⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩ v ↔
      RankPairRelation k ⟨((f,ξ),affineProduct z w),hg⟩ (affineProduct z v) := by
  simp only [RankPairRelation,signedCriticalFiber_rebase,mem_preimage,
    affineUpperHomeomorph_apply,criticalRank_rebase,criticalHeight_rebase,
    mul_lt_mul_iff_right₀ (heightRebaseScale_pos k f z)]

lemma rankPairingDomain_rebase_iff {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (z w : UpperHalfPlane) :
    (⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩ : RankParameters k) ∈
      rankPairingDomain k ↔
    (⟨((f,ξ),affineProduct z w),hg⟩ : RankParameters k) ∈ rankPairingDomain k := by
  change (∃ v, RankPairRelation k _ v) ↔ ∃ v, RankPairRelation k _ v
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨affineProduct z v,(rankPairRelation_rebase_iff hg z w v).mp hv⟩
  · rintro ⟨v,hv⟩
    obtain ⟨a,ha⟩ := (affineUpperHomeomorph z).surjective v
    change affineProduct z a = v at ha
    refine ⟨a,(rankPairRelation_rebase_iff hg z w a).mpr ?_⟩
    rw [ha]
    exact hv

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def availableSource (k : ℝ) (p : AvailableRankPair k) : DiskFamily × UpperHalfPlane :=
  (p.1.1.1.1,p.1.1.2)

def sourcePairingDomain (k : ℝ) : Set (DiskFamily × UpperHalfPlane) := range (availableSource k)

def sourcePair (k : ℝ) (q : sourcePairingDomain k) : AvailableRankPair k := q.2.choose

def sourcePartnerOn (k : ℝ) (q : sourcePairingDomain k) : UpperHalfPlane :=
  availableRankPartner k (sourcePair k q)

def sourcePartner (k : ℝ) (q : DiskFamily × UpperHalfPlane) : UpperHalfPlane :=
  by
    classical
    exact if h : q ∈ sourcePairingDomain k then sourcePartnerOn k ⟨q,h⟩ else UpperHalfPlane.I

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PairingCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def partnerRatio (k : ℝ) (q : DiskFamily × UpperHalfPlane) : ℝ :=
  by
    classical
    exact if q ∈ sourcePairingDomain k then
    (criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q) /
      criticalHeight k (halfPlaneFunction q.1) q.2)^3 else 0

def truncatedPairingDomain (k N : ℝ) : Set (DiskFamily × UpperHalfPlane) :=
  {q | q ∈ sourcePairingDomain k ∧ 1/N ≤ (sourcePartner k q).im / q.2.im ∧
    (sourcePartner k q).im / q.2.im ≤ N ∧
    |(sourcePartner k q).re - q.2.re| ≤ N*q.2.im}

@[simp] lemma affineProduct_re (t w : UpperHalfPlane) :
    (affineProduct t w).re = t.re+t.im*w.re := by simp [affineProduct,affineAt]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.FiberSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory
open scoped ENNReal
namespace StrictInverseFirstPower
noncomputable section

def fiberSum {X Y : Type*} (G : X → Y) (s : Set X) (h : X → ℝ≥0∞) (ξ : Y) : ℝ≥0∞ :=
  ∑' z : {z | z ∈ s ∧ G z = ξ}, h z

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def unsignedTargetWeight (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1) * ‖halfPlaneQ f z‖^3)

def jacobianPart (k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) : ℝ :=
  max (if positive then jacobianExpression k (halfPlaneFunction f) z else
    -jacobianExpression k (halfPlaneFunction f) z) 0

def sourceMassDensity (β k : ℝ) (f : DiskFamily) (positive : Bool)
    (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1) * ‖halfPlaneQ f z‖ * jacobianPart k f positive z)

def signedJacobianLocus (k : ℝ) (f : DiskFamily) (positive : Bool) : Set ℂ :=
  {z | 0 < z.im ∧ if positive then 0 < jacobianExpression k (halfPlaneFunction f) z
    else jacobianExpression k (halfPlaneFunction f) z < 0}

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LawDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def AffineProbabilityLaw (μ : ProbabilityMeasure DiskFamily) (β : ℝ) : Prop :=
  ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
    (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)

def spatialWeight (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1) * ‖halfPlaneQ f z‖)

@[simp] lemma affineProduct_I (z : UpperHalfPlane) : affineProduct z UpperHalfPlane.I = z := by
  apply UpperHalfPlane.ext
  simp only [coe_affineProduct,UpperHalfPlane.coe_I,affineAt]
  exact z.1.re_add_im

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

abbrev upperArea : Measure UpperHalfPlane := (volume : Measure ℂ).comap UpperHalfPlane.coe

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.NormalizedTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def badSourceTest (k : ℝ) : DiskFamily × UpperHalfPlane → ℝ≥0∞ :=
  (sourcePairingDomain k)ᶜ.indicator (fun _ => 1)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def transportTest (k N : ℝ) : DiskFamily × UpperHalfPlane → ℝ≥0∞ :=
  (truncatedPairingDomain k N).indicator (fun q => ENNReal.ofReal (partnerRatio k q))

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoxTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def upperBox (S a b : ℝ) : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' complexBox S a b

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CircleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def horizontalQMean (y : ℝ) (hy : 0 < y) : C(DiskFamily, ℝ) :=
  (1/2:ℝ) • ∫ x in (-1:ℝ)..1, affineOperator (xyPoint x y hy) 1

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def arcDenom (r t : ℝ) : ℝ := 1 + 2*r*Real.cos t + r^2
def arcX (r t : ℝ) : ℝ := 2*r*Real.sin t / arcDenom r t
def arcY (r t : ℝ) : ℝ := (1-r^2) / arcDenom r t
def arcXDeriv (r t : ℝ) : ℝ :=
  (2*r*(1+r^2)*Real.cos t+4*r^2)/(arcDenom r t)^2

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def diskNegateMap (f : C(UnitDisk,ℂ)) : C(UnitDisk,ℂ) :=
  ⟨fun z => -f ⟨-z,by simpa only [mem_ball,dist_zero_right,norm_neg] using z.property⟩,
    (f.continuous.comp ((continuous_subtype_val.neg).subtype_mk _)).neg⟩

lemma diskNegateMap_extension (f : C(UnitDisk,ℂ)) (z : ℂ) :
    diskExtension (diskNegateMap f) z = -diskExtension f (-z) := by
  classical
  by_cases hz : z ∈ ball (0:ℂ) 1
  · have hm : -z ∈ ball (0:ℂ) 1 := by simpa using hz
    simp only [diskExtension,dite_eq_left hz,dite_eq_left hm]
    rfl
  · have hm : -z ∉ ball (0:ℂ) 1 := by simpa using hz
    simp only [diskExtension,dite_eq_right hz,dite_eq_right hm,neg_zero]

lemma diskNegateMap_hasDerivAt (f : DiskFamily) {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    HasDerivAt (diskExtension (diskNegateMap f.val)) (deriv (diskExtension f.val) (-z)) z := by
  have hm : -z ∈ ball (0:ℂ) 1 := by simpa using hz
  have hh := ((f.property.1.differentiableAt (isOpen_ball.mem_nhds hm)).hasDerivAt.comp z
    (hasDerivAt_id z).neg).neg
  simp only [mul_neg,mul_one,neg_neg] at hh
  rw [show diskExtension (diskNegateMap f.val) = (fun w => -diskExtension f.val (-w)) from
    funext (diskNegateMap_extension f.val)]
  exact hh

def diskNegateFamily (f : DiskFamily) : DiskFamily := ⟨diskNegateMap f.val, by
  refine ⟨fun z hz => (diskNegateMap_hasDerivAt f hz).differentiableAt.differentiableWithinAt,
    ?_, ?_, ?_⟩
  · intro z hz w hw he
    simp only [diskNegateMap_extension,neg_inj] at he
    exact neg_injective (f.property.2.1 (by simpa using hz) (by simpa using hw) he)
  · simp [diskNegateMap_extension,f.property.2.2.1]
  · simpa only [neg_zero,f.property.2.2.2] using
      (diskNegateMap_hasDerivAt f (mem_ball_self zero_lt_one)).deriv⟩

def circleInverseDensity (f : DiskFamily) (r t : ℝ) : ℝ :=
  ‖deriv (diskExtension f.val) ((r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹

def leftArcInverseDensity (f : DiskFamily) (r t : ℝ) : ℝ :=
  ‖deriv (diskExtension f.val) (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.UniformMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def normalizedDiskMap (f : ℂ → ℂ) (hf : NormalizedUnivalent f) : C(UnitDisk,ℂ) :=
  ⟨fun z => f z,hf.1.continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)⟩

lemma normalizedDiskMap_extension (f : ℂ → ℂ) (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ disk) : diskExtension (normalizedDiskMap f hf) z = f z := by
  have hz' : z ∈ Metric.ball (0:ℂ) 1 := hz
  simp only [diskExtension,dite_eq_left hz',normalizedDiskMap,ContinuousMap.coe_mk]

lemma normalizedDiskMap_deriv (f : ℂ → ℂ) (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ disk) : deriv (diskExtension (normalizedDiskMap f hf)) z = deriv f z := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact normalizedDiskMap_extension f hf hw

def normalizedDiskFamily (f : ℂ → ℂ) (hf : NormalizedUnivalent f) : DiskFamily :=
  ⟨normalizedDiskMap f hf, by
    refine ⟨hf.1.congr (fun z hz => normalizedDiskMap_extension f hf hz),?_,?_,?_⟩
    · intro z hz w hw he
      exact hf.2.1 hz hw (by simpa only [normalizedDiskMap_extension f hf hz,
        normalizedDiskMap_extension f hf hw] using he)
    · rw [normalizedDiskMap_extension f hf (mem_ball_self zero_lt_one),hf.2.2.1]
    · rw [normalizedDiskMap_deriv f hf (mem_ball_self zero_lt_one),hf.2.2.2]⟩

end
end StrictInverseFirstPower

end

end OAI
end


