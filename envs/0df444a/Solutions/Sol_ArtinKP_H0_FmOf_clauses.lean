-- Prove2me | solution 1 for ArtinKP.H0.FmOf_clauses
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:41.472971+00:00
-- url     : https://prove2.me/submissions/d87b5aa5-7df7-449c-9de5-fc9130a443d5

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_K_kappaB_iteratedDeriv_bound_shift

section
-- module Solutions.Artin.KP.K_Bessel
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 1: the K-Bessel function

`besselK μ z = ½ ∫_0^∞ t^{μ−1} exp(−(z/2)(t + 1/t)) dt` (`μ : ℂ`, `z : ℝ`; meaningful for `z > 0`),
defined as half the Mellin transform of `besselKer z`.  Mathlib only.

* `besselK_differentiable`: entire in `μ`;
* `besselK_neg`: `K_{−μ} = K_μ`;
* `besselK_ofReal`, `besselKR_pos`: real and positive for real `μ`;
* `norm_besselK_le`: `‖K_μ(z)‖ ≤ K_{Re μ}(z)`;
* `besselKR_le_exp_mul`: `K_μ(z) ≤ e^{−(z−z₀)} K_μ(z₀)` for `z ≥ z₀ > 0`;
* `besselKR_le_gamma`: `K_μ(z) ≤ ½ Γ(|μ|) (z/2)^{−|μ|}` (`μ ≠ 0`);
* `besselKR_le_two_mul`: `K_μ(z) ≤ 2 K_M(z)` for `|μ| ≤ M`;
* `besselKR_le_min`: `K_μ(z) ≤ C min(z^{−|μ|}, z^{−N})` uniformly for `a ≤ |μ| ≤ M ≤ N`;
* `besselK_eq_schlafli`: the Schläfli form `½ (z/2)^{−μ} ∫ t^{μ−1} exp(−t − z²/(4t)) dt`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter Asymptotics Topology

noncomputable section

theorem besselK_ofReal (μ z : ℝ) : besselK (μ : ℂ) z = (besselKR μ z : ℂ) := by
  unfold besselK besselKR mellin
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · norm_num
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [smul_eq_mul, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_cpow ht'.le]
    push_cast
    rfl

end

end ArtinKP.K
end

section
-- module Solutions.Artin.T12.L3X_Meas
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem countable_field (F : Type*) [Field F] [NumberField F] : Countable F := by
  have b := Module.finBasis ℚ F
  exact b.equivFun.injective.countable

instance instCountableSFin : Countable (SFin 𝔪 k) := by
  have := countable_field F
  have : Countable Fˣ := Function.Injective.countable (f := fun u : Fˣ => (u : F))
    Units.val_injective
  have : Countable (Fˣ ⧸ SLevel 𝔪 k) := (QuotientGroup.mk_surjective).countable
  exact Countable.of_equiv (Fˣ ⧸ SLevel 𝔪 k) Additive.ofMul

/-! ### The finite norm -/

/-! ### `lnorm` -/

/-! ### Slices -/

variable (w₀ : InfinitePlace F)


/-! ### Measure preservation -/

instance instMeasurableAddSFin_solutions : MeasurableAdd (SFin 𝔪 k) :=
  ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩

instance instMeasurableNegSFin_solutions : MeasurableNeg (SFin 𝔪 k) := ⟨measurable_of_countable _⟩

instance instMeasurableAdd₂SFin_solutions : MeasurableAdd₂ (SFin 𝔪 k) := ⟨measurable_of_countable _⟩

instance instMeasurableAddSModel : MeasurableAdd (SModel 𝔪 k) := by
  constructor
  · intro c
    exact (measurable_fst.const_add c.1).prodMk
      (((measurable_fst.comp measurable_snd).const_add c.2.1).prodMk
        ((measurable_snd.comp measurable_snd).const_add c.2.2))
  · intro c
    exact (measurable_fst.add_const c.1).prodMk
      (((measurable_fst.comp measurable_snd).add_const c.2.1).prodMk
        ((measurable_snd.comp measurable_snd).add_const c.2.2))

instance instMeasurableNegSModel : MeasurableNeg (SModel 𝔪 k) := by
  constructor
  exact measurable_fst.neg.prodMk ((measurable_fst.comp measurable_snd).neg.prodMk
    (measurable_snd.comp measurable_snd).neg)

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_V
/-! # L3X_V: the radial profile `V` of (5.21) and its Mellin transform

* `Vprof w₀ 𝔪 k κ u`: the sheet integral over `X_u` of `1_{y_f = 0} ∏_w κ(|y_w|_w)`.
* `Vprof_eq`: `V(u) = (2π)^{|W|} ∫_{x' ∈ ℝ^{W∖w₀}} κ(e^{log u − Σx'}) ∏_{w'} κ(e^{x'_{w'}})`.
* `Vprof_mellin`: measurability and `V̂(s) = (2π)^{|W|} cκ^{|W|} (Aκ^{|W|})^s (Γ(s+5/6)Γ(s+7/6))^{|W|}`
  for `Re s > −5/6`, from `κ̂(s) = cκ Aκ^s Γ(s+5/6)Γ(s+7/6)` (Fubini; `κ ≥ 0`).
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The exponential substitution in the Mellin transform -/

theorem cpow_exp_eq (a : ℝ) (s : ℂ) :
    ((Real.exp a : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ) ^ (s - 1) = Complex.exp (s * a) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos a).ne'),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; ring

theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ a : ℝ, Complex.exp (s * a) * f (Real.exp a) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [mellin, h]
  congr 1; funext a
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

theorem mellinConvergent_iff_exp (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun a : ℝ => Complex.exp (s * a) * f (Real.exp a)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, integrableOn_univ] at h
  rw [MellinConvergent, h]
  refine integrable_congr (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

/-! ### The Mellin transform of `V` -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3J_Kappa
attribute [-instance] _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinKP.X.instSigmaFiniteXVol
/-! # L3J_Kappa: the κ-clauses of the corrected KP cut are satisfiable

`κ₀(t) = ∫ g_{5/6}(log t − y) g_{7/6}(y) dy`, with `g_a(b) = exp(a b − e^b)`, is the Mellin
convolution of `t^{5/6} e^{-t}` and `t^{7/6} e^{-t}`. So `mellin κ₀ s = Γ(s+5/6) Γ(s+7/6)` for
`Re s > −5/6`, and `κ₀(t) ≤ C_N min(t^α, t^{-N})` for every `0 < α ≤ 5/6` and every `N > 0`.
It is the archimedean Whittaker profile `t K_{1/3}(2√t)` of (5.7)/(5.11), up to normalization. -/

namespace ArtinPrimitiveRoots.L3J

open MeasureTheory Set

noncomputable section

theorem gA_pos (a b : ℝ) : 0 < gA a b := Real.exp_pos _

theorem continuous_gA (a : ℝ) : Continuous (gA a) := by
  unfold gA; fun_prop

/-- `exp(s b) g_a(b) = exp((s + a) b) exp(−e^b)`. -/
theorem cexp_mul_gA (s : ℂ) (a b : ℝ) :
    Complex.exp (s * b) * (gA a b : ℂ) =
      Complex.exp ((s + a) * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ) := by
  unfold gA
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `Γ(c)` in exponential coordinates. -/
theorem gamma_exp {c : ℂ} (hc : 0 < c.re) :
    Integrable (fun b : ℝ => Complex.exp (c * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ)) ∧
    ∫ b : ℝ, Complex.exp (c * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ) = Complex.Gamma c := by
  have hm : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) c := by
    unfold MellinConvergent
    refine (Complex.GammaIntegral_convergent hc).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  refine ⟨(L3X.mellinConvergent_iff_exp _ c).1 hm, ?_⟩
  rw [Complex.Gamma_eq_integral hc, Complex.GammaIntegral_eq_mellin, L3X.mellin_eq_integral_exp]

theorem integrable_cexp_gA {s : ℂ} {a : ℝ} (h : 0 < s.re + a) :
    Integrable (fun b : ℝ => Complex.exp (s * b) * (gA a b : ℂ)) := by
  have := (gamma_exp (c := s + a) (by simpa using h)).1
  simpa only [cexp_mul_gA] using this

theorem integral_cexp_gA {s : ℂ} {a : ℝ} (h : 0 < s.re + a) :
    ∫ b : ℝ, Complex.exp (s * b) * (gA a b : ℂ) = Complex.Gamma (s + a) := by
  have := (gamma_exp (c := s + a) (by simpa using h)).2
  simpa only [cexp_mul_gA] using this

theorem integrable_gA {a : ℝ} (ha : 0 < a) : Integrable (gA a) := by
  have h := (integrable_cexp_gA (s := 0) (a := a) (by simpa using ha)).norm
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [zero_mul, Complex.exp_zero, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (gA_pos a b).le]

theorem measurable_kappa0 : Measurable kappa0 := by
  have hfm : Measurable (fun q : ℝ × ℝ => gA (5 / 6) (q.1 - q.2) * gA (7 / 6) q.2) := by
    have : Continuous (fun q : ℝ × ℝ => gA (5 / 6) (q.1 - q.2) * gA (7 / 6) q.2) :=
      ((continuous_gA _).comp (continuous_fst.sub continuous_snd)).mul
        ((continuous_gA _).comp continuous_snd)
    exact this.measurable
  have : Measurable (fun x : ℝ => ∫ y, gA (5 / 6) (x - y) * gA (7 / 6) y) :=
    (hfm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  exact this.comp Real.measurable_log

theorem kappa0_nonneg (t : ℝ) : 0 ≤ kappa0 t :=
  integral_nonneg fun y => (mul_pos (gA_pos _ _) (gA_pos _ _)).le

/-- The pointwise identity `g_{5/6}(x−y) g_{7/6}(y) = e^{5x/6} exp(y/3 − e^{x−y} − e^y)`. -/
theorem gA_mul_eq (x y : ℝ) :
    gA (5 / 6) (x - y) * gA (7 / 6) y =
      Real.exp (5 / 6 * x) * Real.exp (1 / 3 * y - Real.exp (x - y) - Real.exp y) := by
  unfold gA
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem kappa0_le_small (x : ℝ) :
    kappa0 (Real.exp x) ≤ Real.exp (5 / 6 * x) * ∫ y, gA (1 / 3) y := by
  unfold kappa0
  rw [Real.log_exp, ← integral_const_mul]
  have hi : Integrable (fun y => Real.exp (5 / 6 * x) * gA (1 / 3) y) :=
    (integrable_gA (by norm_num)).const_mul _
  have hle : ∀ y, gA (5 / 6) (x - y) * gA (7 / 6) y ≤ Real.exp (5 / 6 * x) * gA (1 / 3) y := by
    intro y
    rw [gA_mul_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have := Real.exp_pos (x - y)
    linarith
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
    (mul_pos (gA_pos _ _) (gA_pos _ _)).le) hi (Filter.Eventually.of_forall hle)

/-- `e^{x−y} + e^y ≥ e^{x/2} + e^y/2`. -/
theorem exp_sum_ge (x y : ℝ) :
    Real.exp (x / 2) + Real.exp y / 2 ≤ Real.exp (x - y) + Real.exp y := by
  set A := Real.exp (x - y)
  set B := Real.exp y
  set E := Real.exp (x / 2)
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 < B := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hAB : A * B = E * E := by
    simp only [A, B, E]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h2 : E ≤ A + B / 2 := by
    nlinarith [sq_nonneg (A - B / 2), sq_nonneg (E - (A + B / 2))]
  linarith

theorem kappa0_le_large (x : ℝ) :
    kappa0 (Real.exp x) ≤
      Real.exp (5 / 6 * x) * Real.exp (-Real.exp (x / 2)) *
        (Real.exp (Real.log 2 / 3) * ∫ y, gA (1 / 3) y) := by
  unfold kappa0
  rw [Real.log_exp]
  set K := Real.exp (5 / 6 * x) * Real.exp (-Real.exp (x / 2)) * Real.exp (Real.log 2 / 3)
  have hshift : ∀ y, Real.exp (1 / 3 * y - Real.exp y / 2) =
      Real.exp (Real.log 2 / 3) * gA (1 / 3) (y - Real.log 2) := by
    intro y
    unfold gA
    rw [← Real.exp_add, show Real.exp (y - Real.log 2) = Real.exp y / 2 by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
    congr 1; ring
  have hi : Integrable (fun y => K * gA (1 / 3) (y - Real.log 2)) :=
    ((integrable_gA (by norm_num)).comp_sub_right _).const_mul _
  have hle : ∀ y, gA (5 / 6) (x - y) * gA (7 / 6) y ≤ K * gA (1 / 3) (y - Real.log 2) := by
    intro y
    rw [gA_mul_eq]
    have h1 : Real.exp (1 / 3 * y - Real.exp (x - y) - Real.exp y) ≤
        Real.exp (-Real.exp (x / 2)) * Real.exp (1 / 3 * y - Real.exp y / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := exp_sum_ge x y
      linarith
    rw [hshift] at h1
    calc Real.exp (5 / 6 * x) * Real.exp (1 / 3 * y - Real.exp (x - y) - Real.exp y)
        ≤ Real.exp (5 / 6 * x) * (Real.exp (-Real.exp (x / 2)) *
            (Real.exp (Real.log 2 / 3) * gA (1 / 3) (y - Real.log 2))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = K * gA (1 / 3) (y - Real.log 2) := by simp only [K]; ring
  have := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
    (mul_pos (gA_pos (5 / 6) (x - y)) (gA_pos (7 / 6) y)).le) hi (Filter.Eventually.of_forall hle)
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => gA (1 / 3) y)]
  simp only [K]; ring

/-- `t^{a} e^{-√t} ≤ ⌈2a⌉₊!` for `t ≥ 1`, `a ≥ 0`. -/
theorem rpow_mul_exp_neg_sqrt_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 1 ≤ t) :
    t ^ a * Real.exp (-Real.sqrt t) ≤ (Nat.ceil (2 * a)).factorial := by
  set u := Real.sqrt t
  have hu1 : 1 ≤ u := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ht
  have hu0 : 0 ≤ u := by linarith
  set m := Nat.ceil (2 * a)
  have htu : t = u ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.sq_sqrt (by linarith)]
  have h1 : t ^ a = u ^ (2 * a) := by
    rw [htu, ← Real.rpow_mul hu0]
  have h2 : u ^ (2 * a) ≤ u ^ (m : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (Nat.le_ceil _)
  have h3 : u ^ (m : ℝ) = u ^ m := Real.rpow_natCast u m
  have h4 : u ^ m / m.factorial ≤ Real.exp u := Real.pow_div_factorial_le_exp (x := u) hu0 m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h4
  rw [h1]
  calc u ^ (2 * a) * Real.exp (-u) ≤ u ^ m * Real.exp (-u) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ ≤ Real.exp u * m.factorial * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = m.factorial := by rw [mul_comm (Real.exp u), mul_assoc, ← Real.exp_add]; simp

theorem kappa0_bound {α : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) {N : ℝ} (hN : 0 < N) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → kappa0 t ≤ C * min (t ^ α) (t ^ (-N)) := by
  set I := ∫ y, gA (1 / 3) y
  have hI : 0 ≤ I := integral_nonneg fun y => (gA_pos _ _).le
  set M : ℝ := ((Nat.ceil (2 * (N + 5 / 6))).factorial : ℝ)
  refine ⟨max I (Real.exp (Real.log 2 / 3) * I * M), fun t ht => ?_⟩
  have hx := Real.exp_log ht
  set x := Real.log t
  rcases le_or_gt t 1 with h1 | h1
  · -- small `t`: `κ₀(t) ≤ I t^{5/6} ≤ I t^α`, and the min is `t^α`
    have hmin : min (t ^ α) (t ^ (-N)) = t ^ α := by
      refine min_eq_left ?_
      have : t ^ α ≤ 1 := Real.rpow_le_one ht.le h1 hα.le
      have : 1 ≤ t ^ (-N) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht h1 (by linarith)
      linarith
    rw [hmin]
    have hk := kappa0_le_small x
    rw [hx] at hk
    have he : Real.exp (5 / 6 * x) = t ^ (5 / 6 : ℝ) := by
      rw [← hx, ← Real.exp_mul]; ring_nf
    rw [he] at hk
    have hpow : t ^ (5 / 6 : ℝ) ≤ t ^ α := Real.rpow_le_rpow_of_exponent_ge ht h1 hα'
    calc kappa0 t ≤ t ^ (5 / 6 : ℝ) * I := hk
      _ ≤ t ^ α * I := mul_le_mul_of_nonneg_right hpow hI
      _ = I * t ^ α := mul_comm _ _
      _ ≤ max I (Real.exp (Real.log 2 / 3) * I * M) * t ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le _)
  · -- large `t`: `κ₀(t) ≤ 2^{1/3} I t^{5/6} e^{−√t} ≤ 2^{1/3} I M t^{−N}`
    have hmin : min (t ^ α) (t ^ (-N)) = t ^ (-N) := by
      refine min_eq_right ?_
      have : t ^ (-N) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith)
      have : 1 ≤ t ^ α := Real.one_le_rpow h1.le hα.le
      linarith
    rw [hmin]
    have hk := kappa0_le_large x
    rw [hx] at hk
    have he : Real.exp (5 / 6 * x) = t ^ (5 / 6 : ℝ) := by
      rw [← hx, ← Real.exp_mul]; ring_nf
    have hs : Real.exp (x / 2) = Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, ← hx, ← Real.exp_mul]; ring_nf
    rw [he, hs] at hk
    have hb := rpow_mul_exp_neg_sqrt_le (a := N + 5 / 6) (by linarith) h1.le
    have hsplit : t ^ (5 / 6 : ℝ) = t ^ (N + 5 / 6) * t ^ (-N) := by
      rw [← Real.rpow_add ht]; ring_nf
    have hc : 0 ≤ Real.exp (Real.log 2 / 3) * I := mul_nonneg (Real.exp_pos _).le hI
    calc kappa0 t ≤ t ^ (5 / 6 : ℝ) * Real.exp (-Real.sqrt t) * (Real.exp (Real.log 2 / 3) * I) := hk
      _ = (t ^ (N + 5 / 6) * Real.exp (-Real.sqrt t)) * (Real.exp (Real.log 2 / 3) * I) *
            t ^ (-N) := by rw [hsplit]; ring
      _ ≤ M * (Real.exp (Real.log 2 / 3) * I) * t ^ (-N) := by
          gcongr
      _ = Real.exp (Real.log 2 / 3) * I * M * t ^ (-N) := by ring
      _ ≤ max I (Real.exp (Real.log 2 / 3) * I * M) * t ^ (-N) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

/-- The Mellin transform: `mellin κ₀ s = Γ(s + 5/6) Γ(s + 7/6)` for `Re s > −5/6`. -/
theorem kappa0_mellin (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (fun t => (kappa0 t : ℂ)) s ∧
      mellin (fun t => (kappa0 t : ℂ)) s =
        Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) := by
  set G₁ : ℝ → ℂ := fun b => Complex.exp (s * b) * (gA (5 / 6) b : ℂ)
  set G₂ : ℝ → ℂ := fun b => Complex.exp (s * b) * (gA (7 / 6) b : ℂ)
  have hG₁ : Integrable G₁ := integrable_cexp_gA (by linarith)
  have hG₂ : Integrable G₂ := integrable_cexp_gA (by linarith)
  have iG₁ : ∫ b, G₁ b = Complex.Gamma (s + 5 / 6) := by
    rw [integral_cexp_gA (by linarith)]; push_cast; ring_nf
  have iG₂ : ∫ b, G₂ b = Complex.Gamma (s + 7 / 6) := by
    rw [integral_cexp_gA (by linarith)]; push_cast; ring_nf
  set f₂ : ℝ × ℝ → ℂ := fun q => G₁ (q.1 - q.2) * G₂ q.2
  have hf₂m : AEStronglyMeasurable f₂ (volume.prod volume) := by
    have hc : Continuous f₂ := by
      simp only [f₂, G₁, G₂]
      have := continuous_gA (5 / 6); have := continuous_gA (7 / 6)
      fun_prop
    exact hc.aestronglyMeasurable
  have hf₂i : Integrable f₂ (volume.prod volume) := by
    rw [integrable_prod_iff' hf₂m]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · exact (hG₁.comp_sub_right y).mul_const (G₂ y)
    · have : (fun y : ℝ => ∫ x, ‖f₂ (x, y)‖) = fun y => (∫ b, ‖G₁ b‖) * ‖G₂ y‖ := by
        funext y
        simp only [f₂, norm_mul]
        rw [integral_mul_const, integral_sub_right_eq_self (fun b => ‖G₁ b‖)]
      rw [this]
      exact hG₂.norm.const_mul _
  have hpt : ∀ x : ℝ, Complex.exp (s * x) * ((kappa0 (Real.exp x) : ℝ) : ℂ) = ∫ y, f₂ (x, y) := by
    intro x
    simp only [kappa0, Real.log_exp]
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [f₂, G₁, G₂, Complex.ofReal_mul]
    rw [show Complex.exp (s * (x : ℂ)) = Complex.exp (s * ((x - y : ℝ) : ℂ)) *
        Complex.exp (s * (y : ℂ)) by rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  refine ⟨?_, ?_⟩
  · rw [L3X.mellinConvergent_iff_exp]
    simp only [hpt]
    exact hf₂i.integral_prod_left
  · rw [L3X.mellin_eq_integral_exp]
    simp only [hpt]
    rw [integral_integral_swap (f := fun x y => f₂ (x, y))
      (by have : Function.uncurry (fun x y => f₂ (x, y)) = f₂ := by funext q; rfl
          rw [this]; exact hf₂i)]
    have hin : ∀ y : ℝ, ∫ x, f₂ (x, y) = Complex.Gamma (s + 5 / 6) * G₂ y := by
      intro y
      simp only [f₂]
      rw [integral_mul_const, integral_sub_right_eq_self G₁, iG₁]
    simp only [hin]
    rw [integral_const_mul, iG₂]

end

end ArtinPrimitiveRoots.L3J
end

section
-- module Solutions.Artin.KP.K_Kappa
/-! # WP-K, file 3: the profile `κ`

* `cc a b x = ∫ g_a(x−y) g_b(y) dy` (`g_a(u) = exp(a u − e^u)`, `L3J.gA`): the Mellin convolution of
  `t^a e^{−t}` and `t^b e^{−t}` in the variable `x = log t`; `L3J.kappa0 (e^x) = cc (5/6) (7/6) x`.
  `hasDerivAt_cc`: `cc a b ' = a · cc a b − cc (a+1) b`; `contDiff_cc`: smooth;
  `cc_bound`: `cc a b x ≤ C min(e^{αx}, e^{−Nx})` for `a ≠ b`, `0 < α ≤ min a b`.
* `kappa0_eq_bessel`: `κ₀(t) = 2 t K_{1/3}(2√t)`.
* `kappaB c t = t · K_{1/3}(c √t)` (`t > 0`; `0` otherwise) `= (2/c²) κ₀(c² t/4)`;
  `kappaB_clauses`: all `κ`-clauses of the frozen goal with `cκ = 2/c²`, `Aκ = (c²/4)⁻¹ = 4/c²`
  (for `c = 4π`: `cκ = 1/(8π²)`, `Aκ = 1/(4π²)`).
* `kappaB_contDiff`, `kappaB_iteratedDeriv_bound`, `kappaB_iteratedDeriv_bound_shift`,
  `kappaB_ofReal_iteratedDeriv_bound_shift`: `s ↦ κ(e^{x+s})` is smooth and its derivatives of
  order `≤ 2` are `≤ C min(e^{αx}, e^{−Nx})`, `0 < α ≤ 5/6`, any `N > 0`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open ArtinPrimitiveRoots.L3J (gA kappa0 gA_pos continuous_gA integrable_gA)

noncomputable section

/-! ## The functions `g_a` -/

theorem gA_le {a : ℝ} (ha : 0 < a) (b : ℝ) : gA a b ≤ Real.exp (a * Real.log a - a) := by
  unfold gA
  refine Real.exp_le_exp.2 ?_
  have h := Real.add_one_le_exp (b - Real.log a)
  have he : Real.exp (b - Real.log a) = Real.exp b / a := by rw [Real.exp_sub, Real.exp_log ha]
  rw [he, le_div_iff₀ ha] at h
  have : (b - Real.log a + 1) * a = a * b - a * Real.log a + a := by ring
  linarith

theorem exp_mul_gA (a b : ℝ) : Real.exp b * gA a b = gA (a + 1) b := by
  unfold gA
  rw [← Real.exp_add]
  congr 1; ring

theorem hasDerivAt_gA (a b : ℝ) : HasDerivAt (gA a) (a * gA a b - gA (a + 1) b) b := by
  have h := (((hasDerivAt_id b).const_mul a).sub (Real.hasDerivAt_exp b)).exp
  have e : a * gA a b - gA (a + 1) b = Real.exp (a * id b - Real.exp b) * (a * 1 - Real.exp b) := by
    rw [← exp_mul_gA]; unfold gA; simp only [id]; ring
  rw [e]
  exact h

/-! ## The family `cc a b` -/

theorem kappa0_eq_cc (t : ℝ) : kappa0 t = cc (5 / 6) (7 / 6) (Real.log t) := rfl

theorem kappa0_exp (x : ℝ) : kappa0 (Real.exp x) = cc (5 / 6) (7 / 6) x := by
  rw [kappa0_eq_cc, Real.log_exp]

theorem integrable_cc_integrand {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Integrable fun y => gA a (x - y) * gA b y := by
  refine ((integrable_gA hb).const_mul (Real.exp (a * Real.log a - a))).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (((continuous_gA a).comp (continuous_const.sub continuous_id)).mul
      (continuous_gA b)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_pos (gA_pos _ _) (gA_pos _ _)).le]
    exact mul_le_mul_of_nonneg_right (gA_le ha _) (gA_pos _ _).le

/-- `cc a b ' = a · cc a b − cc (a+1) b`. -/
theorem hasDerivAt_cc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    HasDerivAt (cc a b) (a * cc a b x - cc (a + 1) b x) x := by
  have ha1 : 0 < a + 1 := by linarith
  set S : ℝ := Real.exp (a * Real.log a - a) with hS
  set S1 : ℝ := Real.exp ((a + 1) * Real.log (a + 1) - (a + 1)) with hS1
  have hF' : ∀ x : ℝ, (fun y => (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y) =
      fun y => a * (gA a (x - y) * gA b y) - gA (a + 1) (x - y) * gA b y := by
    intro x; funext y; ring
  have hint : ∀ x : ℝ, Integrable fun y => (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y := by
    intro x
    rw [hF']
    exact ((integrable_cc_integrand ha hb x).const_mul a).sub (integrable_cc_integrand ha1 hb x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun x y => gA a (x - y) * gA b y)
    (F' := fun x y => (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y)
    (x₀ := x) (s := univ) (bound := fun y => (a * S + S1) * gA b y) univ_mem
    (Eventually.of_forall fun x => (integrable_cc_integrand ha hb x).aestronglyMeasurable)
    (integrable_cc_integrand ha hb x)
    (hint x).aestronglyMeasurable
    (Eventually.of_forall fun y x _ => by
      rw [norm_mul, Real.norm_of_nonneg (gA_pos b y).le]
      refine mul_le_mul_of_nonneg_right ?_ (gA_pos b y).le
      rw [Real.norm_eq_abs, abs_le]
      have h1 := mul_le_mul_of_nonneg_left (gA_le ha (x - y)) ha.le
      have h2 := gA_le ha1 (x - y)
      have p1 := mul_pos ha (gA_pos a (x - y))
      have p2 := gA_pos (a + 1) (x - y)
      have q1 : 0 < a * S := mul_pos ha (Real.exp_pos _)
      have q2 : 0 < S1 := Real.exp_pos _
      constructor <;> linarith)
    ((integrable_gA hb).const_mul _)
    (Eventually.of_forall fun y x _ => by
      have := ((hasDerivAt_gA a (x - y)).comp_sub_const x y).mul_const (gA b y)
      exact this)
  have h := key.2
  have e : ∫ y, (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y =
      a * cc a b x - cc (a + 1) b x := by
    rw [hF', integral_sub ((integrable_cc_integrand ha hb x).const_mul a)
      (integrable_cc_integrand ha1 hb x), integral_const_mul]
    rfl
  rw [e] at h
  exact h

theorem deriv_cc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv (cc a b) = fun x => a * cc a b x - cc (a + 1) b x :=
  funext fun x => (hasDerivAt_cc ha hb x).deriv

theorem contDiff_cc_nat {b : ℝ} (hb : 0 < b) :
    ∀ (n : ℕ) {a : ℝ}, 0 < a → ContDiff ℝ n (cc a b)
  | 0, a, ha => by
    have : Continuous (cc a b) :=
      continuous_iff_continuousAt.2 fun x => (hasDerivAt_cc ha hb x).continuousAt
    exact_mod_cast contDiff_zero.2 this
  | n + 1, a, ha => by
    have h : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (cc a b) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun x => (hasDerivAt_cc ha hb x).differentiableAt, fun h => ?_, ?_⟩
      · simp at h
      · rw [deriv_cc ha hb]
        exact (contDiff_const.mul (contDiff_cc_nat hb n ha)).sub
          (contDiff_cc_nat hb n (by linarith))
    exact_mod_cast h

/-- `cc a b` is smooth. -/
theorem contDiff_cc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ContDiff ℝ (⊤ : ℕ∞) (cc a b) :=
  contDiff_infty.2 fun n => contDiff_cc_nat hb n ha

/-! ## Bounds for `cc a b` -/

theorem gA_mul_eq' (a b x y : ℝ) :
    gA a (x - y) * gA b y =
      Real.exp (a * x) * Real.exp ((b - a) * y - Real.exp (x - y) - Real.exp y) := by
  unfold gA
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-! ## `κ₀` is a K-Bessel function -/

/-- `K_μ(z) = ½ ∫_ℝ e^{μ a} exp(−(z/2)(e^a + e^{−a})) da`. -/
theorem besselKR_eq_integral_exp (μ z : ℝ) :
    besselKR μ z = 1 / 2 * ∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) := by
  have h := besselK_ofReal μ z
  unfold besselK at h
  rw [ArtinPrimitiveRoots.L3X.mellin_eq_integral_exp] at h
  have e : (∫ a : ℝ, Complex.exp ((μ : ℂ) * a) * (besselKer z (Real.exp a) : ℂ)) =
      ((∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    push_cast
    rfl
  rw [e] at h
  have h' : ((1 / 2 * ∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) : ℝ) : ℂ) =
      (besselKR μ z : ℂ) := by
    rw [← h]; push_cast; ring
  exact_mod_cast h'.symm

/-- `κ₀(e^x) = 2 e^x K_{1/3}(2 e^{x/2})`. -/
theorem kappa0_exp_eq_bessel (x : ℝ) :
    kappa0 (Real.exp x) = 2 * Real.exp x * besselKR (1 / 3) (2 * Real.exp (x / 2)) := by
  rw [besselKR_eq_integral_exp,
    ← integral_sub_right_eq_self
      (fun a => Real.exp (1 / 3 * a) * besselKer (2 * Real.exp (x / 2)) (Real.exp a)) (x / 2),
    kappa0_exp]
  unfold cc
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gA_mul_eq']
  have e1 : Real.exp (x / 2) * Real.exp (y - x / 2) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (x / 2) * (Real.exp (y - x / 2))⁻¹ = Real.exp (x - y) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hk : besselKer (2 * Real.exp (x / 2)) (Real.exp (y - x / 2)) =
      Real.exp (-(Real.exp y + Real.exp (x - y))) := by
    unfold besselKer
    congr 1
    rw [← e1, ← e2]; ring
  rw [hk, ← Real.exp_add, ← Real.exp_add]
  have e3 : Real.exp (5 / 6 * x + ((7 / 6 - 5 / 6) * y - Real.exp (x - y) - Real.exp y)) =
      Real.exp x * Real.exp (1 / 3 * (y - x / 2) + -(Real.exp y + Real.exp (x - y))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e3]; ring

/-- `κ₀(t) = 2 t K_{1/3}(2√t)` for `t > 0`. -/
theorem kappa0_eq_bessel {t : ℝ} (ht : 0 < t) :
    kappa0 t = 2 * t * besselKR (1 / 3) (2 * Real.sqrt t) := by
  have h := kappa0_exp_eq_bessel (Real.log t)
  rwa [Real.exp_half, Real.exp_log ht] at h

/-! ## The Bessel profile `κ(t) = t K_{1/3}(c√t)` -/

theorem kappaB_of_pos (c : ℝ) {t : ℝ} (ht : 0 < t) :
    kappaB c t = t * besselKR (1 / 3) (c * Real.sqrt t) := if_pos ht

/-- `κ(t) = (2/c²) κ₀(c² t / 4)`. -/
theorem kappaB_eq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    kappaB c t = 2 / c ^ 2 * kappa0 (c ^ 2 / 4 * t) := by
  have hL : 0 < c ^ 2 / 4 * t := by positivity
  have hs : Real.sqrt (c ^ 2 / 4 * t) = c / 2 * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), show c ^ 2 / 4 = (c / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [kappaB_of_pos c ht, kappa0_eq_bessel hL, hs, show 2 * (c / 2 * Real.sqrt t) = c * Real.sqrt t
    by ring]
  field_simp
  ring

theorem kappaB_exp {c : ℝ} (hc : 0 < c) (x : ℝ) :
    kappaB c (Real.exp x) = 2 / c ^ 2 * cc (5 / 6) (7 / 6) (x + Real.log (c ^ 2 / 4)) := by
  have hL : 0 < c ^ 2 / 4 := by positivity
  rw [kappaB_eq hc (Real.exp_pos x), ← kappa0_exp, Real.exp_add, Real.exp_log hL, mul_comm (Real.exp x)]

theorem kappaB_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ kappaB c t := by
  by_cases ht : 0 < t
  · rw [kappaB_eq hc ht]
    exact mul_nonneg (by positivity) (ArtinPrimitiveRoots.L3J.kappa0_nonneg _)
  · simp [kappaB, ht]

theorem measurable_kappaB {c : ℝ} (hc : 0 < c) : Measurable (kappaB c) := by
  have h : kappaB c = fun t => if 0 < t then 2 / c ^ 2 * kappa0 (c ^ 2 / 4 * t) else 0 := by
    funext t
    by_cases ht : 0 < t
    · rw [kappaB_eq hc ht, if_pos ht]
    · simp [kappaB, ht]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((ArtinPrimitiveRoots.L3J.measurable_kappa0.comp (measurable_const.mul measurable_id)).const_mul _)
    measurable_const

theorem kappaB_mellin {c : ℝ} (hc : 0 < c) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (fun t => (kappaB c t : ℂ)) s ∧
      mellin (fun t => (kappaB c t : ℂ)) s =
        ((2 / c ^ 2 : ℝ) : ℂ) * (((c ^ 2 / 4)⁻¹ : ℝ) : ℂ) ^ s *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  have hL : 0 < c ^ 2 / 4 := by positivity
  obtain ⟨h1, h2⟩ := ArtinPrimitiveRoots.L3J.kappa0_mellin s hs
  have hEq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (((2 / c ^ 2 : ℝ) : ℂ) •
        (fun t : ℝ => (kappa0 t : ℂ)) (c ^ 2 / 4 * t)))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (kappaB c t : ℂ)) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [smul_eq_mul]
    rw [kappaB_eq hc ht']
    push_cast
    ring
  have hc1 : MellinConvergent (fun t : ℝ => ((2 / c ^ 2 : ℝ) : ℂ) •
      (fun t : ℝ => (kappa0 t : ℂ)) (c ^ 2 / 4 * t)) s :=
    ((MellinConvergent.comp_mul_left hL).2 h1).const_smul _
  refine ⟨IntegrableOn.congr_fun hc1 hEq measurableSet_Ioi, ?_⟩
  have hm : mellin (fun t => (kappaB c t : ℂ)) s =
      mellin (fun t : ℝ => ((2 / c ^ 2 : ℝ) : ℂ) •
        (fun t : ℝ => (kappa0 t : ℂ)) (c ^ 2 / 4 * t)) s := by
    unfold mellin
    exact (setIntegral_congr_fun measurableSet_Ioi hEq).symm
  rw [hm, mellin_const_smul, mellin_comp_mul_left (fun t : ℝ => (kappa0 t : ℂ)) s hL, h2, smul_eq_mul, smul_eq_mul,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hL.le, Complex.cpow_neg]
  ring

theorem min_rpow_scale {L α N t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    min ((L * t) ^ α) ((L * t) ^ (-N)) ≤ max (L ^ α) (L ^ (-N)) * min (t ^ α) (t ^ (-N)) := by
  have hmx : 0 ≤ max (L ^ α) (L ^ (-N)) := le_max_of_le_left (Real.rpow_nonneg hL.le _)
  rw [mul_min_of_nonneg _ _ hmx, Real.mul_rpow hL.le ht.le, Real.mul_rpow hL.le ht.le]
  exact min_le_min (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _))

theorem kappaB_bound {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) {N : ℝ}
    (hN : 0 < N) : ∃ C : ℝ, ∀ t : ℝ, 0 < t → kappaB c t ≤ C * min (t ^ α) (t ^ (-N)) := by
  have hL : 0 < c ^ 2 / 4 := by positivity
  obtain ⟨C, hC⟩ := ArtinPrimitiveRoots.L3J.kappa0_bound hα hα' hN
  refine ⟨2 / c ^ 2 * (|C| * max ((c ^ 2 / 4) ^ α) ((c ^ 2 / 4) ^ (-N))), fun t ht => ?_⟩
  rw [kappaB_eq hc ht]
  have hLt : 0 < c ^ 2 / 4 * t := by positivity
  have h1 := hC _ hLt
  have hmin0 : 0 ≤ min ((c ^ 2 / 4 * t) ^ α) ((c ^ 2 / 4 * t) ^ (-N)) :=
    le_min (Real.rpow_nonneg hLt.le _) (Real.rpow_nonneg hLt.le _)
  have h2 : C * min ((c ^ 2 / 4 * t) ^ α) ((c ^ 2 / 4 * t) ^ (-N)) ≤
      |C| * min ((c ^ 2 / 4 * t) ^ α) ((c ^ 2 / 4 * t) ^ (-N)) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hmin0
  have h3 := mul_le_mul_of_nonneg_left (min_rpow_scale (α := α) (N := N) hL ht) (abs_nonneg C)
  have hpos : (0 : ℝ) ≤ 2 / c ^ 2 := by positivity
  calc 2 / c ^ 2 * kappa0 (c ^ 2 / 4 * t)
      ≤ 2 / c ^ 2 * (|C| * (max ((c ^ 2 / 4) ^ α) ((c ^ 2 / 4) ^ (-N)) * min (t ^ α) (t ^ (-N)))) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hpos
    _ = _ := by ring

/-- **The `κ`-clauses of the frozen goal for the Bessel profile** `κ(t) = t K_{1/3}(c√t)`, with
`cκ = 2/c²`, `Aκ = (c²/4)⁻¹`, and any `0 < α ≤ 5/6`. -/
theorem kappaB_clauses {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) :
    Measurable (kappaB c) ∧ (0 : ℝ) < 2 / c ^ 2 ∧ (0 : ℝ) < (c ^ 2 / 4)⁻¹ ∧ 0 < α ∧
      (∀ t, 0 ≤ kappaB c t) ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (kappaB c t : ℂ)) s ∧
        mellin (fun t => (kappaB c t : ℂ)) s =
          ((2 / c ^ 2 : ℝ) : ℂ) * (((c ^ 2 / 4)⁻¹ : ℝ) : ℂ) ^ s *
            (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → kappaB c t ≤ C * min (t ^ α) (t ^ (-N))) :=
  ⟨measurable_kappaB hc, by positivity, by positivity, hα, kappaB_nonneg hc,
    fun s hs => kappaB_mellin hc s hs, fun _ hN => kappaB_bound hc hα hα' hN⟩

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

theorem kappaB_exp_fun {c : ℝ} (hc : 0 < c) :
    (fun s : ℝ => kappaB c (Real.exp s)) =
      fun s => 2 / c ^ 2 * cc (5 / 6) (7 / 6) (s + Real.log (c ^ 2 / 4)) :=
  funext fun s => kappaB_exp hc s

/-- `s ↦ κ(e^s)` is smooth. -/
theorem kappaB_contDiff {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => kappaB c (Real.exp s) := by
  rw [kappaB_exp_fun hc]
  exact contDiff_const.mul ((contDiff_cc (by norm_num) (by norm_num)).comp
    (contDiff_id.add contDiff_const))

theorem kappaB_contDiff_shift {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => kappaB c (Real.exp (x + s)) :=
  (kappaB_contDiff hc).comp (contDiff_const.add contDiff_id)

/-- Iterated derivatives commute with the coercion `ℝ → ℂ`, for smooth functions. -/
theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => (f s : ℂ)) = fun s => ((iteratedDeriv n f s : ℝ) : ℂ) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : DifferentiableAt ℝ (iteratedDeriv n f) x :=
      (hf.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n)) x
    have := hd.hasDerivAt.ofReal_comp.deriv
    rw [this, iteratedDeriv_succ]

/-- Complex-valued form: `s ↦ (κ(e^{x+s}) : ℂ)` is smooth with derivatives of order `≤ 2` at `0`
bounded by `C min(e^{αx}, e^{−Nx})`. -/
theorem kappaB_ofReal_iteratedDeriv_bound_shift {c : ℝ} (hc : 0 < c) {α N : ℝ} (hα : 0 < α)
    (hα' : α ≤ 5 / 6) (hN : 0 < N) :
    (∀ x : ℝ, ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => ((kappaB c (Real.exp (x + s)) : ℝ) : ℂ)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv j (fun s : ℝ => ((kappaB c (Real.exp (x + s)) : ℝ) : ℂ)) 0‖ ≤
        C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  refine ⟨fun x => Complex.ofRealCLM.contDiff.comp (kappaB_contDiff_shift hc x), ?_⟩
  obtain ⟨C, hC, hb⟩ := kappaB_iteratedDeriv_bound_shift hc hα hα' hN
  refine ⟨C, hC, fun j hj x => ?_⟩
  rw [iteratedDeriv_ofReal (kappaB_contDiff_shift hc x) j, Complex.norm_real, Real.norm_eq_abs]
  exact hb j hj x

end

end ArtinKP.K
end

section
-- module Solutions.Artin.T12.L3X_Rho
/-! # L3X_Rho: a partition of unity for `Γ = U_S⁶` acting on `SModel 𝔪 k`

* `valF : SFin 𝔪 k → (S_f → ℤ)`, the valuations at `S_f` (they descend from `F^×`).
* `rho0 y = Ω(−log y, val y)` with L3P's fundamental-domain weight; every `U_S`-orbit meets it with
  total weight `|μ_F|`.
* `rho y = |μ_F|⁻¹ Σ_{s ∈ U_S/U_S⁶} rho0 (u_s y)`; then `Σ_{γ ∈ Γ} rho (γ y) = 1`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain NumberField.Units

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

instance instCountableSUnit : Countable (SUnit 𝔪) := by
  have := countable_field F
  exact Function.Injective.countable (f := fun u : SUnit 𝔪 => ((u : Fˣ) : F))
    (fun a b h => Subtype.ext (Units.ext h))

instance instCountableSClass : Countable (SClass 𝔪) := QuotientGroup.mk_surjective.countable

/-! ### The weights -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Phi
/-! # L3X_Phi: the weight `Φ = ρ · 1_B([y]) · L(y)⁻¹` and the `S`-functions

* `Lmod` is a unitary character of `SModel`, radially trivial, rotating by `ω_{m_w}`.
* `psi y = 1_B([y]) L(y)⁻¹` is `Γ`-invariant; `Phi = ρ · psi`.
* `fpF` facts: its norm, and `L(y)⁻¹ fpF(y) = ∏_w κ(|y_w|)` on `y_f = 0`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Angular characters -/

section Lmod

variable (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ)
  (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b) (hLfn : ∀ a, ‖Lf a‖ = 1)

theorem continuous_toCircle_zsmul (n : ℤ) :
    Continuous fun θ : AddCircle (2 * Real.pi) => ((AddCircle.toCircle (n • θ) : Circle) : ℂ) :=
  continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp (continuous_zsmul n))

end Lmod

/-! ### The weight -/

/-! ### The forward `S`-function -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Main
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice
/-! # WP-H0, file 2: `KPCut` implies the frozen goal 8b3180bd

* `FmOf κ m J`: the product-form reflected `S`-Whittaker function of the cut.
* `FmOf_clauses`: for `κ = K.kappaB c` and `‖J‖ ≤ bf` it satisfies every `Fm`-clause of the goal
  (measurable, `bf ≥ 0`, C² along each radial coordinate, the derivative bound with
  `C = C_κ ^ #places`).
* `goal_of_KPCut`: the frozen statement, verbatim, from `KPCut`. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ)

theorem measurable_FmOf (hκ : Measurable κ) (cl : SFinCls 𝔪 k) :
    Measurable (FmOf κ m J cl) := by
  unfold FmOf
  refine ((measurable_of_countable (J cl)).comp (measurable_snd.comp measurable_snd)).mul ?_
  refine Finset.measurable_prod _ fun w _ => ?_
  refine ((L3X.continuous_toCircle_zsmul (-m w)).measurable.comp ((measurable_pi_apply w).comp
    (measurable_fst.comp measurable_snd))).mul ?_
  exact Complex.measurable_ofReal.comp (hκ.comp (Real.measurable_exp.comp
    ((measurable_pi_apply w).comp measurable_fst)))

theorem FmOf_radial (cl : SFinCls 𝔪 k) (y : SModel 𝔪 k) (w : InfinitePlace F) (s : ℝ) :
    FmOf κ m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)) =
      radConst κ m J cl y w * (κ (Real.exp (y.1 w + s)) : ℂ) := by
  unfold FmOf radConst
  have h1 : ∀ w', (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)).2.1 w' = y.2.1 w' := fun w' => by simp
  have h2 : (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)).2.2 = y.2.2 := by simp
  have h3 : ∀ w', (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)).1 w' = y.1 w' + (Pi.single w s : InfinitePlace F → ℝ) w' :=
    fun w' => rfl
  simp only [h1, h2, h3]
  rw [Finset.prod_mul_distrib, ← Finset.prod_erase_mul (s := Finset.univ)
    (fun w' => (κ (Real.exp (y.1 w' + (Pi.single w s : InfinitePlace F → ℝ) w')) : ℂ)) (Finset.mem_univ w),
    Pi.single_eq_same]
  have : ∏ w' ∈ Finset.univ.erase w, (κ (Real.exp (y.1 w' + (Pi.single w s : InfinitePlace F → ℝ) w')) : ℂ) =
      ∏ w' ∈ Finset.univ.erase w, (κ (Real.exp (y.1 w')) : ℂ) :=
    Finset.prod_congr rfl fun w' hw' => by
      rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hw'), add_zero]
  rw [this]
  ring

theorem norm_radConst_le {bf : SFin 𝔪 k → ℝ} (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y) {B : ℝ → ℝ}
    (hκ : ∀ x, ‖(κ (Real.exp x) : ℂ)‖ ≤ B x) (cl : SFinCls 𝔪 k) (y : SModel 𝔪 k)
    (w : InfinitePlace F) :
    ‖radConst κ m J cl y w‖ ≤ bf y.2.2 * ∏ w' ∈ Finset.univ.erase w, B (y.1 w') := by
  unfold radConst
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  have h1 : ∏ w', ‖((AddCircle.toCircle ((-m w') • y.2.1 w') : Circle) : ℂ)‖ = 1 :=
    Finset.prod_eq_one fun w' _ => Circle.norm_coe _
  rw [h1, mul_one]
  refine mul_le_mul (hJ cl y.2.2) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    ((norm_nonneg _).trans (hJ cl y.2.2))
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w' _ => hκ _

/-- Every `Fm`-clause of the frozen goal for the product form with `κ = kappaB c`. -/
theorem FmOf_clauses_oai {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (hα' : α ≤ 5 / 6)
    (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
    (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y) :
    (∀ cl, Measurable (FmOf (K.kappaB c) m J cl)) ∧ (∀ y, 0 ≤ bf y) ∧
    (∀ w cl y, ContDiff ℝ 2
      (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
    (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w cl y, ∀ j : ℕ, j ≤ 2 →
      ‖iteratedDeriv j
          (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
        C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2) := by
  have hmeas := (K.kappaB_clauses hc hα hα').1
  refine ⟨fun cl => measurable_FmOf _ m J hmeas cl,
    fun y => (norm_nonneg _).trans (hJ 0 y), fun w cl y => ?_, fun N hN => ?_⟩
  · have hfun : (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))
        = fun s : ℝ => radConst (K.kappaB c) m J cl y w * ((K.kappaB c (Real.exp (y.1 w + s)) : ℝ) : ℂ) :=
      funext fun s => FmOf_radial _ m J cl y w s
    rw [hfun]
    exact contDiff_const.mul
      (((K.kappaB_ofReal_iteratedDeriv_bound_shift hc hα hα' one_pos).1 (y.1 w)).of_le
        (by norm_cast))
  · obtain ⟨-, C, hC, hb⟩ := K.kappaB_ofReal_iteratedDeriv_bound_shift hc hα hα' hN
    set B : ℝ → ℝ := fun x => C * min (Real.exp (α * x)) (Real.exp (-(N * x))) with hB
    have hκ0 : ∀ x, ‖((K.kappaB c (Real.exp x) : ℝ) : ℂ)‖ ≤ B x := fun x => by
      have := hb 0 (by norm_num) x
      simpa [iteratedDeriv_zero] using this
    refine ⟨C ^ Fintype.card (InfinitePlace F), fun w cl y j hj => ?_⟩
    have hfun : (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))
        = fun s : ℝ => radConst (K.kappaB c) m J cl y w * ((K.kappaB c (Real.exp (y.1 w + s)) : ℝ) : ℂ) :=
      funext fun s => FmOf_radial _ m J cl y w s
    rw [hfun, iteratedDeriv_const_mul_field, norm_mul]
    have h1 := norm_radConst_le (K.kappaB c) m J hJ hκ0 cl y w
    have h2 : ‖iteratedDeriv j (fun s : ℝ => ((K.kappaB c (Real.exp (y.1 w + s)) : ℝ) : ℂ)) 0‖ ≤
        B (y.1 w) := hb j hj (y.1 w)
    have hBnn : ∀ x, 0 ≤ B x := fun x => (norm_nonneg _).trans (hκ0 x)
    have hbf : 0 ≤ bf y.2.2 := (norm_nonneg _).trans (hJ cl y.2.2)
    calc ‖radConst (K.kappaB c) m J cl y w‖ *
          ‖iteratedDeriv j (fun s : ℝ => ((K.kappaB c (Real.exp (y.1 w + s)) : ℝ) : ℂ)) 0‖
        ≤ (bf y.2.2 * ∏ w' ∈ Finset.univ.erase w, B (y.1 w')) * B (y.1 w) :=
          mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg hbf (Finset.prod_nonneg fun _ _ => hBnn _))
      _ = bf y.2.2 * ∏ w', B (y.1 w') := by
          rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
      _ = C ^ Fintype.card (InfinitePlace F) *
            (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2 := by
          simp only [hB, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
          ring

end

end ArtinKP.H0
end

theorem solution.{u_1} : type_of% @ArtinKP.H0.FmOf_clauses_oai.{u_1} := @ArtinKP.H0.FmOf_clauses_oai.{u_1}
