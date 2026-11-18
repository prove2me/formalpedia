-- Prove2me | solution 1 for ArtinKP.K.kappaB_iteratedDeriv_bound_shift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:42.58889+00:00
-- url     : https://prove2.me/submissions/f35fb046-1ecd-4c90-8b22-c4e5b472462f

import Mathlib
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinKPB017

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

theorem integrable_gA {a : ℝ} (ha : 0 < a) : Integrable (gA a) := by
  have h := (integrable_cexp_gA (s := 0) (a := a) (by simpa using ha)).norm
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [zero_mul, Complex.exp_zero, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (gA_pos a b).le]

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

end

end ArtinPrimitiveRoots.L3J
end

section
-- module Solutions.Artin.KP.K_Kappa
attribute [-instance] _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinKP.X.instSigmaFiniteXVol
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

theorem cc_nonneg (a b x : ℝ) : 0 ≤ cc a b x :=
  integral_nonneg fun _ => (mul_pos (gA_pos _ _) (gA_pos _ _)).le

theorem integrable_cc_integrand {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Integrable fun y => gA a (x - y) * gA b y := by
  refine ((integrable_gA hb).const_mul (Real.exp (a * Real.log a - a))).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (((continuous_gA a).comp (continuous_const.sub continuous_id)).mul
      (continuous_gA b)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_pos (gA_pos _ _) (gA_pos _ _)).le]
    exact mul_le_mul_of_nonneg_right (gA_le ha _) (gA_pos _ _).le

theorem cc_comm (a b x : ℝ) : cc a b x = cc b a x := by
  have h := integral_sub_left_eq_self (fun y => gA b (x - y) * gA a y) volume x
  simp only [sub_sub_cancel] at h
  unfold cc
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mul_comm]

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

theorem iteratedDeriv_one_cc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    iteratedDeriv 1 (cc a b) x = a * cc a b x - cc (a + 1) b x := by
  rw [iteratedDeriv_one, deriv_cc ha hb]

theorem iteratedDeriv_two_cc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    iteratedDeriv 2 (cc a b) x =
      a ^ 2 * cc a b x - (2 * a + 1) * cc (a + 1) b x + cc (a + 1 + 1) b x := by
  have ha1 : 0 < a + 1 := by linarith
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_cc ha hb]
  have h : HasDerivAt (fun x => a * cc a b x - cc (a + 1) b x)
      (a * (a * cc a b x - cc (a + 1) b x) - ((a + 1) * cc (a + 1) b x - cc (a + 1 + 1) b x)) x :=
    ((hasDerivAt_cc ha hb x).const_mul a).sub (hasDerivAt_cc ha1 hb x)
  rw [h.deriv]
  ring

/-! ## Bounds for `cc a b` -/

theorem gA_mul_eq' (a b x y : ℝ) :
    gA a (x - y) * gA b y =
      Real.exp (a * x) * Real.exp ((b - a) * y - Real.exp (x - y) - Real.exp y) := by
  unfold gA
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem cc_le_small {a b : ℝ} (hab : a < b) (x : ℝ) :
    cc a b x ≤ Real.exp (a * x) * ∫ y, gA (b - a) y := by
  unfold cc
  rw [← integral_const_mul]
  have hi : Integrable (fun y => Real.exp (a * x) * gA (b - a) y) :=
    (integrable_gA (by linarith)).const_mul _
  have hle : ∀ y, gA a (x - y) * gA b y ≤ Real.exp (a * x) * gA (b - a) y := by
    intro y
    rw [gA_mul_eq']
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have := Real.exp_pos (x - y)
    linarith
  exact integral_mono_of_nonneg (Eventually.of_forall fun y =>
    (mul_pos (gA_pos _ _) (gA_pos _ _)).le) hi (Eventually.of_forall hle)

theorem cc_le_large {a b : ℝ} (hab : a < b) (x : ℝ) :
    cc a b x ≤ Real.exp (a * x) * Real.exp (-Real.exp (x / 2)) *
      (Real.exp ((b - a) * Real.log 2) * ∫ y, gA (b - a) y) := by
  unfold cc
  set K := Real.exp (a * x) * Real.exp (-Real.exp (x / 2)) * Real.exp ((b - a) * Real.log 2)
  have hshift : ∀ y, Real.exp ((b - a) * y - Real.exp y / 2) =
      Real.exp ((b - a) * Real.log 2) * gA (b - a) (y - Real.log 2) := by
    intro y
    unfold gA
    rw [← Real.exp_add, show Real.exp (y - Real.log 2) = Real.exp y / 2 by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
    congr 1; ring
  have hi : Integrable (fun y => K * gA (b - a) (y - Real.log 2)) :=
    ((integrable_gA (by linarith)).comp_sub_right _).const_mul _
  have hle : ∀ y, gA a (x - y) * gA b y ≤ K * gA (b - a) (y - Real.log 2) := by
    intro y
    rw [gA_mul_eq']
    have h1 : Real.exp ((b - a) * y - Real.exp (x - y) - Real.exp y) ≤
        Real.exp (-Real.exp (x / 2)) * Real.exp ((b - a) * y - Real.exp y / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := ArtinPrimitiveRoots.L3J.exp_sum_ge x y
      linarith
    rw [hshift] at h1
    calc Real.exp (a * x) * Real.exp ((b - a) * y - Real.exp (x - y) - Real.exp y)
        ≤ Real.exp (a * x) * (Real.exp (-Real.exp (x / 2)) *
            (Real.exp ((b - a) * Real.log 2) * gA (b - a) (y - Real.log 2))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = K * gA (b - a) (y - Real.log 2) := by simp only [K]; ring
  have := integral_mono_of_nonneg (Eventually.of_forall fun y =>
    (mul_pos (gA_pos a (x - y)) (gA_pos b y)).le) hi (Eventually.of_forall hle)
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => gA (b - a) y)]
  simp only [K]; ring

theorem cc_bound_of_lt {a b α N : ℝ} (hab : a < b) (hα : 0 < α) (hαa : α ≤ a) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, cc a b x ≤ C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  have hNa : 0 ≤ N + a := by linarith
  set I := ∫ y, gA (b - a) y
  have hI : 0 ≤ I := integral_nonneg fun y => (gA_pos _ _).le
  set E := Real.exp ((b - a) * Real.log 2)
  set M : ℝ := ((Nat.ceil (2 * (N + a))).factorial : ℝ)
  have hM : 0 ≤ M := by positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨max I (E * I * M), le_max_of_le_left hI, fun x => ?_⟩
  rcases le_total x 0 with hx | hx
  · have hmin : min (Real.exp (α * x)) (Real.exp (-(N * x))) = Real.exp (α * x) := by
      refine min_eq_left (Real.exp_le_exp.2 ?_)
      nlinarith
    rw [hmin]
    have h1 : Real.exp (a * x) ≤ Real.exp (α * x) := Real.exp_le_exp.2 (by nlinarith)
    calc cc a b x ≤ Real.exp (a * x) * I := cc_le_small hab x
      _ ≤ Real.exp (α * x) * I := mul_le_mul_of_nonneg_right h1 hI
      _ = I * Real.exp (α * x) := mul_comm _ _
      _ ≤ max I (E * I * M) * Real.exp (α * x) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have hmin : min (Real.exp (α * x)) (Real.exp (-(N * x))) = Real.exp (-(N * x)) := by
      refine min_eq_right (Real.exp_le_exp.2 ?_)
      nlinarith
    rw [hmin]
    have hb := ArtinPrimitiveRoots.L3J.rpow_mul_exp_neg_sqrt_le (a := N + a) hNa
      (t := Real.exp x) (Real.one_le_exp hx)
    rw [← Real.exp_half, ← Real.exp_mul] at hb
    have hsplit : Real.exp (a * x) = Real.exp (x * (N + a)) * Real.exp (-(N * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc cc a b x ≤ Real.exp (a * x) * Real.exp (-Real.exp (x / 2)) * (E * I) := cc_le_large hab x
      _ = (Real.exp (x * (N + a)) * Real.exp (-Real.exp (x / 2))) * (E * I) *
            Real.exp (-(N * x)) := by rw [hsplit]; ring
      _ ≤ M * (E * I) * Real.exp (-(N * x)) := by gcongr
      _ = E * I * M * Real.exp (-(N * x)) := by ring
      _ ≤ max I (E * I * M) * Real.exp (-(N * x)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- `cc a b x ≤ C min(e^{αx}, e^{−Nx})` for `a ≠ b`, `0 < α ≤ min a b`. -/
theorem cc_bound {a b α N : ℝ} (hab : a ≠ b) (hα : 0 < α) (hαa : α ≤ a) (hαb : α ≤ b)
    (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, cc a b x ≤ C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact cc_bound_of_lt h hα hαa hN
  · obtain ⟨C, hC, hb⟩ := cc_bound_of_lt (α := α) (N := N) h hα hαb hN
    exact ⟨C, hC, fun x => by rw [cc_comm]; exact hb x⟩

/-- Derivatives of order `≤ 2` of `x ↦ κ₀(e^x) = cc (5/6) (7/6) x`. -/
theorem iteratedDeriv_cc_bound {α N : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv j (cc (5 / 6) (7 / 6)) x| ≤
        C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  obtain ⟨C0, hC0, h0⟩ := cc_bound (a := 5 / 6) (b := 7 / 6) (α := α) (N := N) (by norm_num) hα hα'
    (by linarith) hN
  obtain ⟨C1, hC1, h1⟩ := cc_bound (a := 5 / 6 + 1) (b := 7 / 6) (α := α) (N := N) (by norm_num) hα
    (by linarith) (by linarith) hN
  obtain ⟨C2, hC2, h2⟩ := cc_bound (a := 5 / 6 + 1 + 1) (b := 7 / 6) (α := α) (N := N)
    (by norm_num) hα (by linarith) (by linarith) hN
  refine ⟨3 * (C0 + C1 + C2), by positivity, fun j hj x => ?_⟩
  set m := min (Real.exp (α * x)) (Real.exp (-(N * x)))
  have hm : 0 ≤ m := le_min (Real.exp_pos _).le (Real.exp_pos _).le
  have p0 := cc_nonneg (5 / 6) (7 / 6) x
  have p1 := cc_nonneg (5 / 6 + 1) (7 / 6) x
  have p2 := cc_nonneg (5 / 6 + 1 + 1) (7 / 6) x
  have b0 := h0 x
  have b1 := h1 x
  have b2 := h2 x
  have m0 := mul_nonneg hC0 hm
  have m1 := mul_nonneg hC1 hm
  have m2 := mul_nonneg hC2 hm
  interval_cases j
  · rw [iteratedDeriv_zero, abs_of_nonneg p0]
    nlinarith
  · rw [iteratedDeriv_one_cc (by norm_num) (by norm_num), abs_le]
    constructor <;> nlinarith
  · rw [iteratedDeriv_two_cc (by norm_num) (by norm_num), abs_le]
    constructor <;> nlinarith

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

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

theorem kappaB_exp_fun {c : ℝ} (hc : 0 < c) :
    (fun s : ℝ => kappaB c (Real.exp s)) =
      fun s => 2 / c ^ 2 * cc (5 / 6) (7 / 6) (s + Real.log (c ^ 2 / 4)) :=
  funext fun s => kappaB_exp hc s

theorem min_exp_shift (α N x l : ℝ) :
    min (Real.exp (α * (x + l))) (Real.exp (-(N * (x + l)))) ≤
      max (Real.exp (α * l)) (Real.exp (-(N * l))) *
        min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  have hmx : 0 ≤ max (Real.exp (α * l)) (Real.exp (-(N * l))) :=
    le_max_of_le_left (Real.exp_pos _).le
  rw [mul_min_of_nonneg _ _ hmx,
    show α * (x + l) = α * l + α * x by ring, show -(N * (x + l)) = -(N * l) + -(N * x) by ring,
    Real.exp_add, Real.exp_add]
  exact min_le_min (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- Derivatives of order `≤ 2` of `s ↦ κ(e^s)`: `≤ C min(e^{αx}, e^{−Nx})`. -/
theorem kappaB_iteratedDeriv_bound {c : ℝ} (hc : 0 < c) {α N : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6)
    (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv j (fun s : ℝ => kappaB c (Real.exp s)) x| ≤
        C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_cc_bound hα hα' hN
  set l := Real.log (c ^ 2 / 4)
  set Mx := max (Real.exp (α * l)) (Real.exp (-(N * l)))
  have hMx : 0 ≤ Mx := le_max_of_le_left (Real.exp_pos _).le
  have hpos : (0 : ℝ) ≤ 2 / c ^ 2 := by positivity
  refine ⟨2 / c ^ 2 * (C * Mx), by positivity, fun j hj x => ?_⟩
  rw [kappaB_exp_fun hc]
  have e : iteratedDeriv j (fun s => 2 / c ^ 2 * cc (5 / 6) (7 / 6) (s + l)) x =
      2 / c ^ 2 * iteratedDeriv j (cc (5 / 6) (7 / 6)) (x + l) := by
    rw [iteratedDeriv_const_mul_field (2 / c ^ 2) (fun s => cc (5 / 6) (7 / 6) (s + l)),
      iteratedDeriv_comp_add_const]
  rw [e, abs_mul, abs_of_nonneg hpos]
  have h1 := hb j hj (x + l)
  have h2 := mul_le_mul_of_nonneg_left (min_exp_shift α N x l) hC
  calc 2 / c ^ 2 * |iteratedDeriv j (cc (5 / 6) (7 / 6)) (x + l)|
      ≤ 2 / c ^ 2 * (C * (Mx * min (Real.exp (α * x)) (Real.exp (-(N * x))))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hpos
    _ = _ := by ring

/-- The form in which the frozen goal asks for it: derivatives at `0` of `s ↦ κ(e^{x+s})`. -/
theorem kappaB_iteratedDeriv_bound_shift_oai {c : ℝ} (hc : 0 < c) {α N : ℝ} (hα : 0 < α)
    (hα' : α ≤ 5 / 6) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv j (fun s : ℝ => kappaB c (Real.exp (x + s))) 0| ≤
        C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  obtain ⟨C, hC, hb⟩ := kappaB_iteratedDeriv_bound hc hα hα' hN
  refine ⟨C, hC, fun j hj x => ?_⟩
  have e := congrFun (iteratedDeriv_comp_const_add (n := j)
    (f := fun s : ℝ => kappaB c (Real.exp s)) (s := x)) 0
  simp only [add_zero] at e
  rw [e]
  exact hb j hj x

end

end ArtinKP.K
end

theorem solution : type_of% @ArtinKP.K.kappaB_iteratedDeriv_bound_shift_oai := @ArtinKP.K.kappaB_iteratedDeriv_bound_shift_oai
