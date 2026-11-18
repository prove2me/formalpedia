-- Prove2me | solution 1 for ArtinKP.GR.weylFlip_of_thmE
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:40.836829+00:00
-- url     : https://prove2.me/submissions/8ac69a02-bf92-44d8-8868-1f2202b34249

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_G2a_exists_major
import Theorems.Thm_ArtinKP_G2a_exists_major_prod
import Theorems.Thm_ArtinKP_G2a_hasFDerivAt_block
import Theorems.Thm_ArtinKP_G2a_jac_bound

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
open ArtinPrimitiveRoots.L3J (gA kappa0 gA_pos integrable_gA)

noncomputable section

/-! ## The functions `g_a` -/

/-! ## The family `cc a b` -/

theorem cc_nonneg (a b x : ℝ) : 0 ≤ cc a b x :=
  integral_nonneg fun _ => (mul_pos (gA_pos _ _) (gA_pos _ _)).le

theorem cc_comm (a b x : ℝ) : cc a b x = cc b a x := by
  have h := integral_sub_left_eq_self (fun y => gA b (x - y) * gA a y) volume x
  simp only [sub_sub_cancel] at h
  unfold cc
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mul_comm]

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

/-! ## `κ₀` is a K-Bessel function -/

/-! ## The Bessel profile `κ(t) = t K_{1/3}(c√t)` -/

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.G2a_Bessel
/-! # WP-G2a, file 10: the `v`-derivative of the Jacquet integral at `s = 4/3`

* `cc_shift`: `cc (a+c) (b+c) x = e^{cx}·cc a b x`; **`zK_eq_cc`**: `z·K_{1/3}(z) = cc (1/3) (2/3) (2 log (z/2))`
  (the lemma "of the type `kappa0_eq_bessel`" that WP-K left open; MATH3 §5.2 (ii)).
* `jacquet_eq_cc`, **`hasDerivAt_jacquet`**: `v ↦ jacquet (4/3) a v` is differentiable on `v > 0`
  with derivative `jd a v` (from `K.hasDerivAt_cc`).
* `grid_decay`: the uniform bound used for both the function and its derivative;
  **`jd_bound`**: `|a|^{2/3}(1+|a|)^p·|jd a v| ≤ K (1+|a|)^{-4}` for `v` in a compact of `(0, ∞)`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B ArtinKP.RF ArtinPrimitiveRoots

noncomputable section

/-- The uniform decay on the grid: `g ≤ C`, `g ≤ C z^{-(p+4)}` give
`(1+n)^{p+4}·g(4πnv) ≤ C'` for `v ≥ 1/(n₀+1)`. -/
theorem grid_decay (p n₀ : ℕ) {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z : ℝ, 0 < z → 0 ≤ g z ∧ g z ≤ C ∧ g z ≤ C * (z ^ (p + 4))⁻¹)
    {n : ℝ} (hn : 0 < n) {v : ℝ} (hv1 : 1 / ((n₀ : ℝ) + 1) ≤ v) :
    (1 + n) ^ (p + 4) * g (4 * Real.pi * n * v)
      ≤ C * 2 ^ (p + 4) * (1 + ((4 * Real.pi / ((n₀ : ℝ) + 1)) ^ (p + 4))⁻¹) := by
  set c : ℝ := 4 * Real.pi / ((n₀ : ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hv1
  set z : ℝ := 4 * Real.pi * n * v with hzdef
  have hz0 : 0 < z := by positivity
  have hzc : c * n ≤ z := by
    rw [hc, hzdef]
    have : 4 * Real.pi * n * (1 / ((n₀ : ℝ) + 1)) ≤ 4 * Real.pi * n * v :=
      mul_le_mul_of_nonneg_left hv1 (by positivity)
    calc 4 * Real.pi / ((n₀ : ℝ) + 1) * n = 4 * Real.pi * n * (1 / ((n₀ : ℝ) + 1)) := by ring
      _ ≤ _ := this
  obtain ⟨hK0, h3a, h3b⟩ := hg z hz0
  have h4 : (0 : ℝ) ≤ (c ^ (p + 4))⁻¹ := by positivity
  have h5 : (0 : ℝ) ≤ C * 2 ^ (p + 4) := by positivity
  rcases le_total n 1 with h1 | h1
  · have h2 : (1 + n) ^ (p + 4) ≤ 2 ^ (p + 4) := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc (1 + n) ^ (p + 4) * g z ≤ 2 ^ (p + 4) * C := mul_le_mul h2 h3a hK0 (by positivity)
      _ ≤ C * 2 ^ (p + 4) * (1 + (c ^ (p + 4))⁻¹) := by nlinarith
  · have h2 : (1 + n) ^ (p + 4) ≤ (2 * n) ^ (p + 4) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h6 : (z ^ (p + 4))⁻¹ ≤ ((c * n) ^ (p + 4))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hzc _)
    calc (1 + n) ^ (p + 4) * g z ≤ (2 * n) ^ (p + 4) * (C * ((c * n) ^ (p + 4))⁻¹) :=
          mul_le_mul h2 (h3b.trans (mul_le_mul_of_nonneg_left h6 hC)) hK0 (by positivity)
      _ = C * 2 ^ (p + 4) * (c ^ (p + 4))⁻¹ := by
          rw [mul_pow, mul_pow]
          have : n ^ (p + 4) ≠ 0 := by positivity
          field_simp
      _ ≤ C * 2 ^ (p + 4) * (1 + (c ^ (p + 4))⁻¹) := by nlinarith

/-- `cc a b (2 log (z/2)) ≤ C` and `≤ C z^{-q}`. -/
theorem cc_grid {a b : ℝ} (hab : a ≠ b) (ha : 1 / 3 ≤ a) (hb : 1 / 3 ≤ b) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → cc a b (2 * Real.log (z / 2)) ≤ C ∧
      cc a b (2 * Real.log (z / 2)) ≤ C * (z ^ q)⁻¹ := by
  obtain ⟨C, hC, h⟩ := cc_bound (a := a) (b := b) (α := 1 / 3) (N := (q : ℝ) / 2 + 1) hab
    (by norm_num) ha hb (by positivity)
  refine ⟨C * 2 ^ (q + 2) , by positivity, fun z hz => ?_⟩
  have hz2 : 0 < z / 2 := by positivity
  set x : ℝ := 2 * Real.log (z / 2) with hx
  have hmin := h x
  have h2q : (1 : ℝ) ≤ 2 ^ (q + 2) := one_le_pow₀ (by norm_num)
  have hcc := cc_nonneg a b x
  constructor
  · rcases le_total x 0 with hx0 | hx0
    · have h1 : Real.exp (1 / 3 * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have := hmin.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
      nlinarith
    · have h1 : Real.exp (-(((q : ℝ) / 2 + 1) * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ ((q : ℝ) / 2 + 1) * x := by positivity
        linarith)
      have := hmin.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
      nlinarith
  · have h1 : Real.exp (-(((q : ℝ) / 2 + 1) * x)) = ((z / 2) ^ (q + 2))⁻¹ := by
      rw [hx, show -(((q : ℝ) / 2 + 1) * (2 * Real.log (z / 2)))
        = -(((q + 2 : ℕ) : ℝ) * Real.log (z / 2)) by push_cast; ring, Real.exp_neg,
        Real.exp_nat_mul, Real.exp_log hz2]
    have h3 := hmin.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
    rw [h1] at h3
    -- `((z/2)^(q+2))⁻¹ ≤ 2^(q+2) (z^q)⁻¹` needs care for small `z`; use the first bound there
    rcases le_total z 2 with hz' | hz'
    · -- `z ≤ 2`: `(z^q)⁻¹ ≥ 2^{-q}`
      have h4 : cc a b x ≤ C := by
        rcases le_total x 0 with hx0 | hx0
        · have h1' : Real.exp (1 / 3 * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          have := hmin.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
          nlinarith
        · have h1' : Real.exp (-(((q : ℝ) / 2 + 1) * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
            have : (0 : ℝ) ≤ ((q : ℝ) / 2 + 1) * x := by positivity
            linarith)
          have := hmin.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
          nlinarith
      have h5 : (2 : ℝ) ^ q * (z ^ q)⁻¹ ≥ 1 := by
        rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ hz.le hz' q
      calc cc a b x ≤ C := h4
        _ ≤ C * (2 ^ q * (z ^ q)⁻¹) := le_mul_of_one_le_right hC h5
        _ ≤ C * 2 ^ (q + 2) * (z ^ q)⁻¹ := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hC
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    · -- `z ≥ 2`: `(z/2)^{q+2} ≥ (z/2)^q`
      have h4 : ((z / 2) ^ (q + 2))⁻¹ ≤ ((z / 2) ^ q)⁻¹ :=
        inv_anti₀ (by positivity)
          (pow_le_pow_right₀ (by rw [le_div_iff₀ (by norm_num)]; linarith) (by omega))
      calc cc a b x ≤ C * ((z / 2) ^ q)⁻¹ := h3.trans (mul_le_mul_of_nonneg_left h4 hC)
        _ = C * 2 ^ q * (z ^ q)⁻¹ := by rw [div_pow]; field_simp
        _ ≤ C * 2 ^ (q + 2) * (z ^ q)⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hC

/-- **The derivative bound, one place.** -/
theorem jd_bound (p n₀ : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℂ, a ≠ 0 → ∀ v : ℝ,
    1 / ((n₀ : ℝ) + 1) ≤ v → v ≤ (n₀ : ℝ) + 1 →
    ‖a‖ ^ (2 / 3 : ℝ) * (1 + ‖a‖) ^ p * ‖jd a v‖ ≤ K * ((1 + ‖a‖) ^ 4)⁻¹ := by
  obtain ⟨C₁, hC₁, h₁⟩ := cc_grid (a := 1 / 3) (b := 2 / 3) (by norm_num) le_rfl (by norm_num)
    (p + 4)
  obtain ⟨C₂, hC₂, h₂⟩ := cc_grid (a := 1 / 3 + 1) (b := 2 / 3) (by norm_num) (by norm_num)
    (by norm_num) (p + 4)
  set g : ℝ → ℝ := fun z => cc (1 / 3) (2 / 3) (2 * Real.log (z / 2))
    + cc (1 / 3 + 1) (2 / 3) (2 * Real.log (z / 2)) with hg
  have hgb : ∀ z : ℝ, 0 < z → 0 ≤ g z ∧ g z ≤ (C₁ + C₂) ∧ g z ≤ (C₁ + C₂) * (z ^ (p + 4))⁻¹ := by
    intro z hz
    refine ⟨add_nonneg (cc_nonneg _ _ _) (cc_nonneg _ _ _), add_le_add (h₁ z hz).1 (h₂ z hz).1, ?_⟩
    rw [add_mul]
    exact add_le_add (h₁ z hz).2 (h₂ z hz).2
  set M : ℝ := (C₁ + C₂) * 2 ^ (p + 4) * (1 + ((4 * Real.pi / ((n₀ : ℝ) + 1)) ^ (p + 4))⁻¹)
    with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨‖c1‖ * (2 * ((n₀ : ℝ) + 1)) * M, by positivity, fun a ha v hv1 hv2 => ?_⟩
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hv1
  have hgrid := grid_decay p n₀ (add_nonneg hC₁ hC₂) hgb hn hv1
  set A := cc (1 / 3) (2 / 3) (2 * Real.log (2 * Real.pi * ‖a‖ * v)) with hA
  set B := cc (1 / 3 + 1) (2 / 3) (2 * Real.log (2 * Real.pi * ‖a‖ * v)) with hB
  have hA0 : 0 ≤ A := cc_nonneg _ _ _
  have hB0 : 0 ≤ B := cc_nonneg _ _ _
  have hgz : g (4 * Real.pi * ‖a‖ * v) = A + B := by
    simp only [hg, hA, hB]
    rw [show 4 * Real.pi * ‖a‖ * v / 2 = 2 * Real.pi * ‖a‖ * v by ring]
  rw [hgz] at hgrid
  have h2v : 2 / v ≤ 2 * ((n₀ : ℝ) + 1) := by
    rw [div_le_iff₀ hv]
    have : 1 ≤ ((n₀ : ℝ) + 1) * v := by
      have := mul_le_mul_of_nonneg_left hv1 (by positivity : (0 : ℝ) ≤ (n₀ : ℝ) + 1)
      rwa [mul_one_div_cancel (by positivity)] at this
    nlinarith
  have hnorm : ‖jd a v‖ ≤ ‖c1‖ * (‖a‖ ^ (-(2 / 3 : ℝ)) * ((A + B) * (2 * ((n₀ : ℝ) + 1)))) := by
    rw [jd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hn _), abs_of_pos (by positivity : 0 < 2 / v)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)
    refine mul_le_mul ?_ h2v (by positivity) (by positivity)
    rw [abs_le]
    constructor <;> linarith
  have hrr : ‖a‖ ^ (2 / 3 : ℝ) * ‖a‖ ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hn]; norm_num
  have h14 : (0 : ℝ) < (1 + ‖a‖) ^ 4 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h14]
  calc ‖a‖ ^ (2 / 3 : ℝ) * (1 + ‖a‖) ^ p * ‖jd a v‖ * (1 + ‖a‖) ^ 4
      ≤ ‖a‖ ^ (2 / 3 : ℝ) * (1 + ‖a‖) ^ p *
          (‖c1‖ * (‖a‖ ^ (-(2 / 3 : ℝ)) * ((A + B) * (2 * ((n₀ : ℝ) + 1))))) * (1 + ‖a‖) ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by positivity)) h14.le
    _ = ‖c1‖ * (2 * ((n₀ : ℝ) + 1)) * (‖a‖ ^ (2 / 3 : ℝ) * ‖a‖ ^ (-(2 / 3 : ℝ))) *
          ((1 + ‖a‖) ^ (p + 4) * (A + B)) := by rw [pow_add]; ring
    _ ≤ ‖c1‖ * (2 * ((n₀ : ℝ) + 1)) * 1 * M := by
        rw [hrr]
        exact mul_le_mul_of_nonneg_left hgrid (by positivity)
    _ = _ := by ring

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Def
/-! # WP-G2a, file 3: the series `thetaS` (definition, convergence, continuity, linearity)

`term Φ ν Q = τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` (`Q = (x, v)`), `thetaS Φ Q = Σ_{ν ∈ R∖0} term Φ ν Q`.
Under Theorem E (`ThmE`) the series converges absolutely, uniformly on every set `vOpen n`
(`v ∈ (1/(n+1), n+1)^r`, any `x`), together with every polynomial weight `∏_w (1+|ν|_w)^p`;
`thetaS Φ` is continuous on `X F`, additive in `Φ` and homogeneous for `smulFun`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

omit [IsTotallyComplex F] in
lemma vOpen_subset_vBox {n : ℕ} {Q : X F} (hQ : Q ∈ vOpen F n) : Q.v ∈ vBox F n :=
  fun w => ⟨(hQ w).1.le, (hQ w).2.le⟩

omit [IsTotallyComplex F] in
lemma exists_mem_vOpen (Q : X F) : ∃ n : ℕ, Q ∈ vOpen F n := by
  obtain ⟨n, hn⟩ := exists_nat_ge
    (∑ w : InfinitePlace F, (Q.v w + (Q.v w)⁻¹))
  refine ⟨n, fun w => ?_⟩
  have hpos := Q.v_pos w
  have hle : Q.v w + (Q.v w)⁻¹ ≤ n :=
    (Finset.single_le_sum (f := fun w => Q.v w + (Q.v w)⁻¹)
      (fun w _ => add_nonneg (Q.v_pos w).le (inv_nonneg.mpr (Q.v_pos w).le))
      (Finset.mem_univ w)).trans hn
  have hinv : 0 < (Q.v w)⁻¹ := inv_pos.mpr hpos
  constructor
  · rw [one_div, inv_lt_comm₀ (by positivity) hpos]
    linarith
  · linarith

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Exp
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 6: the pointwise theta function and **(Exp)**

* `kapC F = covol(𝓞_F)⁻¹` (`= T.kap 𝔪 M` for every `M ≥ 0`).
* `IsExp Φ z`: for every finite-index `Γ` fixing `Φ.twist`,
  `X.lift Γ (C5.theta Γ Φ.twist) = z·ht^{2/3} + kapC·thetaS Φ` almost everywhere.
* **`exists_isExp`** (Theorem E + `hdiff`): such a `z` exists.  (Fourier uniqueness on the full
  stabilizer, `C9.ae_eq_htC_of_coeff`; other groups by `N.lift_theta_congr`.)
* `zc Φ` := that `z` (unique: `isExp_unique`); **`thetaT Φ Q := zc Φ·ht(Q)^{2/3} + kapC·thetaS Φ Q`**,
  continuous, and `thetaT_ae`: it represents `θ_{Φ.twist}` for every admissible `Γ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6)

/-- MATH3's display (Exp) in coordinates. -/
theorem thetaT_mk (Φ : GSection ι P 𝔪) (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    thetaT hG hz6 Φ (X.mk x v hv) =
      zc hG hz6 Φ * ((X.ht (X.mk x v hv) : ℝ) : ℂ) ^ (2 / 3 : ℂ) +
        kapC F * ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
          T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v *
            eInf (emb ((ν : SInt 𝔪) : F) * x) := rfl

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.K_Weyl
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-! # WP-K, file 4: the Weyl flip on `H³ = SL₂(ℂ)/SU(2)`, and Fourier terms

Model: WP-X's `ArtinKP.X.H3 = {(x, v) : ℂ × ℝ | 0 < v}` with its `SL(2,ℂ)`-action; a right
`SU(2)`-invariant function on `SL₂(ℂ)` is `g ↦ f (g • j0)`, `j0 = (0, 1)`.

For `g = n(x) a(y)` (`a(y) = diag(y, y⁻¹)`, `y ∈ ℂˣ`), the two curves through `g • j0 = (x, |y|²)`
* `ζ ↦ g n(ζ) • j0 = (x + y² ζ, |y|²)`                               (`curveN`, `orbit_N`),
* `ζ ↦ g w n(ζ) • j0 = (x − y² ζ̄/(1+|ζ|²), |y|²/(1+|ζ|²))`           (`curveW`, `orbit_W`)
have Wirtinger derivatives at `ζ = 0` related by

  `∂_ζ (f ∘ curveW) = −∂_ζ̄ (f ∘ curveN)`,  `∂_ζ̄ (f ∘ curveW) = −∂_ζ (f ∘ curveN)`   (`weyl_flip`):

right translation by `w` exchanges the derivatives of weight `+1` and `−1` along `n(ζ)`, up to
the sign `−1` (MATH §4.5 "Weyl element"; `Ad(w) X_ζ = Y_{−ζ} ≡ X_{−ζ̄}` mod `𝔰𝔲(2)`).
On a Fourier term `f(x, v) = e(Tr νx) W(v)`: `∂_ζ (f ∘ curveN) = 2πi ν y² f`,
`∂_ζ̄ (f ∘ curveN) = 2πi conj(ν y²) f` (`dz_fourierTerm_curveN`), hence
`∂_ζ (f ∘ curveW) = −2πi conj(ν y²) f`, `∂_ζ̄ (f ∘ curveW) = −2πi ν y² f` (`weyl_flip_fourierTerm`).
-/

open scoped MatrixGroups ComplexConjugate

namespace ArtinKP.K

open ArtinKP.X

noncomputable section

/-! ## Matrices and orbits -/

/-! ## Wirtinger derivatives and the flip -/

theorem curveN_zero (x y : ℂ) : curveN x y 0 = (x, ‖y‖ ^ 2) := by simp [curveN]

theorem curveW_zero (x y : ℂ) : curveW x y 0 = (x, ‖y‖ ^ 2) := by simp [curveW]

theorem hasFDerivAt_curveN (x y ζ : ℂ) :
    HasFDerivAt (curveN x y)
      (((y ^ 2 : ℂ) • ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℝ)) ζ := by
  have h1 : HasFDerivAt (fun ζ : ℂ => x + y ^ 2 * ζ) ((y ^ 2 : ℂ) • ContinuousLinearMap.id ℝ ℂ) ζ :=
    ((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_mul (y ^ 2)).const_add x
  exact h1.prodMk (hasFDerivAt_const (‖y‖ ^ 2) ζ)

theorem hasFDerivAt_curveW (x y : ℂ) :
    HasFDerivAt (curveW x y)
      ((-((y ^ 2 : ℂ) • (Complex.conjCLE : ℂ →L[ℝ] ℂ))).prod (0 : ℂ →L[ℝ] ℝ)) 0 := by
  have hn : HasFDerivAt (fun ζ : ℂ => ‖ζ‖ ^ 2) (0 : ℂ →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt
  have hr : HasFDerivAt (fun ζ : ℂ => (1 + ‖ζ‖ ^ 2)⁻¹) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h := (hasDerivAt_inv (x := (1 : ℝ) + ‖(0 : ℂ)‖ ^ 2) (by simp)).comp_hasFDerivAt (0 : ℂ)
      (hn.const_add 1)
    rw [smul_zero] at h
    exact h
  have hrc : HasFDerivAt (fun ζ : ℂ => (((1 + ‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ)) (0 : ℂ →L[ℝ] ℂ) 0 := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) hr
    rw [ContinuousLinearMap.comp_zero] at h
    exact h
  have hc : HasFDerivAt (fun ζ : ℂ => conj ζ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 :=
    Complex.conjCLE.hasFDerivAt
  have hp : HasFDerivAt (fun ζ : ℂ => conj ζ * (((1 + ‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ))
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 := by
    refine (hc.mul hrc).congr_fderiv ?_
    simp
  have h1 : HasFDerivAt (fun ζ : ℂ => x - y ^ 2 * (conj ζ * (((1 + ‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ)))
      (-((y ^ 2 : ℂ) • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) 0 :=
    (hp.const_mul (y ^ 2)).const_sub x
  have h2 : HasFDerivAt (fun ζ : ℂ => ‖y‖ ^ 2 * (1 + ‖ζ‖ ^ 2)⁻¹) (0 : ℂ →L[ℝ] ℝ) 0 :=
    (hr.const_mul (‖y‖ ^ 2)).congr_fderiv (smul_zero _)
  exact h1.prodMk h2

theorem fderiv_comp_curveN (f : ℂ × ℝ → ℂ) (x y : ℂ) (hf : DifferentiableAt ℝ f (x, ‖y‖ ^ 2))
    (h : ℂ) : fderiv ℝ (f ∘ curveN x y) 0 h = fderiv ℝ f (x, ‖y‖ ^ 2) (y ^ 2 * h, 0) := by
  have hf' : HasFDerivAt f (fderiv ℝ f (x, ‖y‖ ^ 2)) (curveN x y 0) := by
    rw [curveN_zero]; exact hf.hasFDerivAt
  rw [(hf'.comp 0 (hasFDerivAt_curveN x y 0)).fderiv]
  simp

theorem fderiv_comp_curveW (f : ℂ × ℝ → ℂ) (x y : ℂ) (hf : DifferentiableAt ℝ f (x, ‖y‖ ^ 2))
    (h : ℂ) : fderiv ℝ (f ∘ curveW x y) 0 h = -fderiv ℝ f (x, ‖y‖ ^ 2) (y ^ 2 * conj h, 0) := by
  have hf' : HasFDerivAt f (fderiv ℝ f (x, ‖y‖ ^ 2)) (curveW x y 0) := by
    rw [curveW_zero]; exact hf.hasFDerivAt
  rw [(hf'.comp 0 (hasFDerivAt_curveW x y)).fderiv, ← map_neg]
  simp

/-- **Weyl flip.** For `f` real-differentiable at `(x, |y|²) = n(x)a(y) • j`: right translation by
the Weyl element exchanges the `ζ`- and `ζ̄`-derivatives along `n(ζ)`, with sign `−1`. -/
theorem weyl_flip (f : ℂ × ℝ → ℂ) (x y : ℂ) (hf : DifferentiableAt ℝ f (x, ‖y‖ ^ 2)) :
    dz (f ∘ curveW x y) 0 = -dzbar (f ∘ curveN x y) 0 ∧
      dzbar (f ∘ curveW x y) 0 = -dz (f ∘ curveN x y) 0 := by
  unfold dz dzbar
  simp only [fderiv_comp_curveN f x y hf, fderiv_comp_curveW f x y hf, map_one, Complex.conj_I,
    mul_one, mul_neg]
  have e : ((-(y ^ 2 * Complex.I), (0 : ℝ)) : ℂ × ℝ) = -((y ^ 2 * Complex.I, (0 : ℝ)) : ℂ × ℝ) := by
    simp
  rw [e, map_neg]
  constructor <;> ring

/-! ## Fourier terms -/

/-! ## The Whittaker function at `s = 4/3` and the profile `κ` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.G2a_Dx
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-G2a, file 8: the mixed first `x`-derivative `∂_m` and Fourier series

`∂^{(+1)} = ∂_x`, `∂^{(−1)} = ∂_x̄` (Wirtinger, `K.dz`, `K.dzbar`) in one coordinate `x_w` of
`x : InfinitePlace F → ℂ`; `∂_m = ∏_w ∂^{(m_w)}_{x_w}` (MATH3 §0), defined by iterating over a
list of places.

* `Dw m w f`: the Wirtinger derivative of type `m` in the `w`-th coordinate.
* `DList m l f`: iteration over the list `l`; `Dm m f := DList m Finset.univ.toList f`.
* **`DList_series`**: for a Fourier series `Σ_i c_i e_∞(ν_i x)` whose coefficients are summable
  against every power of `1 + ‖ν_i‖`, `DList m l` acts termwise:
  the `i`-th term is multiplied by `∏_{w ∈ l} (−2πi · ν_{i,w}^{(m_w)})`.
-/

open scoped ComplexConjugate Topology
open NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B

noncomputable section

/-! ### One complex variable -/

lemma linA_apply (a h : ℂ) : linA a h = 2 * Real.pi * Complex.I * (a * h + conj (a * h)) := by
  simp [linA]
  ring

lemma archChar_eq_exp_linA (a ζ : ℂ) : archChar (a * ζ) = Complex.exp (linA a ζ) := by
  rw [archChar, linA_apply]

lemma norm_linA_le (a : ℂ) : ‖linA a‖ ≤ 4 * Real.pi * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [linA_apply, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have : ‖a * h + conj (a * h)‖ ≤ 2 * (‖a‖ * ‖h‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [RCLike.norm_conj, norm_mul]
    linarith
  nlinarith [Real.pi_pos]

lemma hasFDerivAt_archChar (a b ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => archChar (a * (ζ - b))) (archChar (a * (ζ - b)) • linA a) ζ := by
  have h1 : HasFDerivAt (fun ζ : ℂ => linA a (ζ - b))
      ((linA a).comp (ContinuousLinearMap.id ℝ ℂ)) ζ :=
    (linA a).hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).sub_const b)
  rw [ContinuousLinearMap.comp_id] at h1
  have h2 := h1.cexp
  simp only [← archChar_eq_exp_linA] at h2
  exact h2

lemma dz_eq (φ : ℂ → ℂ) (ζ : ℂ) : dz φ ζ = dzL (fderiv ℝ φ ζ) := by simp [dz, dzL]

lemma dzbar_eq (φ : ℂ → ℂ) (ζ : ℂ) : dzbar φ ζ = dzbarL (fderiv ℝ φ ζ) := by
  simp [dzbar, dzbarL]
  ring

lemma dzL_smul_linA (t a : ℂ) : dzL (t • linA a) = t * (2 * Real.pi * Complex.I * a) := by
  simp only [dzL, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
    ContinuousLinearMap.apply_apply, linA_apply, smul_eq_mul, mul_one, map_mul, Complex.conj_I]
  linear_combination (-(t * Real.pi * Complex.I * (a - conj a))) * Complex.I_sq

lemma dzbarL_smul_linA (t a : ℂ) :
    dzbarL (t • linA a) = t * (2 * Real.pi * Complex.I * conj a) := by
  simp only [dzbarL, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
    ContinuousLinearMap.apply_apply, linA_apply, smul_eq_mul, mul_one, map_mul, Complex.conj_I]
  linear_combination (t * Real.pi * Complex.I * (a - conj a)) * Complex.I_sq

lemma norm_cj (m : ℤ) (z : ℂ) : ‖cj m z‖ = ‖z‖ := by
  unfold cj; split_ifs <;> simp

/-! ### Several variables -/

variable {W : Type*} [Fintype W] [DecidableEq W]

lemma norm_eW (ν x : W → ℂ) : ‖eW ν x‖ = 1 := by
  simp only [eW, norm_prod, archChar_norm, Finset.prod_const_one]

lemma eW_update (ν x : W → ℂ) (w : W) (ζ : ℂ) :
    eW ν (Function.update x w ζ) = eW ν x * archChar (-(ν w) * (ζ - x w)) := by
  unfold eW
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), ← Finset.mul_prod_erase _
    (fun w' => archChar (-(ν w' * x w'))) (Finset.mem_univ w), Function.update_self]
  have h : ∏ w' ∈ Finset.univ.erase w, archChar (-(ν w' * Function.update x w ζ w'))
      = ∏ w' ∈ Finset.univ.erase w, archChar (-(ν w' * x w')) :=
    Finset.prod_congr rfl fun w' hw' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  rw [h, show -(ν w * ζ) = -(ν w * x w) + -(ν w) * (ζ - x w) by ring, archChar_add]
  ring

variable {I : Type*}

/-- **One step**: the derivative of a Fourier series in one coordinate, termwise. -/
theorem Dw_series (c : I → ℂ) (ν : I → W → ℂ)
    (hs : Summable fun i => ‖c i‖ * (1 + ‖ν i‖)) (m : ℤ) (w : W) (x : W → ℂ) :
    Dw m w (fun x => ∑' i, c i * eW (ν i) x) x =
      ∑' i, c i * (-(2 * Real.pi * Complex.I) * cj m (ν i w)) * eW (ν i) x := by
  set f : I → ℂ → ℂ := fun i ζ => c i * eW (ν i) (Function.update x w ζ) with hf
  set f' : I → ℂ → (ℂ →L[ℝ] ℂ) := fun i ζ =>
    (c i * (eW (ν i) x * archChar (-(ν i w) * (ζ - x w)))) • linA (-(ν i w)) with hf'
  have hd : ∀ i ζ, HasFDerivAt (f i) (f' i ζ) ζ := by
    intro i ζ
    have e : f i = fun ζ => (c i * eW (ν i) x) * archChar (-(ν i w) * (ζ - x w)) := by
      funext ζ; simp only [hf, eW_update]; ring
    rw [e]
    have := (hasFDerivAt_archChar (-(ν i w)) (x w) ζ).const_mul (c i * eW (ν i) x)
    simpa only [hf', smul_smul, mul_assoc] using this
  set u : I → ℝ := fun i => 4 * Real.pi * (‖c i‖ * (1 + ‖ν i‖)) with hu
  have hus : Summable u := hs.mul_left _
  have hb : ∀ i ζ, ‖f' i ζ‖ ≤ u i := by
    intro i ζ
    rw [norm_smul, norm_mul, norm_mul, norm_eW, archChar_norm, mul_one, mul_one]
    have h1 := norm_linA_le (-(ν i w))
    rw [norm_neg] at h1
    have h2 : ‖ν i w‖ ≤ 1 + ‖ν i‖ := (norm_le_pi_norm (ν i) w).trans (by linarith)
    calc ‖c i‖ * ‖linA (-(ν i w))‖ ≤ ‖c i‖ * (4 * Real.pi * (1 + ‖ν i‖)) :=
          mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (norm_nonneg _)
      _ = u i := by rw [hu]; ring
  have h0 : Summable fun i => f i (x w) := by
    refine Summable.of_norm_bounded hs fun i => ?_
    rw [hf, norm_mul, norm_eW, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg (ν i)])
  have H := hasFDerivAt_tsum hus hd hb h0 (x w)
  have hsL : Summable fun i => f' i (x w) := Summable.of_norm_bounded hus fun i => hb i (x w)
  have hval : ∀ i, f' i (x w) = (c i * eW (ν i) x) • linA (-(ν i w)) := fun i => by
    simp only [hf', sub_self, mul_zero]
    rw [show archChar 0 = 1 by simp [archChar], mul_one]
  have hfun : (fun ζ => (fun x => ∑' i, c i * eW (ν i) x) (Function.update x w ζ))
      = fun ζ => ∑' i, f i ζ := rfl
  unfold Dw
  split_ifs with hm
  · rw [hfun, dz_eq, H.fderiv, ← (hsL.hasSum.mapL dzL).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hval, dzL_smul_linA, cj, if_pos hm]
    ring
  · rw [hfun, dzbar_eq, H.fderiv, ← (hsL.hasSum.mapL dzbarL).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hval, dzbarL_smul_linA, cj, if_neg hm, map_neg]
    ring

/-! ### Constants are killed -/

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Fwd
/-! # WP-G2a, file 9: `∂_m θ̃_Φ` termwise and the forward field (MATH3 §1.1)

* `thetaX Φ v hv x = θ̃_Φ(x, v)` as a function of `x` at fixed height `v`.
* **`Dm_thetaX`**: `∂_m θ̃_Φ(·, v)` is the termwise series; the constant term is killed and the
  `ν`-th term is multiplied by `∏_w (−2πi·ν_w^{(m_w)})`.
* `ThetaM m Φ X Y := ∏_w Y_w^{(m_w)} · (∂_m θ̃_Φ)(X, |Y|)` (MATH3's `Θ_m^Φ(X, Y)`).
* `place_kappaB`: `(νY)^{(m)}·jacquet (4/3) (−ν) |Y| = C0·|ν|^{−2/3}·ω_m(νY)·κ(|νY|²)`,
  `κ = K.kappaB (4π)`, `C0 = (2π)^{4/3}/Γ(4/3)`.
* **`ThetaM_tau`**: the expansion with coefficient `τ_Φ(ν)` (no Theorem E beyond convergence);
* **`ThetaM_forward`** = MATH3 (1.1):
  `Θ_m^Φ(X,Y) = kapC·C_a^r·Σ_ν coef^S(ν)·ξ_Φ(ν)·e_∞(νX)·∏_w ω_{m_w}(ν_wY_w)·κ(|ν_wY_w|²)`,
  `C_a = −2πi·C0`, with `summable_forward`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

/-! ### One place -/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

lemma eW_emb (ν : F) (x : InfinitePlace F → ℂ) : eW (emb ν) x = eInf (emb ν * x) := rfl

omit [IsTotallyComplex F] in
lemma one_add_norm_emb_le (ν : F) :
    1 + ‖(emb ν : InfinitePlace F → ℂ)‖ ≤ ∏ w : InfinitePlace F, (1 + w ν) := by
  have h1 : (1 : ℝ) ≤ ∏ w : InfinitePlace F, (1 + w ν) := by
    calc (1 : ℝ) = ∏ _w : InfinitePlace F, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
        fun w _ => by linarith [apply_nonneg w ν]
  have h2 : ‖(emb ν : InfinitePlace F → ℂ)‖ ≤ ∏ w : InfinitePlace F, (1 + w ν) - 1 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro w
    rw [emb_apply, InfinitePlace.norm_embedding_eq]
    have : (1 + w ν) = ∏ w' : InfinitePlace F, (if w' = w then 1 + w ν else 1) := by
      rw [Finset.prod_ite_eq' Finset.univ w, if_pos (Finset.mem_univ w)]
    have h3 : 1 + w ν ≤ ∏ w' : InfinitePlace F, (1 + w' ν) := by
      rw [this]
      refine Finset.prod_le_prod (fun w' _ => by split_ifs <;> positivity) fun w' _ => ?_
      split_ifs with h
      · rw [h]
      · linarith [apply_nonneg w' ν]
    linarith
  linarith

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Block
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-G2a, file 11: first derivatives in a block `(x_w, v_w)`

* `exists_major_prod`: the majorant of `G2a_Major` for an arbitrary product of one-place factors
  satisfying the one-place bound.
* `serA Φ q x v = Σ_ν q(ν)·τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` in ambient coordinates.
* **`differentiableAt_block`**: for `q` of polynomial growth, `serA Φ q` is differentiable in the
  block `(x_w, v_w)` at every point with `v > 0`, the other coordinates fixed (termwise, with a
  summable majorant of the differentials on `ℂ × (a, b)`: MATH3 (Exp), "first partial derivatives
  in each block, locally uniformly").
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-! ### The differential of one term in a block -/

lemma norm_blockD_le (a b : ℂ) (z : ℂ × ℝ) :
    ‖blockD a b z‖ ≤ ‖jd a z.2‖ + 4 * Real.pi * ‖a‖ * ‖jacquet (4 / 3) a z.2‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have h1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have h2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have h3 := (linA a).le_opNorm h.1
  have h4 := norm_linA_le a
  simp only [blockD, add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  · rw [norm_mul, archChar_norm, one_mul, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  · rw [norm_mul, norm_mul, archChar_norm, one_mul]
    have : ‖linA a h.1‖ ≤ 4 * Real.pi * ‖a‖ * ‖h‖ :=
      h3.trans (mul_le_mul h4 h1 (norm_nonneg _) (by positivity))
    calc ‖jacquet (4 / 3) a z.2‖ * ‖linA a h.1‖
        ≤ ‖jacquet (4 / 3) a z.2‖ * (4 * Real.pi * ‖a‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring

omit [IsTotallyComplex F] in
lemma Winf_update (ν : F) (v : InfinitePlace F → ℝ) (w : InfinitePlace F) (t : ℝ) :
    Winf (4 / 3) ν (Function.update v w t) =
      (∏ w' ∈ Finset.univ.erase w, jacquet (4 / 3) (-(w'.embedding ν)) (v w')) *
        jacquet (4 / 3) (-(w.embedding ν)) t := by
  unfold Winf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun w' hw' => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]

/-- **Differentiability in a block.** -/
theorem differentiableAt_block (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪)
    (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (p : ℕ) (C : ℝ)
    (hq : ∀ ν : {ν : SInt 𝔪 // ν ≠ 0},
      ‖q ν‖ ≤ C * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p)
    (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    (w : InfinitePlace F) :
    DifferentiableAt ℝ (fun z : ℂ × ℝ =>
      serA hG hz6 Φ q (Function.update x w z.1) (Function.update v w z.2)) (x w, v w) := by
  obtain ⟨n₀, hn₀⟩ := exists_mem_vOpen (X.mk 0 v hv)
  have hvb : ∀ w', 1 / ((n₀ : ℝ) + 1) < v w' ∧ v w' < (n₀ : ℝ) + 1 := hn₀
  obtain ⟨K₁, hK₁, hj₁⟩ := jac_bound p n₀
  obtain ⟨K₂, hK₂, hj₂⟩ := jd_bound p n₀
  obtain ⟨K₃, hK₃, hj₃⟩ := jac_bound (p + 1) n₀
  set K : ℝ := K₁ + K₂ + 4 * Real.pi * K₃ with hKdef
  have hK : 0 ≤ K := by positivity
  obtain ⟨u, hu, hmaj⟩ := exists_major_prod hE Φ p K
  set U : Set (ℂ × ℝ) := (univ : Set ℂ) ×ˢ Ioo (1 / ((n₀ : ℝ) + 1)) ((n₀ : ℝ) + 1) with hU
  have hUo : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hUc : IsPreconnected U := isPreconnected_univ.prod isPreconnected_Ioo
  have hz₀ : (x w, v w) ∈ U := ⟨mem_univ _, (hvb w).1, (hvb w).2⟩
  -- the terms
  set a : {ν : SInt 𝔪 // ν ≠ 0} → ℂ := fun ν => -(w.embedding ((ν : SInt 𝔪) : F)) with ha
  have ha0 : ∀ ν, a ν ≠ 0 := fun ν => neg_ne_zero.mpr ((map_ne_zero _).mpr (H0.coe_ne_zero ν))
  have hna : ∀ ν, ‖a ν‖ = w ((ν : SInt 𝔪) : F) := fun ν => by
    rw [ha, norm_neg, InfinitePlace.norm_embedding_eq]
  set A : {ν : SInt 𝔪 // ν ≠ 0} → ℂ := fun ν =>
    ∏ w' ∈ Finset.univ.erase w, jacquet (4 / 3) (-(w'.embedding ((ν : SInt 𝔪) : F))) (v w')
    with hA
  set B : {ν : SInt 𝔪 // ν ≠ 0} → ℂ := fun ν =>
    q ν * T.tau hG hz6 Φ (ν : SInt 𝔪) * A ν * eW (emb ((ν : SInt 𝔪) : F)) x with hB
  set f : {ν : SInt 𝔪 // ν ≠ 0} → ℂ × ℝ → ℂ := fun ν z =>
    q ν * (T.tau hG hz6 Φ (ν : SInt 𝔪) *
      Winf (4 / 3) ((ν : SInt 𝔪) : F) (Function.update v w z.2)) *
      eInf (emb ((ν : SInt 𝔪) : F) * Function.update x w z.1) with hf
  have hfeq : ∀ ν, f ν = fun z =>
      B ν * (archChar (a ν * (z.1 - x w)) * jacquet (4 / 3) (a ν) z.2) := by
    intro ν
    funext z
    simp only [hf, hB, hA, ha]
    rw [Winf_update, ← eW_emb, eW_update, emb_apply]
    ring
  set f' : {ν : SInt 𝔪 // ν ≠ 0} → ℂ × ℝ → (ℂ × ℝ →L[ℝ] ℂ) := fun ν z =>
    B ν • blockD (a ν) (x w) z with hf'
  have hd : ∀ ν z, z ∈ U → HasFDerivAt (f ν) (f' ν z) z := by
    intro ν z hz
    rw [hfeq ν]
    have hz2 : 0 < z.2 := lt_trans (by positivity) hz.2.1
    exact (hasFDerivAt_block (ha0 ν) (x w) hz2).const_mul (B ν)
  -- the one-place factors
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hqC : ∀ ν : {ν : SInt 𝔪 // ν ≠ 0},
      ‖q ν‖ ≤ |C| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p := fun ν =>
    (hq ν).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Finset.prod_nonneg fun w _ => by positivity))
  have hbound : ∀ (ν : {ν : SInt 𝔪 // ν ≠ 0}) (β : ℝ), 0 ≤ β →
      (w ((ν : SInt 𝔪) : F)) ^ (2 / 3 : ℝ) * (1 + w ((ν : SInt 𝔪) : F)) ^ p * β
        ≤ K * ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹ →
      ‖q ν‖ * ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ * ‖A ν‖ * β ≤ |C| * u ν := by
    intro ν β hβ hβb
    set b : InfinitePlace F → ℝ := fun w' =>
      if w' = w then β else ‖jacquet (4 / 3) (-(w'.embedding ((ν : SInt 𝔪) : F))) (v w')‖ with hb
    have hb0 : ∀ w', 0 ≤ b w' := fun w' => by
      simp only [hb]; split_ifs <;> positivity
    have hbK : ∀ w' : InfinitePlace F, (w' ((ν : SInt 𝔪) : F)) ^ (2 / 3 : ℝ) *
        (1 + w' ((ν : SInt 𝔪) : F)) ^ p * b w' ≤ K * ((1 + w' ((ν : SInt 𝔪) : F)) ^ 4)⁻¹ := by
      intro w'
      simp only [hb]
      split_ifs with h
      · rw [h]; exact hβb
      · have h1 := hj₁ (-(w'.embedding ((ν : SInt 𝔪) : F)))
          (neg_ne_zero.mpr ((map_ne_zero _).mpr (H0.coe_ne_zero ν))) (v w') (hvb w').1.le
          (hvb w').2.le
        rw [norm_neg, InfinitePlace.norm_embedding_eq] at h1
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        rw [hKdef]
        have : 0 ≤ 4 * Real.pi * K₃ := by positivity
        linarith
    have hprod : ∏ w', b w' = β * ‖A ν‖ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      simp only [hb, if_true, hA, norm_prod]
      congr 1
      exact Finset.prod_congr rfl fun w' hw' => by rw [if_neg (Finset.ne_of_mem_erase hw')]
    have hm := hmaj ν b hb0 hbK
    rw [hprod] at hm
    calc ‖q ν‖ * ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ * ‖A ν‖ * β
        ≤ (|C| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
            ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ * ‖A ν‖ * β := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hqC ν) (norm_nonneg _)) (norm_nonneg _)) hβ
      _ = |C| * ((∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
            (‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ * (β * ‖A ν‖))) := by ring
      _ ≤ |C| * u ν := mul_le_mul_of_nonneg_left hm hC0
  have hnB : ∀ ν, ‖B ν‖ = ‖q ν‖ * ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ * ‖A ν‖ := fun ν => by
    simp only [hB]
    rw [norm_mul, norm_mul, norm_mul, norm_eW, mul_one]
  have hb' : ∀ ν z, z ∈ U → ‖f' ν z‖ ≤ |C| * u ν := by
    intro ν z hz
    have hz1 : 1 / ((n₀ : ℝ) + 1) ≤ z.2 := hz.2.1.le
    have hz2 : z.2 ≤ (n₀ : ℝ) + 1 := hz.2.2.le
    simp only [hf']
    rw [norm_smul, hnB]
    refine le_trans (mul_le_mul_of_nonneg_left (norm_blockD_le (a ν) (x w) z)
      (by positivity)) ?_
    refine hbound ν _ (by positivity) ?_
    have h2 := hj₂ (a ν) (ha0 ν) z.2 hz1 hz2
    have h3 := hj₃ (a ν) (ha0 ν) z.2 hz1 hz2
    rw [hna] at h2 h3 ⊢
    set n := w ((ν : SInt 𝔪) : F) with hn
    have hn0 : 0 ≤ n := apply_nonneg _ _
    have h3' : n ^ (2 / 3 : ℝ) * (1 + n) ^ p *
        (n * ‖jacquet (4 / 3) (a ν) z.2‖) ≤ K₃ * ((1 + n) ^ 4)⁻¹ := by
      refine le_trans ?_ h3
      rw [pow_succ]
      have : n ≤ 1 + n := by linarith
      calc n ^ (2 / 3 : ℝ) * (1 + n) ^ p * (n * ‖jacquet (4 / 3) (a ν) z.2‖)
          = n ^ (2 / 3 : ℝ) * (1 + n) ^ p * ‖jacquet (4 / 3) (a ν) z.2‖ * n := by ring
        _ ≤ n ^ (2 / 3 : ℝ) * (1 + n) ^ p * ‖jacquet (4 / 3) (a ν) z.2‖ * (1 + n) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hK₁' : 0 ≤ K₁ * ((1 + n) ^ 4)⁻¹ := by positivity
    calc n ^ (2 / 3 : ℝ) * (1 + n) ^ p *
          (‖jd (a ν) z.2‖ + 4 * Real.pi * n * ‖jacquet (4 / 3) (a ν) z.2‖)
        = n ^ (2 / 3 : ℝ) * (1 + n) ^ p * ‖jd (a ν) z.2‖ +
          4 * Real.pi * (n ^ (2 / 3 : ℝ) * (1 + n) ^ p *
            (n * ‖jacquet (4 / 3) (a ν) z.2‖)) := by ring
      _ ≤ K₂ * ((1 + n) ^ 4)⁻¹ + 4 * Real.pi * (K₃ * ((1 + n) ^ 4)⁻¹) :=
          add_le_add h2 (mul_le_mul_of_nonneg_left h3' (by positivity))
      _ ≤ K * ((1 + n) ^ 4)⁻¹ := by rw [hKdef]; nlinarith
  have hf0 : Summable fun ν => f ν (x w, v w) := by
    refine Summable.of_norm_bounded (hu.mul_left |C|) fun ν => ?_
    rw [hfeq ν]
    simp only [sub_self, mul_zero]
    rw [show archChar 0 = 1 by simp [archChar], one_mul, norm_mul, hnB]
    refine hbound ν _ (norm_nonneg _) ?_
    have h1 := hj₁ (a ν) (ha0 ν) (v w) (hvb w).1.le (hvb w).2.le
    rw [hna] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hKdef]
    have : 0 ≤ 4 * Real.pi * K₃ := by positivity
    linarith
  have H := hasFDerivAt_tsum_of_isPreconnected (hu.mul_left |C|) hUo hUc hd hb' hz₀ hf0 hz₀
  exact H.differentiableAt

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.GW_One
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-GW, file 1: one place

* `Dt m φ`: the Wirtinger derivative of type `m` of `φ : ℂ → ℂ` at `0` (`∂_ζ` for `m = 1`,
  `∂_ζ̄` otherwise), with `Dw_eq_Dt`, `Dt_add`, `Dt_series`.
* `PolyB q`: the weight `q` on the frequencies is polynomially bounded
  (`‖q ν‖ ≤ C·∏_w (1 + |ν|_w)^p`), the class of weights for which `G2a.serA` converges with all
  its first block derivatives.
* `summable_weight`: the coefficients of `serA Φ q` are summable against every power of `1 + ‖ν‖`.
* **`Dt_serA_curveN`**: along `K.curveN` in the place `w` the series `serA Φ q` is a Fourier series
  in `ζ`; its type-`m` derivative at `0` is `serA Φ (q·μ')`, `μ'(ν) = −2πi·(ν_w y²)^{(m)}`.
* **`Dt_serA_curveW`** (the one-place Weyl flip, `m = ±1`): along `K.curveW` the type-`m`
  derivative at `0` is `serA Φ (q·μ)`, `μ(ν) = 2πi·(ν_w y²)^{(−m)}`
  (`G2a.differentiableAt_block` + `K.weyl_flip` + `Dt_serA_curveN` for the type `−m`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GW

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
open ArtinKP.G2a

noncomputable section

/-! ### The type-`m` derivative at `0` -/

lemma Dw_eq_Dt {W : Type*} [DecidableEq W] (m : ℤ) (w : W) (f : (W → ℂ) → ℂ) (ζ : W → ℂ)
    (h : ζ w = 0) : Dw m w f ζ = Dt m (fun s => f (Function.update ζ w s)) := by
  unfold Dw Dt
  rw [h]

lemma Dt_add (m : ℤ) (a b : ℂ → ℂ) (ha : DifferentiableAt ℝ a 0) (hb : DifferentiableAt ℝ b 0) :
    Dt m (fun s => a s + b s) = Dt m a + Dt m b := by
  have h : fderiv ℝ (fun s => a s + b s) 0 = fderiv ℝ a 0 + fderiv ℝ b 0 :=
    (ha.hasFDerivAt.add hb.hasFDerivAt).fderiv
  unfold Dt dz dzbar
  rw [h]
  split_ifs
  · simp only [add_apply]; ring
  · simp only [add_apply]; ring

lemma Dt_of_hasFDerivAt_zero (m : ℤ) (a : ℂ → ℂ) (h : HasFDerivAt a (0 : ℂ →L[ℝ] ℂ) 0) :
    Dt m a = 0 := by
  unfold Dt dz dzbar
  rw [h.fderiv]
  split_ifs <;> simp

/-- Termwise type-`m` derivative at `0` of a Fourier series in one complex variable. -/
theorem Dt_series {J : Type*} (c a : J → ℂ) (hs : Summable fun i => ‖c i‖ * (1 + ‖a i‖))
    (m : ℤ) :
    Dt m (fun s => ∑' i, c i * archChar (-(a i * s))) =
      ∑' i, c i * (-(2 * Real.pi * Complex.I) * cj m (a i)) := by
  have hs' : Summable fun i => ‖c i‖ * (1 + ‖(fun _ : Unit => a i)‖) := by
    simpa only [pi_norm_const] using hs
  have h := Dw_series (W := Unit) c (fun i _ => a i) hs' m () (fun _ => 0)
  have e0 : archChar 0 = 1 := by simp [archChar]
  simp only [Dw, eW, Finset.univ_unique, Finset.prod_singleton, Function.update_self, mul_zero,
    neg_zero, e0, mul_one] at h
  unfold Dt
  exact h

/-! ### Polynomially bounded weights -/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

omit [IsTotallyComplex F] in
lemma polyB_const (c : ℂ) : PolyB (fun _ : {ν : SInt 𝔪 // ν ≠ 0} => c) :=
  ⟨0, ‖c‖, fun ν => by simp⟩

omit [IsTotallyComplex F] in
lemma PolyB.mul {q q' : {ν : SInt 𝔪 // ν ≠ 0} → ℂ} (hq : PolyB q) (hq' : PolyB q') :
    PolyB (fun ν => q ν * q' ν) := by
  obtain ⟨p, C, hC⟩ := hq
  obtain ⟨p', C', hC'⟩ := hq'
  refine ⟨p + p', |C| * |C'|, fun ν => ?_⟩
  have hP : 0 ≤ ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p :=
    Finset.prod_nonneg fun w _ => by positivity
  have hP' : 0 ≤ ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p' :=
    Finset.prod_nonneg fun w _ => by positivity
  have h1 : ‖q ν‖ ≤ |C| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p :=
    (hC ν).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hP)
  have h2 : ‖q' ν‖ ≤ |C'| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p' :=
    (hC' ν).trans (mul_le_mul_of_nonneg_right (le_abs_self C') hP')
  rw [norm_mul]
  calc ‖q ν‖ * ‖q' ν‖
      ≤ (|C| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
          (|C'| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p') :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (abs_nonneg C) hP)
    _ = _ := by
        simp only [pow_add, Finset.prod_mul_distrib]
        ring

omit [IsTotallyComplex F] in
lemma PolyB.listProd {W : Type*} (μ : W → {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (hμ : ∀ w, PolyB (μ w))
    (l : List W) : PolyB (fun ν => (l.map fun w => μ w ν).prod) := by
  induction l with
  | nil => simpa using polyB_const (𝔪 := 𝔪) 1
  | cons w l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hμ w).mul ih

omit [IsTotallyComplex F] in
/-- The eigenvalue of a first derivative in the place `w` is polynomially bounded. -/
lemma polyB_place (k Y : ℂ) (n : ℤ) (w : InfinitePlace F) :
    PolyB (fun ν : {ν : SInt 𝔪 // ν ≠ 0} => k * cj n (w.embedding ((ν : SInt 𝔪) : F) * Y)) := by
  refine ⟨1, ‖k‖ * ‖Y‖, fun ν => ?_⟩
  rw [norm_mul, norm_cj, norm_mul, InfinitePlace.norm_embedding_eq]
  have h1 : w ((ν : SInt 𝔪) : F) ≤ ∏ w' : InfinitePlace F, (1 + w' ((ν : SInt 𝔪) : F)) ^ 1 := by
    simp only [pow_one]
    have h3 := one_add_norm_emb_le (F := F) ((ν : SInt 𝔪) : F)
    have h2 := norm_le_pi_norm (emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ) w
    rw [emb_apply, InfinitePlace.norm_embedding_eq] at h2
    linarith
  calc ‖k‖ * (w ((ν : SInt 𝔪) : F) * ‖Y‖) = ‖k‖ * ‖Y‖ * w ((ν : SInt 𝔪) : F) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- The coefficients of `serA Φ q` are summable against every power of `1 + ‖ν‖`. -/
theorem summable_weight (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪)
    {q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ} (hq : PolyB q) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) (k : ℕ) :
    Summable fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      ‖q ν * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v)‖ *
        (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) ^ k := by
  obtain ⟨p, C, hC⟩ := hq
  obtain ⟨n₀, hn₀⟩ := exists_mem_vOpen (X.mk 0 v hv)
  have hvb : v ∈ vBox F n₀ := vOpen_subset_vBox hn₀
  obtain ⟨u, hu, -, hle⟩ := exists_major hE Φ (p + k) n₀
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) (hu.mul_left |C|)
  have hP : 0 ≤ ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p :=
    Finset.prod_nonneg fun w _ => by positivity
  have h1 : ‖q ν‖ ≤ |C| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p :=
    (hC ν).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hP)
  have h2 : (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) ^ k
      ≤ ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ k := by
    rw [Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_norm_emb_le _) k
  rw [norm_mul]
  calc ‖q ν‖ * ‖T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖ *
        (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) ^ k
      ≤ (|C| * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
          ‖T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖ *
          ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (by positivity)
          (mul_nonneg (mul_nonneg (abs_nonneg C) hP) (norm_nonneg _))
    _ = |C| * ((∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ (p + k)) *
          ‖T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖) := by
        simp only [pow_add, Finset.prod_mul_distrib]
        ring
    _ ≤ |C| * u ν := mul_le_mul_of_nonneg_left (hle ν v hvb) (abs_nonneg C)

lemma neg_serA (Φ : GSection ι P 𝔪) (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) :
    -serA hG hz6 Φ q x v = serA hG hz6 Φ (fun ν => -q ν) x v := by
  unfold serA
  rw [← tsum_neg]
  exact tsum_congr fun ν => by ring

/-! ### One place, along `curveN` -/

/-- **One place, `curveN`.** -/
theorem Dt_serA_curveN (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪)
    {q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ} (hq : PolyB q) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (w : InfinitePlace F) (y : ℂ)
    (hvw : v w = ‖y‖ ^ 2) (m : ℤ) :
    Dt m (fun s => serA hG hz6 Φ q (Function.update x w (curveN (x w) y s).1)
        (Function.update v w (curveN (x w) y s).2)) =
      serA hG hz6 Φ (fun ν => q ν * (-(2 * Real.pi * Complex.I) *
        cj m (w.embedding ((ν : SInt 𝔪) : F) * y ^ 2))) x v := by
  have hfun : (fun s : ℂ => serA hG hz6 Φ q (Function.update x w (curveN (x w) y s).1)
        (Function.update v w (curveN (x w) y s).2)) = fun s =>
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        (q ν * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v) *
          eW (emb ((ν : SInt 𝔪) : F)) x) *
          archChar (-(w.embedding ((ν : SInt 𝔪) : F) * y ^ 2 * s)) := by
    funext s
    unfold serA
    simp only [curveN]
    rw [← hvw, Function.update_eq_self]
    refine tsum_congr fun ν => ?_
    rw [← eW_emb, eW_update, emb_apply,
      show -(w.embedding ((ν : SInt 𝔪) : F)) * (x w + y ^ 2 * s - x w)
        = -(w.embedding ((ν : SInt 𝔪) : F) * y ^ 2 * s) by ring]
    ring
  have hs : Summable fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      ‖q ν * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v) *
          eW (emb ((ν : SInt 𝔪) : F)) x‖ *
        (1 + ‖w.embedding ((ν : SInt 𝔪) : F) * y ^ 2‖) := by
    refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
      ((summable_weight hE Φ hq v hv 1).mul_left (1 + ‖y ^ 2‖))
    rw [norm_mul _ (eW _ _), norm_eW, mul_one, pow_one, norm_mul (w.embedding _)]
    have h2 := norm_le_pi_norm (emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ) w
    rw [emb_apply] at h2
    have h3 : ‖w.embedding ((ν : SInt 𝔪) : F)‖ * ‖y ^ 2‖
        ≤ ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖ * ‖y ^ 2‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : 1 + ‖w.embedding ((ν : SInt 𝔪) : F)‖ * ‖y ^ 2‖
        ≤ (1 + ‖y ^ 2‖) * (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) := by
      nlinarith [norm_nonneg (emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ), norm_nonneg (y ^ 2)]
    calc _ ≤ ‖q ν * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v)‖ *
          ((1 + ‖y ^ 2‖) * (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖)) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = _ := by ring
  rw [hfun, Dt_series _ _ hs]
  unfold serA
  refine tsum_congr fun ν => ?_
  rw [← eW_emb]
  ring

/-! ### One place, along `curveW`: the Weyl flip -/

/-- **One place, `curveW`** (the Weyl flip termwise; `m = ±1`). -/
theorem Dt_serA_curveW (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪)
    {q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ} (hq : PolyB q) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (w : InfinitePlace F) (y : ℂ)
    (hvw : v w = ‖y‖ ^ 2) {m : ℤ} (hm : m = 1 ∨ m = -1) :
    Dt m (fun s => serA hG hz6 Φ q (Function.update x w (curveW (x w) y s).1)
        (Function.update v w (curveW (x w) y s).2)) =
      serA hG hz6 Φ (fun ν => q ν * ((2 * Real.pi * Complex.I) *
        cj (-m) (w.embedding ((ν : SInt 𝔪) : F) * y ^ 2))) x v := by
  set f : ℂ × ℝ → ℂ := fun z =>
    serA hG hz6 Φ q (Function.update x w z.1) (Function.update v w z.2) with hf
  have hfd : DifferentiableAt ℝ f (x w, ‖y‖ ^ 2) := by
    rw [← hvw]
    obtain ⟨p, C, hC⟩ := hq
    exact differentiableAt_block hE Φ q p C hC x v hv w
  obtain ⟨h1, h2⟩ := weyl_flip f (x w) y hfd
  have hN := fun m' : ℤ => Dt_serA_curveN hE Φ hq x v hv w y hvw m'
  rcases hm with rfl | rfl
  · have hN1 : dzbar (f ∘ curveN (x w) y) 0 = _ :=
      (if_neg (by norm_num : ¬ ((-1 : ℤ) = 1))).symm.trans (hN (-1))
    refine (if_pos rfl).trans ?_
    change dz (f ∘ curveW (x w) y) 0 = _
    rw [h1, hN1, neg_serA]
    congr 1
    funext ν
    ring
  · have hN1 : dz (f ∘ curveN (x w) y) 0 = _ := (if_pos rfl).symm.trans (hN 1)
    refine (if_neg (by norm_num : ¬ ((-1 : ℤ) = 1))).trans ?_
    change dzbar (f ∘ curveW (x w) y) 0 = _
    rw [h2, hN1, neg_serA, neg_neg]
    congr 1
    funext ν
    ring

end

end ArtinKP.GW
end

section
-- module Solutions.Artin.KP.GW_Main
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-GW, file 2: the multi-place Weyl flip for `θ̃_Ψ`

* `cx c ζ`, `cv c ζ`: the point `(c_w(ζ_w))_w` of `X` in ambient coordinates, for a family of
  curves `c w : ℂ → ℂ × ℝ` (one in each place); `Aterm z c ζ = z·ht^{2/3}` along the curves.
* **`DList_curve`**: induction over a list of places.  If in each place the type-`m_w` derivative
  at `0` of every polynomially weighted series along `c w` is the series with the weight
  multiplied by `μ_w` (hypothesis `H1`), and the heights of the curves are stationary at `0`, then
  `DList m l (ζ ↦ z·ht^{2/3} + serA Ψ q)(ζ) = serA Ψ (q·∏_{w ∈ l} μ_w)` at every `ζ` vanishing on
  `l` (`l` without repetitions, nonempty: the constant term dies at the innermost operator).
* **`Dm_thetaT_curveW`**, **`Dm_thetaT_curveN`**: the mixed derivative of type `m` of `θ̃_Ψ` along
  `K.curveW` (for `m = ±1`), resp. along `K.curveN` (all `m`), as termwise series.
* **`weyl_flip_thetaT`**: stub G2a-2, with the statement of `G2a_Stubs.lean` verbatim.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GW

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
open ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### Families of curves -/

omit [NumberField F] [IsTotallyComplex F] in
lemma cx_update (c : InfinitePlace F → ℂ → ℂ × ℝ) (ζ : InfinitePlace F → ℂ) (w : InfinitePlace F)
    (s : ℂ) : cx c (Function.update ζ w s) = Function.update (cx c ζ) w (c w s).1 := by
  funext w'
  by_cases h : w' = w
  · subst h; simp [cx]
  · simp [cx, h]

omit [NumberField F] [IsTotallyComplex F] in
lemma cv_update (c : InfinitePlace F → ℂ → ℂ × ℝ) (ζ : InfinitePlace F → ℂ) (w : InfinitePlace F)
    (s : ℂ) : cv c (Function.update ζ w s) = Function.update (cv c ζ) w (c w s).2 := by
  funext w'
  by_cases h : w' = w
  · subst h; simp [cv]
  · simp [cv, h]

omit [IsTotallyComplex F] in
/-- The constant term is stationary at `0` in each variable when the heights of the curves are. -/
lemma hasFDerivAt_Aterm (z : ℂ) (c : InfinitePlace F → ℂ → ℂ × ℝ) (hpos : ∀ w s, 0 < (c w s).2)
    (hc2 : ∀ w, HasFDerivAt (fun s => (c w s).2) (0 : ℂ →L[ℝ] ℝ) 0) (w : InfinitePlace F)
    (ζ : InfinitePlace F → ℂ) :
    HasFDerivAt (fun s => Aterm z c (Function.update ζ w s)) (0 : ℂ →L[ℝ] ℂ) 0 := by
  set K : ℝ := ∏ w' ∈ Finset.univ.erase w, cv c ζ w' with hK
  have hK0 : 0 < K := Finset.prod_pos fun w' _ => hpos w' _
  have hR : ∀ s, ∏ w', cv c (Function.update ζ w s) w' = (c w s).2 * K := by
    intro s
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), cv_update, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun w' hw' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  have hRd : HasFDerivAt (fun s => (c w s).2 * K) (0 : ℂ →L[ℝ] ℝ) 0 :=
    ((hc2 w).mul_const K).congr_fderiv (by simp)
  have hpos0 : 0 < (c w 0).2 * K := mul_pos (hpos w 0) hK0
  have h1 : HasFDerivAt (fun s => ((c w s).2 * K) ^ (2 / 3 : ℝ)) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h0 := (Real.hasDerivAt_rpow_const (x := (c w 0).2 * K) (p := 2 / 3)
      (Or.inl hpos0.ne')).comp_hasFDerivAt (0 : ℂ) hRd
    rw [smul_zero] at h0
    exact h0
  have h2 : HasFDerivAt (fun s => z * ((((c w s).2 * K) ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      (0 : ℂ →L[ℝ] ℂ) 0 :=
    ((Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) h1).const_mul z).congr_fderiv (by simp)
  have e : (fun s => Aterm z c (Function.update ζ w s))
      = fun s => z * ((((c w s).2 * K) ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    funext s
    unfold Aterm
    rw [hR, Complex.ofReal_cpow (mul_pos (hpos w s) hK0).le]
    norm_num
  rw [e]
  exact h2

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- Differentiability at `0` of a weighted series along a differentiable curve in one place. -/
lemma differentiableAt_serA_curve (hE : ThmE hG hz6 g P) (Ψ : GSection ι P 𝔪)
    {q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ} (hq : PolyB q) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (w : InfinitePlace F) (γ : ℂ → ℂ × ℝ)
    (hγ : DifferentiableAt ℝ γ 0) (hx : x w = (γ 0).1) (hvw : v w = (γ 0).2) :
    DifferentiableAt ℝ (fun s => serA hG hz6 Ψ q (Function.update x w (γ s).1)
      (Function.update v w (γ s).2)) 0 := by
  obtain ⟨p, C, hC⟩ := hq
  have hb := differentiableAt_block hE Ψ q p C hC x v hv w
  rw [hx, hvw, Prod.mk.eta] at hb
  exact hb.comp (0 : ℂ) hγ

/-- **Induction over the places.** -/
theorem DList_curve (hE : ThmE hG hz6 g P) (Ψ : GSection ι P 𝔪) (m : InfinitePlace F → ℤ)
    (c : InfinitePlace F → ℂ → ℂ × ℝ) (z : ℂ) (hpos : ∀ w s, 0 < (c w s).2)
    (hcd : ∀ w, DifferentiableAt ℝ (c w) 0)
    (hc2 : ∀ w, HasFDerivAt (fun s => (c w s).2) (0 : ℂ →L[ℝ] ℝ) 0)
    (μ : InfinitePlace F → {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (hμ : ∀ w, PolyB (μ w))
    (H1 : ∀ (w : InfinitePlace F) (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ), PolyB q →
      ∀ (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ), (∀ w', 0 < v w') →
        x w = (c w 0).1 → v w = (c w 0).2 →
        Dt (m w) (fun s => serA hG hz6 Ψ q (Function.update x w (c w s).1)
          (Function.update v w (c w s).2)) = serA hG hz6 Ψ (fun ν => q ν * μ w ν) x v)
    (l : List (InfinitePlace F)) (hl : l.Nodup) (hne : l ≠ [])
    (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (hq : PolyB q) (ζ : InfinitePlace F → ℂ)
    (hζ : ∀ w ∈ l, ζ w = 0) :
    DList m l (fun ζ => Aterm z c ζ + serA hG hz6 Ψ q (cx c ζ) (cv c ζ)) ζ =
      serA hG hz6 Ψ (fun ν => q ν * (l.map fun w => μ w ν).prod) (cx c ζ) (cv c ζ) := by
  induction l generalizing ζ with
  | nil => exact absurd rfl hne
  | cons w l ih =>
    have hw : ζ w = 0 := hζ w List.mem_cons_self
    have hwl : w ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hx : cx c ζ w = (c w 0).1 := by simp [cx, hw]
    have hv : cv c ζ w = (c w 0).2 := by simp [cv, hw]
    have hvpos : ∀ w', 0 < cv c ζ w' := fun w' => hpos w' _
    show Dw (m w) w (DList m l _) ζ = _
    rw [Dw_eq_Dt _ _ _ _ hw]
    by_cases hnil : l = []
    · subst hnil
      have e : (fun s => DList m [] (fun ζ => Aterm z c ζ + serA hG hz6 Ψ q (cx c ζ) (cv c ζ))
            (Function.update ζ w s))
          = fun s => Aterm z c (Function.update ζ w s) +
              serA hG hz6 Ψ q (Function.update (cx c ζ) w (c w s).1)
                (Function.update (cv c ζ) w (c w s).2) := by
        funext s
        show Aterm z c (Function.update ζ w s) +
          serA hG hz6 Ψ q (cx c (Function.update ζ w s)) (cv c (Function.update ζ w s)) = _
        rw [cx_update, cv_update]
      have hA := hasFDerivAt_Aterm z c hpos hc2 w ζ
      rw [e, Dt_add _ _ _ hA.differentiableAt
        (differentiableAt_serA_curve hE Ψ hq _ _ hvpos w (c w) (hcd w) hx hv),
        Dt_of_hasFDerivAt_zero _ _ hA, zero_add, H1 w q hq _ _ hvpos hx hv]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    · have e : (fun s => DList m l (fun ζ => Aterm z c ζ + serA hG hz6 Ψ q (cx c ζ) (cv c ζ))
            (Function.update ζ w s))
          = fun s => serA hG hz6 Ψ (fun ν => q ν * (l.map fun w => μ w ν).prod)
              (Function.update (cx c ζ) w (c w s).1) (Function.update (cv c ζ) w (c w s).2) := by
        funext s
        rw [ih hl' hnil (Function.update ζ w s) (fun w' hw' => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hw' hwl)]
          exact hζ w' (List.mem_cons_of_mem _ hw')), cx_update, cv_update]
      rw [e, H1 w _ (hq.mul (PolyB.listProd μ hμ l)) _ _ hvpos hx hv]
      unfold serA
      refine tsum_congr fun ν => ?_
      simp only [List.map_cons, List.prod_cons]
      ring

/-- `θ̃_Ψ` in ambient coordinates: constant term plus the series with the constant weight. -/
lemma thetaT_mk_serA (Ψ : GSection ι P 𝔪) (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    thetaT hG hz6 Ψ (X.mk x v hv) =
      zc hG hz6 Ψ * ((∏ w, v w : ℝ) : ℂ) ^ (2 / 3 : ℂ) + serA hG hz6 Ψ (fun _ => kapC F) x v := by
  rw [thetaT_mk]
  unfold serA
  rw [← tsum_mul_left]
  refine congrArg₂ (· + ·) rfl (tsum_congr fun ν => ?_)
  ring

/-- **The mixed derivative of `θ̃_Ψ` along a family of curves, termwise.** -/
theorem Dm_thetaT_curve (hE : ThmE hG hz6 g P) (Ψ : GSection ι P 𝔪) (m : InfinitePlace F → ℤ)
    (c : InfinitePlace F → ℂ → ℂ × ℝ) (hpos : ∀ w s, 0 < (c w s).2)
    (hcd : ∀ w, DifferentiableAt ℝ (c w) 0)
    (hc2 : ∀ w, HasFDerivAt (fun s => (c w s).2) (0 : ℂ →L[ℝ] ℝ) 0)
    (μ : InfinitePlace F → {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (hμ : ∀ w, PolyB (μ w))
    (H1 : ∀ (w : InfinitePlace F) (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ), PolyB q →
      ∀ (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ), (∀ w', 0 < v w') →
        x w = (c w 0).1 → v w = (c w 0).2 →
        Dt (m w) (fun s => serA hG hz6 Ψ q (Function.update x w (c w s).1)
          (Function.update v w (c w s).2)) = serA hG hz6 Ψ (fun ν => q ν * μ w ν) x v) :
    Dm m (fun ζ : InfinitePlace F → ℂ =>
        thetaT hG hz6 Ψ (X.mk (cx c ζ) (cv c ζ) (fun w => hpos w (ζ w)))) 0 =
      serA hG hz6 Ψ (fun ν => kapC F * (Finset.univ.toList.map fun w => μ w ν).prod)
        (cx c 0) (cv c 0) := by
  have hne : (Finset.univ : Finset (InfinitePlace F)).toList ≠ [] := by
    rw [ne_eq, Finset.toList_eq_nil]
    exact Finset.univ_nonempty.ne_empty
  have e : (fun ζ : InfinitePlace F → ℂ =>
        thetaT hG hz6 Ψ (X.mk (cx c ζ) (cv c ζ) (fun w => hpos w (ζ w))))
      = fun ζ => Aterm (zc hG hz6 Ψ) c ζ + serA hG hz6 Ψ (fun _ => kapC F) (cx c ζ) (cv c ζ) := by
    funext ζ
    exact thetaT_mk_serA Ψ (cx c ζ) (cv c ζ) _
  unfold Dm
  rw [e]
  exact DList_curve hE Ψ m c _ hpos hcd hc2 μ hμ H1 _ (Finset.nodup_toList _) hne _
    (polyB_const _) 0 (fun _ _ => rfl)

/-! ### The two curves -/

lemma list_prod_map_neg {W : Type*} (l : List W) (f : W → ℂ) :
    (l.map fun w => -f w).prod = (-1) ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ]
    ring

/-- **`∂_m` of `θ̃_Ψ` along `curveW` in every place** (`m = ±1`), termwise: the `ν`-th term of
(Exp) at the base point `(X₀, |y|²)` is multiplied by `∏_w 2πi·(ν_w y_w²)^{(−m_w)}`. -/
theorem Dm_thetaT_curveW (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ)
    (hm : ∀ w, m w = 1 ∨ m w = -1) (Ψ : GSection ι P 𝔪) (X₀ y : InfinitePlace F → ℂ)
    (hy : ∀ w, y w ≠ 0) :
    Dm m (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Ψ
        (ArtinKP.X.X.mk (fun w => (curveW (X₀ w) (y w) (ζ w)).1)
          (fun w => (curveW (X₀ w) (y w) (ζ w)).2)
          (fun w => curveW_pos (X₀ w) (hy w) (ζ w)))) 0 =
      serA hG hz6 Ψ (fun ν => kapC F * (Finset.univ.toList.map fun w : InfinitePlace F =>
          (2 * Real.pi * Complex.I) * cj (-m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2)).prod)
        X₀ (fun w => ‖y w‖ ^ 2) := by
  have h := Dm_thetaT_curve hE Ψ m (fun w => curveW (X₀ w) (y w))
    (fun w s => curveW_pos (X₀ w) (hy w) s)
    (fun w => (hasFDerivAt_curveW (X₀ w) (y w)).differentiableAt)
    (fun w => (hasFDerivAt_curveW (X₀ w) (y w)).snd.congr_fderiv (by ext h; simp))
    (fun w ν => (2 * Real.pi * Complex.I) * cj (-m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2))
    (fun w => polyB_place _ _ _ w)
    (fun w q hq x v hv hx hvw => by
      have hx' : x w = X₀ w := hx.trans (by rw [curveW_zero])
      have hv' : v w = ‖y w‖ ^ 2 := hvw.trans (by rw [curveW_zero])
      have := Dt_serA_curveW hE Ψ hq x v hv w (y w) hv' (hm w)
      rw [hx'] at this
      exact this)
  have hx0 : cx (fun w => curveW (X₀ w) (y w)) 0 = X₀ := by
    funext w
    show (curveW (X₀ w) (y w) 0).1 = _
    rw [curveW_zero]
  have hv0 : cv (fun w => curveW (X₀ w) (y w)) 0 = fun w => ‖y w‖ ^ 2 := by
    funext w
    show (curveW (X₀ w) (y w) 0).2 = _
    rw [curveW_zero]
  rw [hx0, hv0] at h
  exact h

/-- **`∂_m` of `θ̃_Ψ` along `curveN` in every place**, termwise: the `ν`-th term of (Exp) at the
base point `(X₀, |y|²)` is multiplied by `∏_w (−2πi)·(ν_w y_w²)^{(m_w)}`. -/
theorem Dm_thetaT_curveN (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ)
    (Ψ : GSection ι P 𝔪) (X₀ y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) :
    Dm m (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Ψ
        (ArtinKP.X.X.mk (fun w => (curveN (X₀ w) (y w) (ζ w)).1)
          (fun w => (curveN (X₀ w) (y w) (ζ w)).2)
          (fun w => curveN_pos (X₀ w) (hy w) (ζ w)))) 0 =
      serA hG hz6 Ψ (fun ν => kapC F * (Finset.univ.toList.map fun w : InfinitePlace F =>
          -(2 * Real.pi * Complex.I) * cj (m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2)).prod)
        X₀ (fun w => ‖y w‖ ^ 2) := by
  have h := Dm_thetaT_curve hE Ψ m (fun w => curveN (X₀ w) (y w))
    (fun w s => curveN_pos (X₀ w) (hy w) s)
    (fun w => (hasFDerivAt_curveN (X₀ w) (y w) 0).differentiableAt)
    (fun w => (hasFDerivAt_curveN (X₀ w) (y w) 0).snd.congr_fderiv (by ext h; simp))
    (fun w ν => -(2 * Real.pi * Complex.I) * cj (m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2))
    (fun w => polyB_place _ _ _ w)
    (fun w q hq x v hv hx hvw => by
      have hx' : x w = X₀ w := hx.trans (by rw [curveN_zero])
      have hv' : v w = ‖y w‖ ^ 2 := hvw.trans (by rw [curveN_zero])
      have := Dt_serA_curveN hE Ψ hq x v hv w (y w) hv' (m w)
      rw [hx'] at this
      exact this)
  have hx0 : cx (fun w => curveN (X₀ w) (y w)) 0 = X₀ := by
    funext w
    show (curveN (X₀ w) (y w) 0).1 = _
    rw [curveN_zero]
  have hv0 : cv (fun w => curveN (X₀ w) (y w)) 0 = fun w => ‖y w‖ ^ 2 := by
    funext w
    show (curveN (X₀ w) (y w) 0).2 = _
    rw [curveN_zero]
  rw [hx0, hv0] at h
  exact h

/-- **Stub G2a-2 closed: the multi-place Weyl flip for `θ̃_Ψ`** (MATH3 (2.3) before (Aut));
statement identical to `G2a_Stubs.weyl_flip_thetaT`. -/
theorem weylFlip_thetaT (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ)
    (hm : ∀ w, m w = 1 ∨ m w = -1) (Ψ : GSection ι P 𝔪) (X₀ y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) :
    Dm m (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Ψ
        (ArtinKP.X.X.mk (fun w => (curveW (X₀ w) (y w) (ζ w)).1) (fun w => (curveW (X₀ w) (y w) (ζ w)).2)
          (fun w => curveW_pos (X₀ w) (hy w) (ζ w)))) 0 =
      (-1) ^ Fintype.card (InfinitePlace F) *
        Dm (fun w => -m w) (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Ψ
          (ArtinKP.X.X.mk (fun w => (curveN (X₀ w) (y w) (ζ w)).1) (fun w => (curveN (X₀ w) (y w) (ζ w)).2)
            (fun w => curveN_pos (X₀ w) (hy w) (ζ w)))) 0 := by
  rw [Dm_thetaT_curveW hE m hm Ψ X₀ y hy, Dm_thetaT_curveN hE (fun w => -m w) Ψ X₀ y hy]
  have hp : ∀ ν : {ν : SInt 𝔪 // ν ≠ 0},
      (Finset.univ.toList.map fun w : InfinitePlace F =>
        -(2 * Real.pi * Complex.I) * cj (-m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2)).prod
      = (-1) ^ Fintype.card (InfinitePlace F) *
        (Finset.univ.toList.map fun w : InfinitePlace F =>
          (2 * Real.pi * Complex.I) * cj (-m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2)).prod := by
    intro ν
    simp only [neg_mul]
    rw [list_prod_map_neg, Finset.length_toList, Finset.card_univ]
  have h1 : ((-1 : ℂ) ^ Fintype.card (InfinitePlace F)) * (-1) ^ Fintype.card (InfinitePlace F) = 1 := by
    rw [← mul_pow]
    norm_num
  unfold serA
  rw [← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  beta_reduce
  rw [hp ν]
  linear_combination (-(kapC F * (Finset.univ.toList.map fun w : InfinitePlace F =>
    (2 * Real.pi * Complex.I) * cj (-m w) (w.embedding ((ν : SInt 𝔪) : F) * y w ^ 2)).prod *
    (T.tau hG hz6 Ψ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) (fun w => ‖y w‖ ^ 2)) *
    eInf (emb ((ν : SInt 𝔪) : F) * X₀))) * h1

end

end ArtinKP.GW
end

section
-- module Solutions.Artin.KP.GR_Main
/-! # WP-GR, file 4: the final assembly

* `weylFlip`: the named hypothesis `GR.WeylFlip` discharged by `GW.weyl_flip_thetaT`.
* **`secCut : HB.SecCut n F ι`** — `c = 4π`, `α = 1/4`, `J = GK.Jdef hG hz6 Φ₀`,
  `bf = GK.bfdef hG hz6 Φ₀ k`, `Θ = GR.ThetaG hG hz6 m Φ₀`, `k₀` a deep level of the symbol package.
* `autCut2`, `kpCutNu`, and **`goal`**: the frozen statement 8b3180bd, written out (checked against the stub in `GR_Check`).
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.G2a

noncomputable section

/-- The Weyl flip (WP-GW) in the form of the named hypothesis of `GR_Flip`. -/
theorem weylFlip_of_thmE_oai {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
    {ι : F →+* ℂ} {P : CubicPkg F} {hG : Good 𝔪} {z6 : 𝓞 F} {hz6 : IsPrimitiveRoot z6 6}
    {g : AllowedGen ι 𝔪} (hE : ThmE hG hz6 g P) : WeylFlip (ι := ι) P hG hz6 :=
  fun m hm Ψ X₀ y hy => GW.weylFlip_thetaT hE m hm Ψ X₀ y hy

end

end ArtinKP.GR
end

theorem solution.{u_1} : type_of% @ArtinKP.GR.weylFlip_of_thmE_oai.{u_1} := @ArtinKP.GR.weylFlip_of_thmE_oai.{u_1}
