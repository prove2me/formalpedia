-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0330_parallel1
-- name    : PNT_ZeroFree_433_0330_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:45:57.284473+00:00
-- url     : https://prove2.me/theorems/bb79e6da-8c5f-4aee-98e8-d979991cda05
-- title:
--   Zero-free region foundations: PrimeNumberTheoremAnd.Wiener [0330_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - PrimeNumberTheoremAnd.Wiener
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean#L1632-L2340

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327
import Definitions.Def_PNT_ZeroFree_433_0505

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
/- Original source header, including license and authors:

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.EMetricSpace.BoundedVariation
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics
import PrimeNumberTheoremAnd.Fourier
import PrimeNumberTheoremAnd.SmoothExistence
import Mathlib.Analysis.Convolution


-/
set_option lang.lemmaCmd true
set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

/-
The Fourier transform of an absolutely integrable function $\psi: \R \to \C$ is defined by the
formula $$ \hat \psi(u) := \int_\R e(-tu) \psi(t)\ dt$$ where $e(\theta) := e^{2\pi i \theta}$.

Let $f: \N \to \C$ be an arithmetic function such that $\sum_{n=1}^\infty \frac{|f(n)|}{n^\sigma} <
\infty$ for all $\sigma>1$.  Then the Dirichlet series
$$ F(s) := \sum_{n=1}^\infty \frac{f(n)}{n^s}$$
is absolutely convergent for $\sigma>1$.
-/


-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar


attribute [fun_prop] measurable_coe_nnreal_ennreal


/-
Now let $A \in \C$, and suppose that there is a continuous function $G(s)$ defined on
$\mathrm{Re} s \geq 1$ such that $G(s) = F(s) - \frac{A}{s-1}$ whenever $\mathrm{Re} s > 1$.
We also make the Chebyshev-type hypothesis
\begin{equation}\label{cheby}
\sum_{n \leq x} |f(n)| \ll x
\end{equation}
for all $x \geq 1$ (this hypothesis is not strictly necessary, but simplifies the arguments and
can be obtained fairly easily in applications).
-/


-- Here compact support is used but perhaps it is not necessary


/- Should this be a gcongr lemma? -/


-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead


lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f


noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

set_option backward.isDefEq.respectTransparency false in
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]


local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal


lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert! max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert! max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)


lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]


/-
Now we add the hypothesis that $f(n) \geq 0$ for all $n$.

-/


lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]


-- TODO with `Ico`


/- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert! (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N


/-
\section{Weak PNT}

-/

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)


-- #print axioms WeakPNT

section auto_cheby

variable {f : ℕ → ℝ}

lemma norm_x_cpow_it (x t : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
  rw [cpow_def_of_ne_zero <| ofReal_ne_zero.mpr hx.ne', ← ofReal_log hx.le]
  convert! norm_exp_ofReal_mul_I (t * x.log) using 2
  push_cast; ring_nf


lemma tendsto_tsum_of_monotone_convergence
    {β : Type*} {f : ℕ → β → ENNReal} {g : β → ENNReal}
    (hmono : ∀ k, Monotone (fun n => f n k))
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) := by
  let : MeasurableSpace β := ⊤
  let μ : Measure β := Measure.count
  have hg_iSup (k : β) : (⨆ n : ℕ, f n k) = g k := iSup_eq_of_tendsto (hmono k) (hlim k)
  have h_tend_lint : Tendsto (fun n => ∫⁻ k, f n k ∂μ) atTop (𝓝 (∫⁻ k, (⨆ n, f n k) ∂μ)) := by
    have hmeas : ∀ n, Measurable fun k : β => f n k := fun _ _ _ ↦ trivial
    have hmono_fn : Monotone (fun n => fun k : β => f n k) := fun _ _ hnm k ↦ hmono k hnm
    simpa [lintegral_iSup hmeas hmono_fn] using
      tendsto_atTop_iSup fun _ _ hmn ↦ lintegral_mono fun k ↦ hmono k hmn
  simpa [μ, lintegral_count, hg_iSup] using h_tend_lint


/-
\section{Removing the Chebyshev hypothesis}

In this section we do *not* assume the bound \eqref{cheby}, but instead derive it from the other hypotheses.

-/


/- Smooth compactly supported function with non-negative Fourier transform via self-convolution. -/


/- The series `∑ f(n)/n · 𝓕ψ(log(n/x)/(2π))` is summable for `x ≥ 1`. -/


/- Short interval bound from global filtered bound: if `∑ f(n)/n · 𝓕ψ(log(n/x)) ≤ B`,
then `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for some `ε, C > 0`. -/


/- Bootstraps short interval bounds to global Chebyshev bound via strong induction.
If `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for all `x ≥ 1`, then `∑_{n ≤ x} f(n) = O(x)`. -/


end auto_cheby

/-
\section{The prime number theorem in arithmetic progressions}
-/


/- The von Mangoldt function divided by `n ^ s` is summable for `s > 1`. -/


/-
\section{The Chebotarev density theorem: the case of cyclotomic extensions}

Throughout this section, $K$ is a number field, $m \geq 1$ is a fixed integer,
$L = K(\mu_m)$, and $G = \mathrm{Gal}(L/K)$.  (In particular $G$ is abelian, and for
$K=\mathbb{Q}$ one recovers $G \cong (\mathbb{Z}/m\mathbb{Z})^\times$.)
Write $\zeta_K$ and $\zeta_L$ for the Dedekind zeta functions of $K$ and $L$, and for
an abelian character $\chi : G \to \mathbb{C}^\times$ write $L(\chi,s)$ for the associated
Artin $L$-function (equivalently, the Hecke $L$-function of the ideal character attached to
$\chi$; cf.\ Notation~7.1.17 and Proposition~7.1.18 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf}).

The goal of this section is to prove the Chebotarev density theorem in the cyclotomic case
(Proposition~\ref{Chebotarev-cyclotomic-density} below), following the classical argument via
Artin $L$-functions as in Sharifi, Propositions~7.1.16--7.1.19 and Proposition~7.2.1.  The
abelian and general cases are then reduced to this one in the subsequent sections.
-/

/-
\begin{lemma}[Artin $L$-function as Euler product]\label{Artin-L-euler}
Let $\chi : G \to \mathbb{C}^\times$ be an abelian character.  For $\Re(s) > 1$ one has
\[
L(\chi,s) \;=\; \prod_{\mathfrak{p}} \bigl(1 - \chi(\mathfrak{p})\, N\mathfrak{p}^{-s}\bigr)^{-1}
\;=\; \sum_{\mathfrak{a} \subseteq \mathcal{O}_K} \chi(\mathfrak{a})\, N\mathfrak{a}^{-s},
\]
where the product runs over nonzero prime ideals of $\mathcal{O}_K$, with the convention
$\chi(\mathfrak{p}) = 0$ if $\mathfrak{p}$ ramifies in the fixed field of $\ker\chi$.
\end{lemma}
-/

/-
\begin{proof}
This is the specialisation of the Artin Euler product (Definition~7.1.15 of Sharifi) to
abelian characters; see Proposition~7.1.18 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.  Absolute convergence for $\Re(s)>1$
follows from comparison with $\zeta_K(s)$.
\end{proof}
-/

/-
\begin{lemma}[Dedekind-factor]\label{Dedekind-factor}
For $\Re(s) > 1$ one has
\[
\zeta_L(s) \;=\; \prod_{\chi : G \to \mathbb{C}^\times} L(\chi,s),
\]
where the product runs over all (necessarily one-dimensional) irreducible characters of $G$.
\end{lemma}
-/

/-
\begin{proof}\uses{Artin-L-euler}
In general, for a Galois extension $L/K$ and characters $\chi$ of irreducible representations of
$\mathrm{Gal}(L/K)$, Proposition~7.1.16 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf} gives
$\zeta_L(s) = \prod_\chi L(\chi,s)^{\chi(1)}$ for $\Re(s)>1$.  In the present abelian
(cyclotomic) setting every irreducible character is one-dimensional, so $\chi(1)=1$ and the
exponents disappear.  Alternatively, comparing Euler factors at an unramified prime
$\mathfrak{p}$: the primes of $L$ above $\mathfrak{p}$ contribute the factor
$(1 - N\mathfrak{p}^{-fs})^{-g}$ to $\zeta_L$, while the Artin factors multiply to the same
quantity by the usual identity $\prod_\chi (1 - \chi(\varphi_{\mathfrak{p}}) X) = 1 - X^f$
(with $X = N\mathfrak{p}^{-s}$ and $f$ the residue degree).
\end{proof}
-/

/-
\begin{lemma}[Simple pole]\label{Dedekind-pole}
The Dedekind zeta function $\zeta_L$ admits a meromorphic continuation to a neighbourhood of
the line $\Re(s)=1$ with a single simple pole at $s=1$ (and is otherwise holomorphic and
nonvanishing on that line after removing the pole).  In particular
$\log \zeta_L(s) \sim \log(s-1)^{-1}$ as $s \to 1^+$.
\end{lemma}
-/

/-
\begin{proof}
This is the standard analytic continuation of Dedekind zeta (Theorem~7.1.12 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf}): absolute convergence of the ideal
Dirichlet series and Euler product for $\Re(s)>1$, meromorphic continuation across
$\Re(s)>1-[L:\mathbb{Q}]^{-1}$, and a simple pole at $s=1$.  The logarithmic asymptotic is
immediate from the simple pole.
\end{proof}
-/

/-
\begin{lemma}[Continuation of nontrivial Artin $L$-functions]\label{Artin-L-continuation}
Let $\chi : G \to \mathbb{C}^\times$ be a nontrivial character.  Then $L(\chi,s)$ extends to an
analytic function on the half-plane $\Re(s) > 1 - [K:\mathbb{Q}]^{-1}$, and in particular is
holomorphic at $s=1$.
\end{lemma}
-/

/-
\begin{proof}
Following Proposition~7.1.19 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}: let $n$
be the order of $\chi$.  Geometry of numbers supplies the estimate that, for each $n$th root of
unity $\zeta$, the number of ideals $\mathfrak{a}$ with $N\mathfrak{a} \leq N$ and
$\chi(\mathfrak{a})=\zeta$ is $CN + O\bigl(N^{1-[K:\mathbb{Q}]^{-1}}\bigr)$ with $C$ independent of
$\zeta$.  Summing against $\zeta$ cancels the main terms, so
$\sum_{N\mathfrak{a}\leq N} \chi(\mathfrak{a}) = O\bigl(N^{1-[K:\mathbb{Q}]^{-1}}\bigr)$.
Lemma~7.1.5 of Sharifi then yields absolute uniform convergence of
$\sum_{\mathfrak{a}} \chi(\mathfrak{a})\, N\mathfrak{a}^{-s}$ on compact subsets of
$\Re(s) > 1 - [K:\mathbb{Q}]^{-1}$.
\end{proof}
-/

/-
\begin{lemma}[Dedekind-nonvanishing]\label{Dedekind-nonvanishing}
For any nontrivial character $\chi$ of $G = \mathrm{Gal}(L/K)$, one has $L(\chi,1) \neq 0$.
Moreover $L(\chi,s)$ does not vanish for $\Re(s)=1$.
\end{lemma}
-/

/-
\begin{proof}\uses{Dedekind-factor, Dedekind-pole, Artin-L-continuation}
For the value at $s=1$: write $\log\zeta_L(t) = \sum_\chi \log L(\chi,t)$ for real $t>1$.
As $t\to 1^+$, the left side is $\sim \log(t-1)^{-1}$ by Lemma~\ref{Dedekind-pole}.  If some
nontrivial $L(\chi,\cdot)$ had a zero of order $m_\chi \geq 1$ at $s=1$, the right side would
behave like $\bigl(1 - \sum_\chi m_\chi\bigr)\log(t-1)^{-1}$ up to a bounded error
(the trivial character contributes the pole of $\zeta_K$, absorbed into the factorisation),
forcing $1-\sum m_\chi \leq 0$, a contradiction.  Hence $L(\chi,1)\neq 0$ for all nontrivial
$\chi$ (Sharifi, Proposition~7.1.19).

For the rest of the line $\Re(s)=1$, $s\neq 1$: adapt the classical nonvanishing argument for
Dirichlet $L$-functions (comparison of $\zeta_L(s)$, $\zeta_L(s)^3\,|L(\chi,s)|^4$, or the
$3+4\operatorname{Re}$ inequality) using the Euler product of Lemma~\ref{Artin-L-euler} and the
absence of poles of nontrivial $L(\chi,\cdot)$ on $\Re(s)=1$ from
Lemma~\ref{Artin-L-continuation}.
\end{proof}
-/

/-
\begin{lemma}[Orthogonality for Frobenius classes]\label{Chebotarev-orthogonality}
Fix $\sigma \in G$.  For every prime ideal $\mathfrak{p}$ of $\mathcal{O}_K$ unramified in $L$,
\[
\sum_{\chi : G \to \mathbb{C}^\times} \chi(\sigma)^{-1}\,\chi(\varphi_{\mathfrak{p}})
\;=\;
\begin{cases}
|G| & \text{if }\varphi_{\mathfrak{p}} = \sigma,\\
0 & \text{otherwise.}
\end{cases}
\]
Equivalently, if $\sigma(\zeta_m) = \zeta_m^a$ with $\gcd(a,m)=1$, the sum equals $|G|$
precisely when $N\mathfrak{p} \equiv a \pmod{m}$.
\end{lemma}
-/

/-
\begin{proof}
Standard character orthogonality on the finite abelian group $G$.  The reformulation in terms
of $N\mathfrak{p} \bmod m$ uses that $\varphi_{\mathfrak{p}}(\zeta_m) = \zeta_m^{N\mathfrak{p}}$
for the cyclotomic character.
\end{proof}
-/

/-
\begin{proposition}[Cyclotomic Chebotarev density]\label{Chebotarev-cyclotomic-density}
For every $\sigma \in G$, the set of prime ideals $\mathfrak{p}$ of $K$ unramified in $L$ with
Frobenius $\varphi_{\mathfrak{p}} = \sigma$ has Dirichlet density $1/|G|$.
\end{proposition}
-/

/-
\begin{proof}\uses{Dedekind-factor, Dedekind-pole, Dedekind-nonvanishing, Artin-L-euler,
Chebotarev-orthogonality}
This is Proposition~7.2.1 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.  For
$\Re(s)>1$ one has $\log L(\chi,s) \sim \sum_{\mathfrak{p}} \chi(\mathfrak{p})\, N\mathfrak{p}^{-s}$.
Summing against $\chi(\sigma)^{-1}$ and applying Lemma~\ref{Chebotarev-orthogonality} yields
\[
\sum_{\chi} \chi(\sigma)^{-1} \log L(\chi,s)
\;\sim\;
|G| \sum_{\varphi_{\mathfrak{p}}=\sigma} N\mathfrak{p}^{-s}.
\]
On the other hand, by Lemmas~\ref{Dedekind-factor} and~\ref{Dedekind-nonvanishing} the left
side is $\sim \log\zeta_K(s) \sim \log(s-1)^{-1}$ as $s\to 1^+$ (only the trivial character
contributes a pole).  Comparing the two asymptotics gives the asserted Dirichlet density.
\end{proof}
-/

/-
\begin{lemma}[PNT for one character]\label{Dedekind-PNT}
For any nontrivial character $\chi$ of $G$,
\[
\sum_{N\mathfrak{p} \leq x} \chi(\mathfrak{p})\, \log N\mathfrak{p} \;=\; o(x)
\qquad(x\to\infty).
\]
(Equivalently, writing $\Lambda_\chi$ for the von Mangoldt-type coefficients of $-\frac{L'}{L}(\chi,s)$,
one has $\sum_{n\leq x} \Lambda_\chi(n) = o(x)$.)
\end{lemma}

\emph{Remark on prime powers.}
Expanding $-\frac{L'}{L}(\chi,s)$ as a Dirichlet series selects coefficients supported on
prime powers $\mathfrak{p}^j$ with weight $\chi(\varphi_{\mathfrak{p}})^j\log N\mathfrak{p}$.
Thus an \emph{exact} identity expressing $-\sum_\chi \chi(\sigma)^{-1}\frac{L'}{L}(\chi,s)$ as a
sum over primes with Frobenius $\sigma$ should use the condition $\varphi_{\mathfrak{p}}^j=\sigma$
rather than $\varphi_{\mathfrak{p}}=\sigma$.  For the density statement in
Proposition~\ref{Chebotarev-cyclotomic-density} this distinction is immaterial: the $j=1$ terms
agree with the Frobenius condition, while the $j\geq 2$ terms converge absolutely for
$\Re(s)>1/2$ and do not affect the residue at $s=1$.
-/

/-
\begin{proof}\uses{Dedekind-nonvanishing, Artin-L-continuation}
By Lemmas~\ref{Artin-L-continuation} and~\ref{Dedekind-nonvanishing}, $L(\chi,s)$ is holomorphic
and nonvanishing on $\Re(s)\geq 1$, so $-\frac{L'}{L}(\chi,s)$ extends continuously to
$\Re(s)\geq 1$.  The claimed prime-sum estimate then follows by the same Wiener--Ikehara /
Ingham contour argument used for Dirichlet $L$-functions in the prime-number theorem in
arithmetic progressions (cf.\ the material already formalised for Dirichlet $L$-functions
earlier in this file).  Passing through $\Lambda_\chi$ (rather than the bare prime sum) makes
the $j\geq 2$ prime-power contributions explicit and shows they are $O(x^{1/2}\log x)$,
hence absorbable in the $o(x)$ error; cf.\ the remark after the statement.
\end{proof}
-/

/-
\section{The Chebotarev density theorem: the case of abelian extensions}

Now let $L/K$ be an arbitrary finite abelian extension with Galois group $G$, and fix
$\sigma \in G$.  The goal is to show that the primes of $K$ with Frobenius $\sigma$ still have
Dirichlet density $1/|G|$, by reducing to the cyclotomic case already treated.
(Cf.\ Theorem~7.2.2, Step~2, of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}; cyclic
extensions already suffice for the later reduction to the general case.)
-/

/-
\begin{lemma}[Cyclotomic crossing]\label{Chebotarev-abelian-crossing}
Choose an integer $m\geq 1$ not dividing the discriminant of $L/K$, large enough that
$H := \mathrm{Gal}(L(\mu_m)/L) \cong (\mathbb{Z}/m\mathbb{Z})^\times$ via the cyclotomic character
and $\mathrm{Gal}(L(\mu_m)/K) \cong G \times H$.  For $\sigma\in G$ and $\tau\in H$ write
$S_{\sigma,\tau}$ for the set of primes of $K$ unramified in $L(\mu_m)$ with Frobenius
$(\sigma,\tau)\in G\times H$, and $S_\sigma$ for the set of primes of $K$ unramified in $L$
with Frobenius $\sigma$ in $G$.  Then
\[
\delta_{\mathrm{inf}}(S_\sigma) \;=\; \sum_{\tau\in H} \delta_{\mathrm{inf}}(S_{\sigma,\tau}).
\]
\end{lemma}
-/

/-
\begin{proof}
Every prime counted in $S_\sigma$ lifts to primes in the various $S_{\sigma,\tau}$ according to
the Frobenius in the cyclotomic layer; the identity of lower densities is the usual additivity
of Dirichlet densities over a finite partition (up to the finitely many ramified primes).
\end{proof}
-/

/-
\begin{lemma}[Density after cyclotomic crossing]\label{Chebotarev-abelian-density}
In the notation of Lemma~\ref{Chebotarev-abelian-crossing}, if the order of $\tau\in H$ is
divisible by $|G|$, then $\langle(\sigma,\tau)\rangle \cap (G\times\{1\}) = \{1\}$, so
$L(\mu_m)$ is obtained by adjoining $\mu_m$ to the fixed field
$F := L(\mu_m)^{\langle(\sigma,\tau)\rangle}$.  Applying Proposition~\ref{Chebotarev-cyclotomic-density}
to the cyclotomic extension $F(\mu_m)/F$ and transporting densities as in the reduction step
of Theorem~7.2.2 yields $\delta(S_{\sigma,\tau}) = 1/(|G|\,|H|)$.
\end{lemma}
-/

/-
\begin{proof}\uses{Chebotarev-cyclotomic-density, Chebotarev-abelian-crossing}
See Sharifi, Theorem~7.2.2, Step~2 (display after ``Now suppose that $|G|$ divides the order of
$\tau$'').
\end{proof}
-/

/-
\begin{proposition}[Abelian Chebotarev]\label{Chebotarev-abelian}
Let $L/K$ be finite abelian with Galois group $G$.  For every $\sigma\in G$, the Dirichlet
density of primes of $K$ with Frobenius $\sigma$ exists and equals $1/|G|$.
\end{proposition}
-/

/-
\begin{proof}\uses{Chebotarev-abelian-crossing, Chebotarev-abelian-density,
Chebotarev-cyclotomic-density}
Let $H_n \subset H$ be the set of elements whose order is divisible by $n$.  Summing the
densities of Lemma~\ref{Chebotarev-abelian-density} over $\tau\in H_n$ gives
$\delta_{\mathrm{inf}}(S_\sigma) \geq |H_n|/(|G|\,|H|)$.  Choosing $m$ so that $|H_n|/|H|$ is
arbitrarily close to $1$ (possible since there are primes $m\equiv 1\pmod{n^j}$ by the
cyclotomic case already proved, and $|H_n|/|H|$ tends to $1$ as $j\to\infty$), one obtains
$\delta_{\mathrm{inf}}(S_\sigma) \geq 1/|G|$.  Summing over $\sigma\in G$ forces equality
throughout, so each density exists and equals $1/|G|$.
\end{proof}
-/

/-
\section{The Chebotarev density theorem: the general case}

Finally let $L/K$ be an arbitrary finite Galois extension with group $G$, and let $C\subset G$
be a conjugacy class.  The theorem reduces to the abelian (indeed cyclic) case already proved,
by passing to the fixed field of an element of $C$.
-/

/-
\begin{lemma}[Reduction to a cyclic subextension]\label{Chebotarev-reduction}
Fix $\sigma\in C$ and let $E$ be the fixed field of $\langle\sigma\rangle$, so $L/E$ is cyclic of
degree $f = |\langle\sigma\rangle|$.  Write $S$ for the set of primes of $K$ unramified in $L$
whose Frobenius class equals $C$, and $T_\sigma$ for the set of primes $\mathfrak{P}$ of $E$
unramified in $L$ (and lying over $K$) with Frobenius equal to $\sigma$.  Then
\[
\delta(S) \;=\; \frac{f\,|C|}{|G|}\,\delta(T_\sigma),
\]
whenever either density exists.  In particular, the Chebotarev statement for $L/K$ and $C$
follows from the abelian statement for the cyclic extension $L/E$ and the element $\sigma$.
\end{lemma}
-/

/-
\begin{proof}
If $\mathfrak{P}\in T_\sigma$, then $\varphi_{\mathfrak{P}}=\sigma$ fixes $E$, so $\mathfrak{P}$ has
residue degree one over $K$.  There are exactly $|G|/f$ primes of $L$ over $\mathfrak{P}\cap K$,
and their Frobenii are equidistributed among the $|C|$ elements of the conjugacy class $C$;
exactly $|G|/(f\,|C|)$ of them have Frobenius $\sigma$.  Comparing the Dirichlet series
$\sum N\mathfrak{p}^{-s}$ over $S$ with $\sum N\mathfrak{P}^{-s}$ over $T_\sigma$ (and using
$\sum_{\mathfrak{p}} N\mathfrak{p}^{-s} \sim \sum_{\mathfrak{P}} N\mathfrak{P}^{-s}$) yields the
displayed identity.  See Sharifi, Theorem~7.2.2, Step~1.
\end{proof}
-/

/-
\begin{theorem}[Chebotarev density theorem]\label{Chebotarev-general}
Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, and let
$C\subset G$ be a conjugacy class.  The set of prime ideals $\mathfrak{p}$ of $K$ unramified in
$L$ whose Frobenius conjugacy class equals $C$ has Dirichlet density $|C|/|G|$.
\end{theorem}
-/

/-
\begin{proof}\uses{Chebotarev-reduction, Chebotarev-abelian}
Combine Lemma~\ref{Chebotarev-reduction} with Proposition~\ref{Chebotarev-abelian} applied to
the cyclic extension $L/E$: the latter gives $\delta(T_\sigma) = 1/f$, whence
$\delta(S) = |C|/|G|$.
\end{proof}
-/

end


