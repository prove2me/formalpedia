-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0329_parallel1
-- name    : PNT_ZeroFree_433_0329_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:43:06.373096+00:00
-- url     : https://prove2.me/theorems/e2979f14-4245-45ca-bc73-787f66f2e489
-- title:
--   Zero-free region foundations: PrimeNumberTheoremAnd.Wiener [0329_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - PrimeNumberTheoremAnd.Wiener
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean#L867-L1374

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


theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict


set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext ; congr ; ext
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    congr
    rw [← neg_mul] ; congr ; norm_cast ; field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)


lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩


lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub


lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring


theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := k2 ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxδ
    change 0 ≤ x at hx
    rcases lt_or_eq_of_le hx with hp | rfl
    · exact hd hp hxδ
    · simpa using hε

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert! this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert! this using 1 <;> simp ; ring


-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead


/-
Now we add the hypothesis that $f(n) \geq 0$ for all $n$.

-/


-- TODO with `Ico`


/- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/


/-
\section{Weak PNT}

-/

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)


-- #print axioms WeakPNT


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


