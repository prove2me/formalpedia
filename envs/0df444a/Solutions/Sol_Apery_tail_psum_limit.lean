-- Prove2me | solution 1 for Apery.tail_psum_limit
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:51:11.725684+00:00
-- url     : https://prove2.me/submissions/e9d45353-b361-46b8-9c09-b59337b044b6

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The tail prime-sum limit (source `Apery/Growth/Assembly4.lean`)

This file proves the platform theorem `Apery.tail_psum_limit`:

$$\frac{1}{K^2}\sum_{K/400 < p \le K/20} p\,\Bigl(\frac{K}{p}F\Bigl(\frac{K}{p}\Bigr) +
\frac{27}{16}\Bigr)\log p \;\le\; -\frac{6843153}{128000000} + \delta \quad (K \to \infty),$$

where $F(x) = 4\lambda + 2\lambda\{x\} - 12\lambda\{\alpha x\}$ ($\lambda = 37/40$,
$\alpha = 3/40$) is the tail profile. A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the Abel summation and the limit of
the weighted prime sums (`Apery/PrimeSum.lean`, using the platform's proved prime number
theorem `Apery.theta_eventually_close`), the partition/step-sum bounds
(`Apery/PrimeSumStep.lean`, `Apery/PrimeSumIntegral.lean`), the piecewise-linear majorant on
the grid $t_i = 20 + i/3$, $i \le 1140$ with the numerical evaluation `tail_sum_le`
(two integrations by parts per piece and telescoping, `Apery/Growth/TailIntegral.lean`), and
the assembly in `Apery/Growth/Assembly4.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourcePrimeSum
import Theorems.Thm_Apery_theta_eventually_close

set_option autoImplicit false

section Port0
/-!
# The tail prime-sum limit (source `Apery/Growth/Assembly4.lean`, `TailIntegral.lean`,
# `PrimeSum*.lean`)

This file proves the platform theorem `Apery.tail_psum_limit`:

`psum (x F(x) + 27/16) 20 400 K / K² ≤ -6843153/128000000 + δ` eventually,

where `psum` is the weighted prime sum and `F` the tail profile. It is a faithful port of
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules `Apery/PrimeSum.lean`
(Abel summation and the limit of the weighted prime sums, using the platform's proved
prime number theorem `Apery.theta_eventually_close`), `Apery/PrimeSumStep.lean`,
`Apery/PrimeSumIntegral.lean`, `Apery/Growth/TailIntegral.lean` (the piecewise-linear
majorant on the grid `t_i = 20 + i/3` and the numerical evaluation `tail_sum_le`) and the
tail part of `Apery/Growth/Assembly4.lean`.
-/

set_option autoImplicit false

open Finset Filter Topology MeasureTheory Set Real Asymptotics

namespace Apery

/-! ## Weighted prime sums via the prime number theorem (`Apery/PrimeSum.lean`) -/

/-!
# Weighted prime sums via the prime number theorem

`∑_{a < p ≤ b} p log p = b θ(b) - a θ(a) - ∫_a^b θ` (Abel summation), and with `θ(x) ~ x`
this gives `∑_{K/d < p ≤ K/c} p log p = K² (1/c² - 1/d²)/2 + o(K²)`.
-/

open Finset Filter Topology MeasureTheory Set Real Asymptotics


lemma theta_eq_sum_cPrime (t : ℝ) : Chebyshev.theta t = ∑ k ∈ Icc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

/-- The weighted prime sum `∑_{a < p ≤ b} p log p` (as a sum over integers `k` with
`⌊a⌋₊ < k ≤ ⌊b⌋₊`). -/
noncomputable def wsum (a b : ℝ) : ℝ := ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ) * cPrime k

/-- Abel summation for the weighted prime sum. -/
lemma wsum_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    wsum a b = b * Chebyshev.theta b - a * Chebyshev.theta a -
      ∫ t in Ioc a b, Chebyshev.theta t := by
  unfold wsum
  have hd : deriv (fun t : ℝ => t) = fun _ => 1 := by funext t; simp
  have h := sum_mul_eq_sub_sub_integral_mul cPrime (f := fun t : ℝ => t) ha hab
    (fun t _ => differentiableAt_id) (by
      rw [hd]; exact integrableOn_const measure_Icc_lt_top.ne)
  simp only [hd, one_mul] at h
  rw [h, ← theta_eq_sum_cPrime, ← theta_eq_sum_cPrime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  exact (theta_eq_sum_cPrime t).symm


/-- `∫_a^b θ` is close to `(b² - a²)/2` when `θ` is close to the identity on `[a, b]`. -/
lemma integral_theta_bounds {a b ε : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ y ∈ Icc a b, |Chebyshev.theta y - y| ≤ ε * y) :
    |(∫ t in Ioc a b, Chebyshev.theta t) - (b ^ 2 - a ^ 2) / 2| ≤ ε * (b ^ 2 - a ^ 2) / 2 := by
  have hint : IntegrableOn Chebyshev.theta (Ioc a b) :=
    (Chebyshev.theta_mono.intervalIntegrable (μ := volume) (a := a) (b := b)).1
  have hsub : IntegrableOn (fun t : ℝ => t) (Ioc a b) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hid : ∫ t in Ioc a b, t = (b ^ 2 - a ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hab, integral_id]
  have hε : IntegrableOn (fun t : ℝ => ε * t) (Ioc a b) := hsub.const_mul ε
  calc |(∫ t in Ioc a b, Chebyshev.theta t) - (b ^ 2 - a ^ 2) / 2|
      = ‖∫ t in Ioc a b, (Chebyshev.theta t - t)‖ := by
        rw [← hid, ← integral_sub hint hsub, Real.norm_eq_abs]
    _ ≤ ∫ t in Ioc a b, ‖Chebyshev.theta t - t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc a b, ε * t := by
        refine setIntegral_mono_on (hint.sub hsub).norm hε measurableSet_Ioc fun t ht => ?_
        rw [Real.norm_eq_abs]
        exact h t (Ioc_subset_Icc_self ht)
    _ = ε * (b ^ 2 - a ^ 2) / 2 := by rw [integral_const_mul, hid]; ring

/-- The bound `|wsum a b - (b² - a²)/2| ≤ 2 η b²` when `|θ(y) - y| ≤ η y` on `[a, b]`. -/
lemma wsum_close {a b η : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hη : 0 ≤ η)
    (h : ∀ y ∈ Icc a b, |Chebyshev.theta y - y| ≤ η * y) :
    |wsum a b - (b ^ 2 - a ^ 2) / 2| ≤ 2 * η * b ^ 2 := by
  rw [wsum_eq ha hab]
  have h1 := h b ⟨hab, le_rfl⟩
  have h2 := h a ⟨le_rfl, hab⟩
  have h3 := integral_theta_bounds ha hab h
  have hb : 0 ≤ b := ha.trans hab
  have e1 : |b * Chebyshev.theta b - b ^ 2| ≤ η * b ^ 2 := by
    rw [show b * Chebyshev.theta b - b ^ 2 = b * (Chebyshev.theta b - b) by ring, abs_mul,
      abs_of_nonneg hb]
    nlinarith
  have e2 : |a * Chebyshev.theta a - a ^ 2| ≤ η * a ^ 2 := by
    rw [show a * Chebyshev.theta a - a ^ 2 = a * (Chebyshev.theta a - a) by ring, abs_mul,
      abs_of_nonneg ha]
    nlinarith
  have ha2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rw [abs_le] at e1 e2 h3 ⊢
  constructor <;> nlinarith

/-- `∑_{K/d < p ≤ K/c} p log p / K² → (1/c² - 1/d²)/2`. -/
theorem wsum_tendsto {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun K : ℝ => wsum (K / d) (K / c) / K ^ 2) atTop
      (𝓝 ((1 / c ^ 2 - 1 / d ^ 2) / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd : 0 < d := hc.trans hcd
  set η := ε * c ^ 2 / 8 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (theta_eventually_close hη)
  refine ⟨max (d * Y₀) 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := le_trans (le_max_right _ _) hK
  have hK0 : 0 < K := by linarith
  have hKY : d * Y₀ ≤ K := le_trans (le_max_left _ _) hK
  have ha : 0 ≤ K / d := by positivity
  have hab : K / d ≤ K / c := div_le_div_of_nonneg_left hK0.le hc hcd.le
  have hbound := wsum_close ha hab hη.le (fun y hy => hY₀ y (by
    have : Y₀ ≤ K / d := by rw [le_div_iff₀ hd]; linarith
    linarith [hy.1]))
  rw [Real.dist_eq]
  have e : wsum (K / d) (K / c) / K ^ 2 - (1 / c ^ 2 - 1 / d ^ 2) / 2 =
      (wsum (K / d) (K / c) - ((K / c) ^ 2 - (K / d) ^ 2) / 2) / K ^ 2 := by
    field_simp <;> ring
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < K ^ 2), div_lt_iff₀ (by positivity)]
  calc |wsum (K / d) (K / c) - ((K / c) ^ 2 - (K / d) ^ 2) / 2|
      ≤ 2 * η * (K / c) ^ 2 := hbound
    _ = ε * K ^ 2 / 4 := by rw [hη_def]; field_simp <;> ring
    _ < ε * K ^ 2 := by have : 0 < ε * K ^ 2 := by positivity
                        linarith


/-! ## Prime sums with a weight function (`Apery/PrimeSumStep.lean`) -/

/-!
# Prime sums with a weight function

`psum f a b K = ∑_{K/b < p ≤ K/a} p f(K/p) log p`. If `f ≤ v_j` on each cell `[c_j, c_{j+1}]`
of a partition `a = c_0 < ⋯ < c_r = b`, then
`psum f a b K ≤ ∑_j v_j wsum (K/c_{j+1}) (K/c_j)`, and the right-hand side is
`K² ∑_j v_j (1/c_j² - 1/c_{j+1}²)/2 + o(K²)`.
-/

open Finset Filter Topology Set


lemma cPrime_nonneg (k : ℕ) : 0 ≤ cPrime k := by
  unfold cPrime
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_rfl

/-- Splitting at an intermediate point. -/
lemma psum_split (f : ℝ → ℝ) {a c b K : ℝ} (ha : 0 < a) (hac : a ≤ c) (hcb : c ≤ b) (hK : 0 ≤ K) :
    psum f a b K = psum f a c K + psum f c b K := by
  unfold psum
  rw [add_comm, Finset.sum_Ioc_consecutive _
    (Nat.floor_le_floor (div_le_div_of_nonneg_left hK (by linarith) hcb))
    (Nat.floor_le_floor (div_le_div_of_nonneg_left hK ha hac))]

/-- If `f ≤ v` on `[a, b)`, then `psum f a b K ≤ v * wsum (K/b) (K/a)`. -/
lemma psum_le_of_le {f : ℝ → ℝ} {a b v K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K)
    (hf : ∀ x ∈ Ico a b, f x ≤ v) :
    psum f a b K ≤ v * wsum (K / b) (K / a) := by
  unfold psum wsum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_Ioc] at hk
  have hb : 0 < b := ha.trans_le hab
  have hk0 : 0 < k := by
    have := hk.1; omega
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hx1 : a ≤ K / k := by
    rw [le_div_iff₀ hk0']
    have h1 : (k : ℝ) ≤ K / a := by
      have := Nat.floor_le (div_nonneg hK.le ha.le) |>.trans' (Nat.cast_le.mpr hk.2)
      exact this
    rw [le_div_iff₀ ha] at h1
    linarith
  have hx2 : K / k < b := by
    rw [div_lt_iff₀ hk0']
    have h1 : K / b < k := by
      have := Nat.lt_floor_add_one (K / b)
      have h2 : (⌊K / b⌋₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk.1
      linarith
    rw [div_lt_iff₀ hb] at h1
    linarith
  have hc := cPrime_nonneg k
  have := hf (K / k) ⟨hx1, hx2⟩
  calc (k : ℝ) * cPrime k * f (K / k) ≤ (k : ℝ) * cPrime k * v :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = v * ((k : ℝ) * cPrime k) := by ring

/-- The step sum over a partition `c 0 < c 1 < ⋯ < c r`, with values `v j` on `[c j, c (j+1)]`. -/
noncomputable def stepSum (c v : ℕ → ℝ) (r : ℕ) (K : ℝ) : ℝ :=
  ∑ j ∈ range r, v j * wsum (K / c (j + 1)) (K / c j)

lemma c_zero_le {c : ℕ → ℝ} {r : ℕ} (h : ∀ j < r, c j ≤ c (j + 1)) : c 0 ≤ c r := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact (ih fun j hj => h j (by omega)).trans (h r (by omega))

/-- Upper bound of `psum` over a partition by the step sum. -/
lemma psum_le_stepSum {f : ℝ → ℝ} {c v : ℕ → ℝ} (r : ℕ) (hc0 : 0 < c 0)
    (hmono : ∀ j < r, c j ≤ c (j + 1)) (hf : ∀ j < r, ∀ x ∈ Ico (c j) (c (j + 1)), f x ≤ v j)
    {K : ℝ} (hK : 0 < K) :
    psum f (c 0) (c r) K ≤ stepSum c v r K := by
  induction r with
  | zero => simp [psum, stepSum]
  | succ r ih =>
    have hcr : c 0 ≤ c r := c_zero_le fun j hj => hmono j (by omega)
    rw [psum_split f hc0 hcr (hmono r (by omega)) hK.le, stepSum, Finset.sum_range_succ]
    exact add_le_add (ih (fun j hj => hmono j (by omega)) (fun j hj => hf j (by omega)))
      (psum_le_of_le (hc0.trans_le hcr) (hmono r (by omega)) hK (hf r (by omega)))

/-- The limit of the normalised step sum. -/
lemma stepSum_tendsto {c v : ℕ → ℝ} (r : ℕ) (hc0 : 0 < c 0) (hmono : ∀ j < r, c j < c (j + 1)) :
    Tendsto (fun K : ℝ => stepSum c v r K / K ^ 2) atTop
      (𝓝 (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2))) := by
  have hpos : ∀ j ≤ r, 0 < c j := by
    intro j hj
    induction j with
    | zero => exact hc0
    | succ j ih => exact (ih (by omega)).trans (hmono j (by omega))
  have e : (fun K : ℝ => stepSum c v r K / K ^ 2) =
      fun K => ∑ j ∈ range r, v j * (wsum (K / c (j + 1)) (K / c j) / K ^ 2) := by
    funext K
    unfold stepSum
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine tendsto_finsetSum _ fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  exact (wsum_tendsto (hpos j hj.le) (hmono j hj)).const_mul _

/-- Eventually, `psum f a b K / K² ≤ (upper Darboux sum) + ε`. -/
theorem psum_eventually_le {f : ℝ → ℝ} {c v : ℕ → ℝ} (r : ℕ) (hc0 : 0 < c 0)
    (hmono : ∀ j < r, c j < c (j + 1)) (hf : ∀ j < r, ∀ x ∈ Ico (c j) (c (j + 1)), f x ≤ v j)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop, psum f (c 0) (c r) K / K ^ 2 ≤
      (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2)) + ε := by
  have h := (stepSum_tendsto (v := v) r hc0 hmono).eventually (eventually_le_nhds (by linarith :
    (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2)) <
      (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2)) + ε))
  filter_upwards [h, eventually_gt_atTop 0] with K hK hK0
  have := psum_le_stepSum (f := f) r hc0 (fun j hj => (hmono j hj).le) hf hK0
  calc psum f (c 0) (c r) K / K ^ 2 ≤ stepSum c v r K / K ^ 2 :=
        div_le_div_of_nonneg_right this (by positivity)
    _ ≤ _ := hK


/-! ## Prime sums and integrals (`Apery/PrimeSumIntegral.lean`) -/

/-!
# Prime sums and integrals

For `f` Lipschitz on `[a, b]` (`0 < a < b`), `psum f a b K / K² ≤ ∫_a^b f(x)/x³ dx + ε` for all
large `K`; and the piecewise version for `f` given by Lipschitz pieces on `[t_i, t_{i+1})`.
-/

open Finset Filter Topology Set intervalIntegral MeasureTheory


lemma integral_inv_cube {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, x ^ (-3 : ℤ) = (1 / a ^ 2 - 1 / b ^ 2) / 2 := by
  rw [integral_zpow (Or.inr ⟨by norm_num, fun h => ?_⟩)]
  · norm_num
    field_simp
    ring
  · rcases le_total a b with hab | hab
    · rw [uIcc_of_le hab] at h; linarith [h.1]
    · rw [uIcc_of_ge hab] at h; linarith [h.1]

/-- Upper bound for `psum` by the integral, for `f` Lipschitz on `[a, b]`. -/
theorem psum_le_integral {f : ℝ → ℝ} {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Icc a b))
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ L * |x - y|) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop, psum f a b K / K ^ 2 ≤ (∫ x in a..b, f x / x ^ 3) + ε := by
  -- choose the mesh
  obtain ⟨r, hr⟩ := exists_nat_gt (2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / ε)
  have hr0 : 0 < r := by
    have : (0 : ℝ) ≤ 2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / ε := by
      have : 1 / b ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have : 0 ≤ 1 / a ^ 2 - 1 / b ^ 2 := by linarith
      positivity
    have : (0 : ℝ) < r := lt_of_le_of_lt this hr
    exact_mod_cast this
  set δ := (b - a) / r with hδ
  have hδ0 : 0 < δ := by positivity
  set c : ℕ → ℝ := fun j => a + j * δ with hc
  have hc0 : c 0 = a := by simp [hc]
  have hcr : c r = b := by simp only [hc]; rw [hδ]; field_simp; ring
  have hmono : ∀ j < r, c j < c (j + 1) := by
    intro j _; simp only [hc]; push_cast; linarith
  have hcle : ∀ j, j ≤ r → a ≤ c j ∧ c j ≤ b := by
    intro j hj
    simp only [hc]
    constructor
    · have : (0:ℝ) ≤ j * δ := by positivity
      linarith
    · have : (j : ℝ) * δ ≤ r * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ0.le
      have : (r : ℝ) * δ = b - a := by rw [hδ]; field_simp
      linarith
  set v : ℕ → ℝ := fun j => f (c j) + L * δ with hv
  have hf : ∀ j < r, ∀ x ∈ Ico (c j) (c (j + 1)), f x ≤ v j := by
    intro j hj x hx
    have hcj := hcle j hj.le
    have hcj1 := hcle (j + 1) hj
    have hxI : x ∈ Icc a b := ⟨hcj.1.trans hx.1, hx.2.le.trans hcj1.2⟩
    have := hLip x hxI (c j) ⟨hcj.1, hcj.2⟩
    have hd : |x - c j| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hx.1])]
      have : c (j + 1) = c j + δ := by simp only [hc]; push_cast; ring
      linarith [hx.2]
    simp only [hv]
    have := abs_le.mp this
    nlinarith
  -- the Darboux sum is at most the integral plus the error
  have hD : (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2)) ≤
      (∫ x in a..b, f x / x ^ 3) + 2 * L * δ * ((1 / a ^ 2 - 1 / b ^ 2) / 2) := by
    have hint : ∀ j < r, IntervalIntegrable (fun x => (f x + 2 * L * δ) * x ^ (-3 : ℤ)) volume
        (c j) (c (j + 1)) := by
      intro j hj
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (hmono j hj).le]
      have hsub : Icc (c j) (c (j + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (hcle j hj.le).1 (hcle (j + 1) hj).2
      refine ((hcont.mono hsub).add continuousOn_const).mul ?_
      exact continuousOn_id.zpow₀ (-3) fun x hx =>
        Or.inl (ha.trans_le ((hcle j hj.le).1.trans hx.1)).ne'
    have h1 : ∀ j < r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2) ≤
        ∫ x in c j..c (j + 1), (f x + 2 * L * δ) * x ^ (-3 : ℤ) := by
      intro j hj
      have hcj := hcle j hj.le
      have hcj1 := hcle (j + 1) hj
      rw [← integral_inv_cube (ha.trans_le hcj.1) (ha.trans_le hcj1.1),
        ← intervalIntegral.integral_const_mul]
      apply integral_mono_on (hmono j hj).le
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (hmono j hj).le]
        exact continuousOn_const.mul (continuousOn_id.zpow₀ (-3) fun x hx =>
          Or.inl (ha.trans_le (hcj.1.trans hx.1)).ne')
      · exact hint j hj
      intro x hx
      have hxI : x ∈ Icc a b := ⟨hcj.1.trans hx.1, hx.2.trans hcj1.2⟩
      have hx0 : 0 < x := ha.trans_le hxI.1
      have hLx := hLip (c j) ⟨hcj.1, hcj.2⟩ x hxI
      have hd : |c j - x| ≤ δ := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
        have : c (j + 1) = c j + δ := by simp only [hc]; push_cast; ring
        linarith [hx.2]
      have hvle : v j ≤ f x + 2 * L * δ := by
        simp only [hv]
        have := abs_le.mp hLx
        nlinarith
      exact mul_le_mul_of_nonneg_right hvle (by positivity)
    calc (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2))
        ≤ ∑ j ∈ range r, ∫ x in c j..c (j + 1), (f x + 2 * L * δ) * x ^ (-3 : ℤ) :=
          Finset.sum_le_sum fun j hj => h1 j (Finset.mem_range.mp hj)
      _ = ∫ x in a..b, (f x + 2 * L * δ) * x ^ (-3 : ℤ) := by
          rw [sum_integral_adjacent_intervals hint, hc0, hcr]
      _ = (∫ x in a..b, f x / x ^ 3) + 2 * L * δ * ((1 / a ^ 2 - 1 / b ^ 2) / 2) := by
          rw [← integral_inv_cube ha (ha.trans hab), ← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_add]
          · apply integral_congr
            intro x hx
            rw [uIcc_of_le hab.le] at hx
            have hx0 : 0 < x := ha.trans_le hx.1
            simp only
            rw [zpow_neg, zpow_ofNat]
            field_simp
          · apply ContinuousOn.intervalIntegrable
            rw [uIcc_of_le hab.le]
            exact hcont.div (continuousOn_pow 3) fun x hx => by
              have := ha.trans_le hx.1; positivity
          · apply ContinuousOn.intervalIntegrable
            rw [uIcc_of_le hab.le]
            exact continuousOn_const.mul (continuousOn_id.zpow₀ (-3) fun x hx =>
              Or.inl (ha.trans_le hx.1).ne')
  -- the error term is at most ε/2
  have herr : 2 * L * δ * ((1 / a ^ 2 - 1 / b ^ 2) / 2) ≤ ε / 2 := by
    rw [hδ]
    have hr' : 2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) < r * ε := by
      rwa [div_lt_iff₀ hε] at hr
    rw [show 2 * L * ((b - a) / r) * ((1 / a ^ 2 - 1 / b ^ 2) / 2) =
      2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / r / 2 by field_simp]
    have : 2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / r ≤ ε := by
      rw [div_le_iff₀ (by exact_mod_cast hr0)]; linarith
    linarith
  have hev := psum_eventually_le (f := f) r (by rw [hc0]; exact ha) hmono hf (half_pos hε)
  rw [hc0, hcr] at hev
  filter_upwards [hev] with K hK
  linarith

/-- `K/k ∈ [a, b)` for `k ∈ Ioc ⌊K/b⌋₊ ⌊K/a⌋₊`. -/
lemma div_mem_Ico {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K) {k : ℕ}
    (hk : k ∈ Finset.Ioc ⌊K / b⌋₊ ⌊K / a⌋₊) : K / k ∈ Ico a b := by
  rw [Finset.mem_Ioc] at hk
  have hb : 0 < b := ha.trans_le hab
  have hk0 : 0 < k := by have := hk.1; omega
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  constructor
  · rw [le_div_iff₀ hk0']
    have h1 : (k : ℝ) ≤ K / a :=
      (Nat.floor_le (div_nonneg hK.le ha.le)).trans' (Nat.cast_le.mpr hk.2)
    rw [le_div_iff₀ ha] at h1
    linarith
  · rw [div_lt_iff₀ hk0']
    have h1 : K / b < k := by
      have := Nat.lt_floor_add_one (K / b)
      have h2 : (⌊K / b⌋₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk.1
      linarith
    rw [div_lt_iff₀ hb] at h1
    linarith

lemma psum_congr {f g : ℝ → ℝ} {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K)
    (h : ∀ x ∈ Ico a b, f x = g x) : psum f a b K = psum g a b K := by
  unfold psum
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h _ (div_mem_Ico ha hab hK hk)]

lemma psum_sum_split (f : ℝ → ℝ) {t : ℕ → ℝ} (m : ℕ) (ht0 : 0 < t 0)
    (hmono : ∀ i < m, t i ≤ t (i + 1)) {K : ℝ} (hK : 0 ≤ K) :
    psum f (t 0) (t m) K = ∑ i ∈ range m, psum f (t i) (t (i + 1)) K := by
  induction m with
  | zero => simp [psum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih fun i hi => hmono i (by omega)]
    exact psum_split f ht0 (c_zero_le fun i hi => hmono i (by omega)) (hmono m (by omega)) hK

/-- The piecewise version: `f = g i` on `[t i, t (i+1))`, each `g i` Lipschitz on the closed
piece. -/
theorem psum_piecewise_le {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {t : ℕ → ℝ} {L : ℝ} (m : ℕ)
    (ht0 : 0 < t 0) (hmono : ∀ i < m, t i < t (i + 1)) (hL : 0 ≤ L)
    (hcont : ∀ i < m, ContinuousOn (g i) (Icc (t i) (t (i + 1))))
    (hLip : ∀ i < m, ∀ x ∈ Icc (t i) (t (i + 1)), ∀ y ∈ Icc (t i) (t (i + 1)),
      |g i x - g i y| ≤ L * |x - y|)
    (hfg : ∀ i < m, ∀ x ∈ Ico (t i) (t (i + 1)), f x = g i x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop, psum f (t 0) (t m) K / K ^ 2 ≤
      (∑ i ∈ range m, ∫ x in t i..t (i + 1), g i x / x ^ 3) + ε := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · filter_upwards [eventually_gt_atTop 0] with K hK
    simp [psum]; positivity
  have hpos : ∀ i ≤ m, 0 < t i := by
    intro i hi
    induction i with
    | zero => exact ht0
    | succ i ih => exact (ih (by omega)).trans (hmono i (by omega))
  have hε' : 0 < ε / m := by positivity
  have hev : ∀ i ∈ range m, ∀ᶠ K : ℝ in atTop,
      psum (g i) (t i) (t (i + 1)) K / K ^ 2 ≤
        (∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    exact psum_le_integral (hpos i hi.le) (hmono i hi) hL (hcont i hi) (hLip i hi) hε'
  filter_upwards [(Finset.eventually_all (range m)).mpr hev, eventually_gt_atTop 0] with K hK hK0
  rw [psum_sum_split f m ht0 (fun i hi => (hmono i hi).le) hK0.le, Finset.sum_div]
  have hcongr : ∀ i ∈ range m, psum f (t i) (t (i + 1)) K / K ^ 2 =
      psum (g i) (t i) (t (i + 1)) K / K ^ 2 := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    rw [psum_congr (hpos i hi.le) (hmono i hi).le hK0 (hfg i hi)]
  rw [Finset.sum_congr rfl hcongr]
  calc ∑ i ∈ range m, psum (g i) (t i) (t (i + 1)) K / K ^ 2
      ≤ ∑ i ∈ range m, ((∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m) :=
        Finset.sum_le_sum fun i hi => hK i hi
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

lemma psum_mono {f g : ℝ → ℝ} {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K)
    (h : ∀ x ∈ Ico a b, f x ≤ g x) : psum f a b K ≤ psum g a b K := by
  unfold psum
  refine Finset.sum_le_sum fun k hk => ?_
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * cPrime k := mul_nonneg (Nat.cast_nonneg _) (cPrime_nonneg k)
  exact mul_le_mul_of_nonneg_left (h _ (div_mem_Ico ha hab hK hk)) hk0

/-- The piecewise version with `f ≤ g i` on the pieces. -/
theorem psum_piecewise_le' {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {t : ℕ → ℝ} {L : ℝ} (m : ℕ)
    (ht0 : 0 < t 0) (hmono : ∀ i < m, t i < t (i + 1)) (hL : 0 ≤ L)
    (hcont : ∀ i < m, ContinuousOn (g i) (Icc (t i) (t (i + 1))))
    (hLip : ∀ i < m, ∀ x ∈ Icc (t i) (t (i + 1)), ∀ y ∈ Icc (t i) (t (i + 1)),
      |g i x - g i y| ≤ L * |x - y|)
    (hfg : ∀ i < m, ∀ x ∈ Ico (t i) (t (i + 1)), f x ≤ g i x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop, psum f (t 0) (t m) K / K ^ 2 ≤
      (∑ i ∈ range m, ∫ x in t i..t (i + 1), g i x / x ^ 3) + ε := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · filter_upwards [eventually_gt_atTop 0] with K hK
    simp [psum]; positivity
  have hpos : ∀ i ≤ m, 0 < t i := by
    intro i hi
    induction i with
    | zero => exact ht0
    | succ i ih => exact (ih (by omega)).trans (hmono i (by omega))
  have hε' : 0 < ε / m := by positivity
  have hev : ∀ i ∈ range m, ∀ᶠ K : ℝ in atTop,
      psum (g i) (t i) (t (i + 1)) K / K ^ 2 ≤
        (∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    exact psum_le_integral (hpos i hi.le) (hmono i hi) hL (hcont i hi) (hLip i hi) hε'
  filter_upwards [(Finset.eventually_all (range m)).mpr hev, eventually_gt_atTop 0] with K hK hK0
  rw [psum_sum_split f m ht0 (fun i hi => (hmono i hi).le) hK0.le, Finset.sum_div]
  have hK2 : 0 < K ^ 2 := by positivity
  calc ∑ i ∈ range m, psum f (t i) (t (i + 1)) K / K ^ 2
      ≤ ∑ i ∈ range m, psum (g i) (t i) (t (i + 1)) K / K ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi := Finset.mem_range.mp hi
        exact div_le_div_of_nonneg_right
          (psum_mono (hpos i hi.le) (hmono i hi).le hK0 (hfg i hi)) hK2.le
    _ ≤ ∑ i ∈ range m, ((∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m) :=
        Finset.sum_le_sum fun i hi => hK i hi
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp


/-! ## The tail integral (`Apery/Growth/TailIntegral.lean`) -/

/-!
# The tail integral `∫_{20}^{400} (x F(x) + 27/16)/x³ dx`

On the grid `t_i = 20 + i/3` (`i ≤ 1140`) the fractional parts `{x}` and `{3x/40}` are affine on
each piece. With `P = 74 g(1-g) - λ f(1-f)` and `C = (74/α) G₀(g) - λ G₀(f)`,
`G₀(v) = v(1-v)(2v-1)/6`, we have `P' = F + λ` and `C' = P - P̄` on each piece, and `P`, `C` are
continuous across the breakpoints. Two integrations by parts on each piece and telescoping give
`∑_i ∫_{t_i}^{t_{i+1}} (x F + 27/16)/x³ ≤ tailBound`.
-/

open Finset intervalIntegral


/-- The grid. -/
noncomputable def tT (i : ℕ) : ℝ := 20 + i / 3
def qT (i : ℕ) : ℕ := (60 + i) / 3
def qT' (i : ℕ) : ℕ := (60 + i) / 40

/-- `F` on the piece `i`. -/
noncomputable def FT (i : ℕ) (x : ℝ) : ℝ :=
  37 / 10 + 37 / 20 * (x - qT i) - 111 / 10 * (3 / 40 * x - qT' i)
noncomputable def gT (i : ℕ) (x : ℝ) : ℝ := x * FT i x + 27 / 16
noncomputable def PT (i : ℕ) (x : ℝ) : ℝ :=
  74 * ((3 / 40 * x - qT' i) * (1 - (3 / 40 * x - qT' i))) - 37 / 40 * ((x - qT i) * (1 - (x - qT i)))
noncomputable def G0 (v : ℝ) : ℝ := v * (1 - v) * (2 * v - 1) / 6
noncomputable def CT (i : ℕ) (x : ℝ) : ℝ :=
  74 * 40 / 3 * G0 (3 / 40 * x - qT' i) - 37 / 40 * G0 (x - qT i)

/-- `P̄ = (74 - λ)/6`. -/
noncomputable def Pbar : ℝ := 2923 / 240

/-! ### The pieces -/

lemma tT_succ (i : ℕ) : tT (i + 1) = tT i + 1 / 3 := by unfold tT; push_cast; ring

lemma qT_le (i : ℕ) : (qT i : ℝ) ≤ tT i := by
  unfold qT tT
  have h := Nat.div_mul_le_self (60 + i) 3
  have : ((60 + i) / 3 : ℕ) * (3 : ℝ) ≤ 60 + i := by exact_mod_cast h
  linarith

lemma tT_succ_le (i : ℕ) : tT (i + 1) ≤ qT i + 1 := by
  unfold qT tT
  have h := Nat.lt_div_mul_add (a := 60 + i) (show 0 < 3 by norm_num)
  have : ((60 + i : ℕ) : ℝ) + 1 ≤ ((60 + i) / 3 : ℕ) * 3 + 3 := by exact_mod_cast (by omega : 60 + i + 1 ≤ (60 + i) / 3 * 3 + 3)
  push_cast at this ⊢
  linarith

lemma qT'_le (i : ℕ) : (qT' i : ℝ) ≤ 3 / 40 * tT i := by
  unfold qT' tT
  have h := Nat.div_mul_le_self (60 + i) 40
  have : ((60 + i) / 40 : ℕ) * (40 : ℝ) ≤ 60 + i := by exact_mod_cast h
  linarith

lemma tT_succ_le' (i : ℕ) : 3 / 40 * tT (i + 1) ≤ qT' i + 1 := by
  unfold qT' tT
  have : ((60 + i : ℕ) : ℝ) + 1 ≤ ((60 + i) / 40 : ℕ) * 40 + 40 := by
    exact_mod_cast (by omega : 60 + i + 1 ≤ (60 + i) / 40 * 40 + 40)
  push_cast at this ⊢
  linarith

lemma tT_pos (i : ℕ) : 20 ≤ tT i := by
  unfold tT; have : (0 : ℝ) ≤ (i : ℝ) / 3 := by positivity
  linarith

/-- On the closed piece the local coordinates lie in `[0, 1]`. -/
lemma piece_coords {i : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (tT i) (tT (i + 1))) :
    0 ≤ x - qT i ∧ x - qT i ≤ 1 ∧ 0 ≤ 3 / 40 * x - qT' i ∧ 3 / 40 * x - qT' i ≤ 1 := by
  have h1 := qT_le i; have h2 := tT_succ_le i; have h3 := qT'_le i; have h4 := tT_succ_le' i
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Derivatives -/

lemma hasDerivAt_PT (i : ℕ) (x : ℝ) : HasDerivAt (PT i) (FT i x + 37 / 40) x := by
  have : HasDerivAt (PT i) (74 * ((3 / 40) * (1 - (3 / 40 * x - qT' i)) + (3 / 40 * x - qT' i) * (-(3 / 40))) -
      37 / 40 * (1 * (1 - (x - qT i)) + (x - qT i) * (-1))) x := by
    unfold PT
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · simpa using ((hasDerivAt_id x).const_mul (3 / 40)).sub_const (qT' i : ℝ)
      · simpa using (((hasDerivAt_id x).const_mul (3 / 40)).sub_const (qT' i : ℝ)).const_sub 1
    · apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · simpa using (hasDerivAt_id x).sub_const (qT i : ℝ)
      · simpa using ((hasDerivAt_id x).sub_const (qT i : ℝ)).const_sub 1
  convert this using 1
  unfold FT; ring

lemma hasDerivAt_G0 (v : ℝ) : HasDerivAt G0 (v * (1 - v) - 1 / 6) v := by
  have : HasDerivAt G0 ((-6 * v ^ 2 + 6 * v - 1) / 6) v := by
    have e : G0 = fun v => (-2 * v ^ 3 + 3 * v ^ 2 - v) / 6 := by
      funext v; unfold G0; ring
    rw [e]
    have := ((((hasDerivAt_pow 3 v).const_mul (-2)).add ((hasDerivAt_pow 2 v).const_mul 3)).sub
      (hasDerivAt_id v)).div_const 6
    exact this.congr_deriv (by norm_num; ring)
  exact this.congr_deriv (by ring)

lemma hasDerivAt_CT (i : ℕ) (x : ℝ) : HasDerivAt (CT i) (PT i x - Pbar) x := by
  have h1 := (hasDerivAt_G0 (3 / 40 * x - qT' i)).comp x
    (((hasDerivAt_id x).const_mul (3 / 40)).sub_const (qT' i : ℝ))
  have h2 := (hasDerivAt_G0 (x - qT i)).comp x ((hasDerivAt_id x).sub_const (qT i : ℝ))
  have := (h1.const_mul (74 * 40 / 3)).sub (h2.const_mul (37 / 40))
  have e : CT i = (fun y => 74 * 40 / 3 * (G0 ∘ fun x => 3 / 40 * id x - (qT' i : ℝ)) y) -
      fun y => 37 / 40 * (G0 ∘ fun x => id x - (qT i : ℝ)) y := by
    funext y; simp [CT, Function.comp]
  rw [e]
  exact this.congr_deriv (by unfold PT Pbar; ring)

/-! ### Continuity across breakpoints -/

lemma step3 (i : ℕ) : (qT (i + 1) : ℝ) = qT i ∨ ((qT (i + 1) : ℝ) = qT i + 1 ∧ tT (i + 1) = qT (i + 1)) := by
  unfold qT tT
  rcases (show (60 + (i + 1)) / 3 = (60 + i) / 3 ∨ ((60 + (i + 1)) / 3 = (60 + i) / 3 + 1 ∧
      60 + (i + 1) = 3 * ((60 + (i + 1)) / 3)) by omega) with h | ⟨h1, h2⟩
  · left; rw [h]
  · right
    refine ⟨by rw [h1]; push_cast; ring, ?_⟩
    have : ((60 + (i + 1) : ℕ) : ℝ) = 3 * (((60 + (i + 1)) / 3 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this ⊢; linarith

lemma step40 (i : ℕ) : (qT' (i + 1) : ℝ) = qT' i ∨
    ((qT' (i + 1) : ℝ) = qT' i + 1 ∧ 3 / 40 * tT (i + 1) = qT' (i + 1)) := by
  unfold qT' tT
  rcases (show (60 + (i + 1)) / 40 = (60 + i) / 40 ∨ ((60 + (i + 1)) / 40 = (60 + i) / 40 + 1 ∧
      60 + (i + 1) = 40 * ((60 + (i + 1)) / 40)) by omega) with h | ⟨h1, h2⟩
  · left; rw [h]
  · right
    refine ⟨by rw [h1]; push_cast; ring, ?_⟩
    have : ((60 + (i + 1) : ℕ) : ℝ) = 40 * (((60 + (i + 1)) / 40 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this ⊢; linarith

lemma PT_cont (i : ℕ) : PT i (tT (i + 1)) = PT (i + 1) (tT (i + 1)) := by
  unfold PT
  rcases step3 i with h3 | ⟨h3, e3⟩ <;> rcases step40 i with h4 | ⟨h4, e4⟩
  · rw [h3, h4]
  · rw [h3]; rw [h4] at e4 ⊢; rw [e4]; ring
  · rw [h4]; rw [h3] at e3 ⊢; rw [e3]; ring
  · rw [h3] at e3 ⊢; rw [h4] at e4 ⊢; rw [e3] at e4 ⊢; rw [e4]; ring

lemma CT_cont (i : ℕ) : CT i (tT (i + 1)) = CT (i + 1) (tT (i + 1)) := by
  unfold CT G0
  rcases step3 i with h3 | ⟨h3, e3⟩ <;> rcases step40 i with h4 | ⟨h4, e4⟩
  · rw [h3, h4]
  · rw [h3]; rw [h4] at e4 ⊢; rw [e4]; ring
  · rw [h4]; rw [h3] at e3 ⊢; rw [e3]; ring
  · rw [h3] at e3 ⊢; rw [h4] at e4 ⊢; rw [e3] at e4 ⊢; rw [e4]; ring

/-! ### The antiderivative on a piece -/

/-- `Φ_i(x) = P/x² + 2C/x³ - P̄/x² + λ/x - (27/32)/x²`. -/
noncomputable def PhiT (i : ℕ) (x : ℝ) : ℝ :=
  PT i x / x ^ 2 + 2 * CT i x / x ^ 3 - Pbar / x ^ 2 + 37 / 40 / x - 27 / 32 / x ^ 2

lemma hasDerivAt_PhiT (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (PhiT i) (gT i x / x ^ 3 - 6 * CT i x / x ^ 4) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
  have d1 := (hasDerivAt_PT i x).div h2 (pow_ne_zero 2 hx0)
  have d2 := ((hasDerivAt_CT i x).const_mul 2).div h3 (pow_ne_zero 3 hx0)
  have d3 := (hasDerivAt_const x Pbar).div h2 (pow_ne_zero 2 hx0)
  have d4 := (hasDerivAt_const x (37 / 40 : ℝ)).div (hasDerivAt_id x) hx0
  have d5 := (hasDerivAt_const x (27 / 32 : ℝ)).div h2 (pow_ne_zero 2 hx0)
  have := (((d1.add d2).sub d3).add d4).sub d5
  have e : PhiT i = (((fun y => PT i y / y ^ 2) + fun y => 2 * CT i y / y ^ 3) - fun y => Pbar / y ^ 2) +
      (fun y => 37 / 40 / id y) - fun y => 27 / 32 / y ^ 2 := by
    funext y; simp [PhiT]
  rw [e]
  refine this.congr_deriv ?_
  simp only [id]
  unfold gT FT PT
  field_simp
  ring

lemma continuous_gT (i : ℕ) : Continuous (gT i) := by unfold gT FT; fun_prop
lemma continuous_CT (i : ℕ) : Continuous (CT i) := by unfold CT G0; fun_prop

lemma continuousOn_div_pow {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun x => f x / x ^ k) (Set.uIcc a b) := by
  apply ContinuousOn.div hf.continuousOn (continuous_pow k).continuousOn
  intro x hx
  have : 0 < x := by
    rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  positivity

lemma abs_G0_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : |G0 v| ≤ 1 / 60 := by
  unfold G0
  set w := v * (1 - v) with hw
  have hw0 : 0 ≤ w := mul_nonneg h0 (sub_nonneg.mpr h1)
  have e : (v * (1 - v) * (2 * v - 1)) ^ 2 = w ^ 2 * (1 - 4 * w) := by rw [hw]; ring
  have hfac : w ^ 2 * (1 - 4 * w) - 1 / 108 = -((w - 1 / 6) ^ 2 * (4 * w + 1 / 3)) := by ring
  have h2 : (v * (1 - v) * (2 * v - 1)) ^ 2 ≤ 1 / 100 := by
    rw [e]
    have : 0 ≤ (w - 1 / 6) ^ 2 * (4 * w + 1 / 3) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  rw [abs_le]
  constructor <;> nlinarith [h2]

lemma abs_CT_le {i : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (tT i) (tT (i + 1))) : |CT i x| ≤ 17 := by
  obtain ⟨h1, h2, h3, h4⟩ := piece_coords hx
  have a1 := abs_G0_le h3 h4
  have a2 := abs_G0_le h1 h2
  unfold CT
  rw [abs_le] at a1 a2 ⊢
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]

/-- **One piece.** -/
lemma piece_bound (i : ℕ) :
    ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 ≤
      PhiT i (tT (i + 1)) - PhiT i (tT i) + 34 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) := by
  have ha := tT_pos i
  have hb := tT_pos (i + 1)
  have hab : tT i ≤ tT (i + 1) := by rw [tT_succ]; linarith
  have ha0 : (0 : ℝ) < tT i := by linarith
  have hb0 : (0 : ℝ) < tT (i + 1) := by linarith
  have hpos : ∀ x ∈ Set.uIcc (tT i) (tT (i + 1)), 0 < x := by
    intro x hx; rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  have hint1 : IntervalIntegrable (fun x => gT i x / x ^ 3) MeasureTheory.volume (tT i) (tT (i + 1)) :=
    (continuousOn_div_pow (continuous_gT i) 3 ha0 hb0).intervalIntegrable
  have hint2 : IntervalIntegrable (fun x => CT i x / x ^ 4) MeasureTheory.volume (tT i) (tT (i + 1)) :=
    (continuousOn_div_pow (continuous_CT i) 4 ha0 hb0).intervalIntegrable
  have hftc : ∫ x in tT i..tT (i + 1), (gT i x / x ^ 3 - 6 * CT i x / x ^ 4) =
      PhiT i (tT (i + 1)) - PhiT i (tT i) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x hx; exact hasDerivAt_PhiT i (hpos x hx)
    · have : (fun x => gT i x / x ^ 3 - 6 * CT i x / x ^ 4) =
          fun x => gT i x / x ^ 3 - 6 * (CT i x / x ^ 4) := by funext x; ring
      rw [this]; exact hint1.sub (hint2.const_mul 6)
  have hA : IntervalIntegrable (fun x => gT i x / x ^ 3 - 6 * CT i x / x ^ 4) MeasureTheory.volume
      (tT i) (tT (i + 1)) := by
    have : (fun x => gT i x / x ^ 3 - 6 * CT i x / x ^ 4) =
        fun x => gT i x / x ^ 3 - 6 * (CT i x / x ^ 4) := by funext x; ring
    rw [this]; exact hint1.sub (hint2.const_mul 6)
  have hsplit : ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 =
      (∫ x in tT i..tT (i + 1), (gT i x / x ^ 3 - 6 * CT i x / x ^ 4)) +
        6 * ∫ x in tT i..tT (i + 1), CT i x / x ^ 4 := by
    have e1 : ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 =
        ∫ x in tT i..tT (i + 1), ((gT i x / x ^ 3 - 6 * CT i x / x ^ 4) + 6 * (CT i x / x ^ 4)) := by
      congr 1; funext x; ring
    rw [e1, intervalIntegral.integral_add hA (hint2.const_mul 6), intervalIntegral.integral_const_mul]
  -- the bound on `∫ C/x⁴`
  have hC : ∫ x in tT i..tT (i + 1), CT i x / x ^ 4 ≤ 17 / 3 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) := by
    have hmono : ∫ x in tT i..tT (i + 1), CT i x / x ^ 4 ≤ ∫ x in tT i..tT (i + 1), 17 / x ^ 4 := by
      apply intervalIntegral.integral_mono_on hab hint2
      · exact (continuousOn_div_pow continuous_const 4 ha0 hb0).intervalIntegrable
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have := abs_CT_le hx
        rw [abs_le] at this
        exact div_le_div_of_nonneg_right this.2 (by positivity)
    have hval : ∫ x in tT i..tT (i + 1), 17 / x ^ 4 = 17 / 3 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) := by
      rw [integral_eq_sub_of_hasDerivAt (f := fun x => -(17 / 3) / x ^ 3)]
      · field_simp; ring
      · intro x hx
        have hx0 := hpos x hx
        have := ((hasDerivAt_const x (-(17 / 3) : ℝ)).div (hasDerivAt_pow 3 x)
          (pow_ne_zero 3 hx0.ne'))
        refine this.congr_deriv ?_
        norm_num
        field_simp
      · exact (continuousOn_div_pow continuous_const 4 ha0 hb0).intervalIntegrable
    linarith
  rw [hsplit, hftc]
  linarith

lemma PhiT_cont (i : ℕ) : PhiT i (tT (i + 1)) = PhiT (i + 1) (tT (i + 1)) := by
  unfold PhiT; rw [PT_cont, CT_cont]

lemma tele_phi (N : ℕ) : ∑ i ∈ range N, (PhiT i (tT (i + 1)) - PhiT i (tT i)) =
    PhiT N (tT N) - PhiT 0 (tT 0) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, PhiT_cont]; ring

lemma tele_cube (N : ℕ) : ∑ i ∈ range N, 34 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) =
    34 * (1 / tT 0 ^ 3 - 1 / tT N ^ 3) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- **The tail sum**: `∑_i ∫_{t_i}^{t_{i+1}} g_i/x³ ≤ -6843153/128000000 ≈ -0.05346`. -/
theorem tail_sum_le :
    ∑ i ∈ range 1140, ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 ≤ -6843153 / 128000000 := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ range 1140) => piece_bound i
  have tele1 := tele_phi 1140
  have tele2 := tele_cube 1140
  rw [Finset.sum_add_distrib, tele1, tele2] at h
  refine h.trans (le_of_eq ?_)
  have e0 : tT 0 = 20 := by unfold tT; norm_num
  have e1 : tT 1140 = 400 := by unfold tT; norm_num
  have q0 : qT 0 = 20 := by decide
  have q0' : qT' 0 = 1 := by decide
  have q1 : qT 1140 = 400 := by decide
  have q1' : qT' 1140 = 30 := by decide
  rw [e0, e1]
  unfold PhiT PT CT G0 Pbar
  rw [q0, q0', q1, q1']
  norm_num


/-! ## The tail prime-sum limit (`Apery/Growth/Assembly4.lean`) -/

lemma nat_floor_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : ⌊x⌋₊ = q := by
  rw [Nat.floor_eq_iff (by linarith)]; exact ⟨h1, h2⟩

lemma fract_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : Int.fract x = x - q := by
  rw [Int.fract, show ⌊x⌋ = (q : ℤ) by rw [Int.floor_eq_iff]; push_cast; exact ⟨h1, h2⟩]
  push_cast; ring

lemma tT_zero : tT 0 = 20 := by unfold tT; norm_num
lemma tT_last : tT 1140 = 400 := by unfold tT; norm_num

lemma qT_le_400 {i : ℕ} (hi : i < 1140) : (qT i : ℝ) ≤ 400 := by
  unfold qT; exact_mod_cast (show (60 + i) / 3 ≤ 400 by omega)
lemma qT'_le_30 {i : ℕ} (hi : i < 1140) : (qT' i : ℝ) ≤ 30 := by
  unfold qT'; exact_mod_cast (show (60 + i) / 40 ≤ 30 by omega)

lemma tT_le_400 {i : ℕ} (hi : i ≤ 1140) : tT i ≤ 400 := by
  unfold tT; have : (i : ℝ) ≤ 1140 := by exact_mod_cast hi
  linarith

/-- **The tail sum.** -/
lemma tail_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, psum (fun x => x * Ftail x + 27 / 16) 20 400 K / K ^ 2 ≤
      -6843153 / 128000000 + δ := by
  have h := psum_piecewise_le (f := fun x => x * Ftail x + 27 / 16) (g := gT) (t := tT) (L := 3000)
    1140 (by rw [tT_zero]; norm_num) (fun i _ => by rw [tT_succ]; linarith) (by norm_num)
    (fun i _ => (continuous_gT i).continuousOn)
    (fun i hi x hx y hy => by
      have hx0 : 0 ≤ x := by linarith [hx.1, tT_pos i]
      have hy0 : 0 ≤ y := by linarith [hy.1, tT_pos i]
      have hx4 : x ≤ 400 := hx.2.trans (tT_le_400 (by omega))
      have hy4 : y ≤ 400 := hy.2.trans (tT_le_400 (by omega))
      have hq := qT_le_400 hi
      have hq' := qT'_le_30 hi
      have hq0 : (0 : ℝ) ≤ qT i := by positivity
      have hq0' : (0 : ℝ) ≤ qT' i := by positivity
      have e : gT i x - gT i y = (x - y) * (37 / 10 - 37 / 20 * (qT i : ℝ) + 111 / 10 * (qT' i : ℝ) +
          407 / 400 * (x + y)) := by unfold gT FT; ring
      rw [e, abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [abs_le]; constructor <;> nlinarith)
    (fun i hi x hx => by
      obtain ⟨hx1, hx2⟩ := hx
      have h1 := qT_le i; have h2 := tT_succ_le i; have h3 := qT'_le i; have h4 := tT_succ_le' i
      have hf : Int.fract x = x - qT i := fract_of_bounds (by linarith) (by linarith)
      have hg : Int.fract (3 / 40 * x) = 3 / 40 * x - qT' i := fract_of_bounds (by linarith) (by linarith)
      unfold gT FT Ftail
      rw [hf, hg]; ring) hδ
  have hsum := tail_sum_le
  rw [tT_zero, tT_last] at h
  filter_upwards [h] with K hK
  linarith

end Apery
end Port0


open Finset Filter in
/-- The platform target `Apery.tail_psum_limit`, restated at top level as `solution`. -/
theorem solution {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop,
      Apery.psum (fun x => x * Apery.Ftail x + 27 / 16) 20 400 K / K ^ 2 ≤
        -6843153 / 128000000 + δ :=
  Apery.tail_psum_limit hδ
