-- Prove2me | solution 1 for Apery.inner_psum_limit
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T17:49:43.136644+00:00
-- url     : https://prove2.me/submissions/12966392-50b7-408b-a12c-1ec985048ac7

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The inner table sum (source `Apery/Growth/Assembly4.lean`)

This file proves the platform theorem `Apery.inner_psum_limit`:

$$\frac{1}{K^2}\sum_{K/20 < p \le K/3} p\,F_{\mathrm{in}}\Bigl(\frac{K}{p}\Bigr)\log p
\;\le\; \frac{322437603634266857629}{7535670527041937280000} + \delta \quad (K \to \infty),$$

from the numerical evaluation `Apery.inner_integrals`, the piece locator (with
`pieceIdx_eq` and `tIn_mono`), the slope bound `aIn_le`, the Abel-summation machinery of
`Apery/PrimeSum*.lean` (with the platform's proved prime number theorem
`Apery.theta_eventually_close`) and the assembly in `Apery/Growth/Assembly4.lean`. A faithful
port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePrimeSum
import Theorems.Thm_Apery_theta_eventually_close
import Theorems.Thm_Apery_inner_integrals

set_option autoImplicit false

section Port0
/-!
# The inner table sum (source `Apery/Growth/Assembly4.lean`)

This file proves the platform theorem `Apery.inner_psum_limit`:

`psum fIn 3 20 K / K² ≤ 322437603634266857629 / 7535670527041937280000 + δ` eventually,

from the numerical evaluation `Apery.inner_integrals` of the 125-piece table, the piece
locator `pieceIdx` (with `pieceIdx_eq` and strict monotonicity `tIn_mono` of the grid), the
fact that all table slopes satisfy `|a_i| ≤ 100` (`aIn_le`), the Abel-summation machinery of
`Apery/PrimeSum*.lean` (with the platform's proved prime number theorem
`Apery.theta_eventually_close`) and the assembly in `Apery/Growth/Assembly4.lean`. A faithful
port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

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

/-! ## Locating a point in the inner partition (`Apery/Growth/PieceIdx.lean`) -/

lemma grid_mono {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    t i ≤ t j := by
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · exact (ih (by omega) (by omega)).trans (h j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

lemma pieceIdx_spec {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {x : ℝ}
    (h0 : t 0 ≤ x) (hm : x < t m) :
    pieceIdx t m x < m ∧ t (pieceIdx t m x) ≤ x ∧ x < t (pieceIdx t m x + 1) := by
  classical
  unfold pieceIdx
  set i := Nat.findGreatest (fun i => t i ≤ x) m with hi
  have hspec : t i ≤ x := Nat.findGreatest_spec (P := fun i => t i ≤ x) (Nat.zero_le m) h0
  have hle : i ≤ m := Nat.findGreatest_le m
  have hlt : i < m := by
    rcases Nat.lt_or_ge i m with h1 | h1
    · exact h1
    · have : i = m := by omega
      rw [this] at hspec; linarith
  refine ⟨hlt, hspec, ?_⟩
  by_contra hc
  rw [not_lt] at hc
  have := Nat.findGreatest_is_greatest (P := fun i => t i ≤ x) (n := m) (k := i + 1) (by omega)
    (by omega)
  exact this hc

lemma pieceIdx_eq {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {i : ℕ} (hi : i < m) {x : ℝ}
    (hx : x ∈ Set.Ico (t i) (t (i + 1))) : pieceIdx t m x = i := by
  classical
  unfold pieceIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hi.le, fun _ => hx.1, fun j hj1 hj2 => ?_⟩
  have := grid_mono h (show i + 1 ≤ j by omega) hj2
  exact not_le.mpr (lt_of_lt_of_le hx.2 this)


/-! ## The inner grid (`Apery/Growth/InnerSum.lean`) -/

theorem tIn_mono : ∀ i < 125, tIn i < tIn (i + 1) := by
  intro i hi
  interval_cases i <;> simp only [tIn, tInL, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
lemma tIn_zero : tIn 0 = 3 := by simp [tIn, tInL]
lemma tIn_last : tIn 125 = 20 := by simp [tIn, tInL]


/-! ## The inner table sum (`Apery/Growth/Assembly4.lean`) -/

lemma aIn_le : ∀ i < 125, |((aInL.getD i 0 : ℚ) : ℝ)| ≤ 100 := by
  intro i hi
  interval_cases i <;> simp only [aInL, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num [abs_le]

lemma lin_lip (a b : ℝ) (L : ℝ) (ha : |a| ≤ L) (x y : ℝ) :
    |(a * x + b) - (a * y + b)| ≤ L * |x - y| := by
  rw [show (a * x + b) - (a * y + b) = a * (x - y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)

lemma inner_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, psum fIn 3 20 K / K ^ 2 ≤
      322437603634266857629 / 7535670527041937280000 + δ := by
  have h := psum_piecewise_le (f := fIn) (g := gIn) (t := tIn) (L := 100) 125
    (by rw [tIn_zero]; norm_num) tIn_mono (by norm_num)
    (fun i _ => by unfold gIn; fun_prop)
    (fun i hi x _ y _ => by unfold gIn; exact lin_lip _ _ _ (aIn_le i hi) x y)
    (fun i hi x hx => by unfold fIn; rw [pieceIdx_eq tIn_mono hi hx]) hδ
  rw [tIn_zero, tIn_last, inner_integrals] at h
  exact h

end Apery

#check @Apery.inner_psum_limit
end Port0


open Finset Filter in
/-- The platform target `Apery.inner_psum_limit`, restated at top level as `solution`. -/
theorem solution {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, Apery.psum Apery.fIn 3 20 K / K ^ 2 ≤
      322437603634266857629 / 7535670527041937280000 + δ :=
  Apery.inner_psum_limit hδ
