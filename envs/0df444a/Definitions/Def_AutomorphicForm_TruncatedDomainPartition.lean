-- Prove2me | Definitions.Def_AutomorphicForm_TruncatedDomainPartition
-- name    : AutomorphicForm_TruncatedDomainPartition
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0ef3ebf5-b1fa-574c-a7c4-ae7b8a10cf37
-- title:
--   Cusp neighbourhood of the modular fundamental domain; unipotent kernel sums
-- statement:
--   Working in the standard fundamental domain $\mathcal D$ (Mathlib's `ModularGroup.fd`, i.e. $|z|\ge 1$, $|\mathrm{Re}\,z|\le 1/2$) for $\mathrm{SL}_2(\mathbb Z)$ acting on $\mathbb H$, with the hyperbolic measure `volume` on $\mathbb H$, the module introduces `cuspNeighbourhood T` $=\{z\in\mathcal D : T<\mathrm{Im}\,z\}$, the complement in $\mathcal D$ of the project's truncated domain `truncatedFundamentalDomain T` $=\{z\in\mathcal D:\mathrm{Im}\,z\le T\}$. The elementary lemmas record this: membership is by definition, `cuspNeighbourhood T` is the set difference, the two pieces are disjoint with union $\mathcal D$, both are measurable (the truncation being compact, hence closed, and $\mathcal D$ closed), and volumes add. Quantitatively, `cuspNeighbourhood T` lies in the vertical strip $\{|\mathrm{Re}\,z|\le 1/2,\ T\le \mathrm{Im}\,z\}$; a dyadic-band decomposition plus a geometric series gives $\mathrm{vol}(\text{strip }A,a)\le 4A/a$ for $0\le A$, $0<a$, hence $\mathrm{vol}(\text{cusp neighbourhood})\le 2/T$ for $T>0$, finiteness, and convergence to $0$ as $T\to\infty$; conversely the cusp neighbourhood has positive volume for every real $T$, via an explicit nonempty open box inside it.
--
--   The second half concerns kernels $k:\mathbb H\times\mathbb H\to[0,\infty]$. For such $k$, `unipotentDiagonalSum k z` $=\sum_{n\in\mathbb Z\setminus\{0\}}k(z,\,n+z)$ is the sum of $k$ over the nontrivial integer horizontal translates of $z$. Two complementary results are proved. If there are $\delta\ne 0$ and $c>0$ with $k(z,n+z)\ge\delta$ whenever $n\ne0$ and $|n|\le c\,\mathrm{Im}\,z$, then $\int_{\mathcal D}^-\!\!\text{(unipotent sum)}=\infty$; the proof uses auxiliary dyadic bands $\{|\mathrm{Re}\,z|<1/2,\ Y_02^j<\mathrm{Im}\,z<Y_02^{j+1}\}$, open, pairwise disjoint, contained in $\mathcal D$, with hyperbolic volume bounded below. If instead $k\le M<\infty$ uniformly and $k(z,n+z)=0$ whenever $c\,\mathrm{Im}\,z<|n|$, then the integral over every truncation is finite. The kernel `windowIndicator` $(z,w)\mapsto \mathbf 1\{|\mathrm{Re}\,w-\mathrm{Re}\,z|\le \mathrm{Im}\,z\}$ satisfies both hypotheses with $c=1$, so `sat_windowIndicator` exhibits a kernel whose unipotent sum is non-integrable on $\mathcal D$ but integrable on each truncation; the zero kernel gives the trivial opposite example.
--
--   **Relation to Mathlib.** The fundamental domain $\mathcal D$, its closedness and compactness statements, the vertical strips, and the hyperbolic measure on $\mathbb H$ come from Mathlib; the cusp neighbourhood, the height truncation of $\mathcal D$ and the unipotent translation sum of a kernel are the project's own notions, Mathlib having no truncation operator or trace-formula kernels.
--
--   **Where it is used.** These are measure-theoretic preliminaries for the analytic side of the automorphic theory: the decomposition $\mathcal D=\{\mathrm{Im}\,z\le T\}\sqcup\{\mathrm{Im}\,z>T\}$ with its volume estimates, and the contrast between divergence of the unipotent kernel sum over all of $\mathcal D$ and its integrability over each truncation, which is the reason truncation is imposed before integrating automorphic kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TruncatedDomainPartition.lean

import Mathlib
import Definitions.Def_AutomorphicForm_FundamentalDomainVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set ModularGroup UpperHalfPlane Filter
open scoped MatrixGroups Modular Pointwise NNReal ENNReal Topology

noncomputable section

namespace FLT.TruncatedDomainPartition

def cuspNeighbourhood (T : ℝ) : Set ℍ := {z | z ∈ 𝒟 ∧ T < z.im}

theorem mem_cuspNeighbourhood_iff {T : ℝ} {z : ℍ} :
    z ∈ cuspNeighbourhood T ↔ z ∈ 𝒟 ∧ T < z.im := Iff.rfl

theorem cuspNeighbourhood_eq_diff (T : ℝ) :
    cuspNeighbourhood T = 𝒟 \ truncatedFundamentalDomain T := by
  ext z
  simp only [cuspNeighbourhood, Set.mem_setOf_eq, Set.mem_diff, truncatedFundamentalDomain,
    not_and, not_le]
  exact ⟨fun ⟨h, h'⟩ => ⟨h, fun _ => h'⟩, fun ⟨h, h'⟩ => ⟨h, h' h⟩⟩

theorem truncated_union_cuspNeighbourhood (T : ℝ) :
    truncatedFundamentalDomain T ∪ cuspNeighbourhood T = 𝒟 := by
  ext z
  simp only [Set.mem_union, truncatedFundamentalDomain, Set.mem_setOf_eq, cuspNeighbourhood]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases le_or_gt z.im T with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

theorem disjoint_truncated_cuspNeighbourhood (T : ℝ) :
    Disjoint (truncatedFundamentalDomain T) (cuspNeighbourhood T) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hle⟩ ⟨-, hlt⟩
  exact absurd hle (not_le.mpr hlt)

theorem measurableSet_truncatedFundamentalDomain (T : ℝ) :
    MeasurableSet (truncatedFundamentalDomain T) :=
  (isCompact_truncatedFundamentalDomain T).isClosed.measurableSet

theorem measurableSet_fd : MeasurableSet 𝒟 :=
  ModularGroup.isClosed_fd.measurableSet

theorem measurableSet_cuspNeighbourhood (T : ℝ) :
    MeasurableSet (cuspNeighbourhood T) := by
  rw [cuspNeighbourhood_eq_diff]
  exact measurableSet_fd.diff (measurableSet_truncatedFundamentalDomain T)

theorem volume_fd_eq_add (T : ℝ) :
    volume 𝒟 =
      volume (truncatedFundamentalDomain T) + volume (cuspNeighbourhood T) := by
  rw [← truncated_union_cuspNeighbourhood T,
    measure_union (disjoint_truncated_cuspNeighbourhood T) (measurableSet_cuspNeighbourhood T)]

theorem cuspNeighbourhood_subset_verticalStrip (T : ℝ) :
    cuspNeighbourhood T ⊆ UpperHalfPlane.verticalStrip (1 / 2) T := by
  rintro z ⟨hz, hT⟩
  exact ⟨hz.2, hT.le⟩

theorem volume_verticalStrip_le {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) :
    volume (UpperHalfPlane.verticalStrip A a) ≤ ENNReal.ofReal (4 * A / a) := by
  calc volume (UpperHalfPlane.verticalStrip A a)
      ≤ volume (⋃ n : ℕ, FLT.FundamentalDomainVolume.band A a n) :=
        measure_mono (FLT.FundamentalDomainVolume.verticalStrip_subset_iUnion_band A ha)
    _ ≤ ∑' n : ℕ, volume (FLT.FundamentalDomainVolume.band A a n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) :=
        ENNReal.tsum_le_tsum fun n => FLT.FundamentalDomainVolume.volume_band_le hA ha n
    _ = ∑' n : ℕ, ENNReal.ofReal (2 * A * a⁻¹) * ENNReal.ofReal ((1 / 2) ^ n) :=
        tsum_congr fun n => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal ((1 / 2) ^ n) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal (1 / 2) ^ n :=
        congrArg _ (tsum_congr fun n => ENNReal.ofReal_pow (by norm_num) n)
    _ = ENNReal.ofReal (2 * A * a⁻¹) * (1 - ENNReal.ofReal (1 / 2))⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (2 * A * a⁻¹) * 2 := by
        congr 1
        rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
          ENNReal.one_sub_inv_two, inv_inv]
    _ = ENNReal.ofReal (4 * A / a) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by
            rw [ENNReal.ofReal_ofNat],
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

theorem volume_cuspNeighbourhood_le {T : ℝ} (hT : 0 < T) :
    volume (cuspNeighbourhood T) ≤ ENNReal.ofReal (2 / T) := by
  refine le_trans (measure_mono (cuspNeighbourhood_subset_verticalStrip T)) ?_
  refine le_trans (volume_verticalStrip_le (by norm_num) hT) ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

theorem volume_cuspNeighbourhood_lt_top {T : ℝ} (hT : 0 < T) :
    volume (cuspNeighbourhood T) < ⊤ :=
  lt_of_le_of_lt (volume_cuspNeighbourhood_le hT) ENNReal.ofReal_lt_top

theorem tendsto_volume_cuspNeighbourhood :
    Tendsto (fun T : ℝ => volume (cuspNeighbourhood T)) atTop (𝓝 0) := by
  have h2T : Tendsto (fun T : ℝ => ENNReal.ofReal (2 / T)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    refine ENNReal.tendsto_ofReal ?_
    have h := tendsto_inv_atTop_zero.const_mul (2 : ℝ)
    simp only [← div_eq_mul_inv, mul_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2T
    (Filter.Eventually.of_forall fun T => zero_le') ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  exact volume_cuspNeighbourhood_le hT

theorem volume_cuspNeighbourhood_pos (T : ℝ) :
    0 < volume (cuspNeighbourhood T) := by

  set U : Set ℍ := {z | |z.re| < 1 / 2 ∧ max T 1 < z.im} with hU
  have hUopen : IsOpen U := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
    · exact isOpen_lt continuous_const UpperHalfPlane.continuous_im
  have hmax : (1 : ℝ) ≤ max T 1 := le_max_right T 1
  have hUne : U.Nonempty := by
    refine ⟨UpperHalfPlane.mk ⟨0, max T 1 + 1⟩ (show (0 : ℝ) < max T 1 + 1 by linarith), ?_, ?_⟩
    · show |(UpperHalfPlane.mk ⟨0, max T 1 + 1⟩ _).re| < 1 / 2
      rw [UpperHalfPlane.mk_re]
      show |(0 : ℝ)| < 1 / 2
      norm_num
    · show max T 1 < (UpperHalfPlane.mk ⟨0, max T 1 + 1⟩ _).im
      rw [UpperHalfPlane.mk_im]
      show max T 1 < max T 1 + 1
      linarith
  have hUsub : U ⊆ cuspNeighbourhood T := by
    rintro z ⟨hre, him⟩
    have him1 : (1 : ℝ) < z.im := lt_of_le_of_lt (le_max_right T 1) him
    refine ⟨⟨?_, hre.le⟩, lt_of_le_of_lt (le_max_left T 1) him⟩

    have : (1 : ℝ) ≤ z.im ^ 2 := by nlinarith
    calc (1 : ℝ) ≤ z.im ^ 2 := this
      _ ≤ z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.re]
      _ = Complex.normSq (z : ℂ) := by
          rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  exact lt_of_lt_of_le (FLT.HyperbolicMeasure.volume_pos_of_isOpen hUopen hUne)
    (measure_mono hUsub)

def unipotentDiagonalSum (k : ℍ → ℍ → ℝ≥0∞) (z : ℍ) : ℝ≥0∞ :=
  ∑' n : ℤ, if n = 0 then 0 else k z ((n : ℝ) +ᵥ z)

@[simp] theorem unipotentDiagonalSum_zero (z : ℍ) :
    unipotentDiagonalSum (fun _ _ => 0) z = 0 := by
  simp [unipotentDiagonalSum]

private def divBand (Y₀ : ℝ) (j : ℕ) : Set ℍ :=
  {z | |z.re| < 1 / 2 ∧ Y₀ * 2 ^ j < z.im ∧ z.im < Y₀ * 2 ^ (j + 1)}

private lemma isOpen_divBand (Y₀ : ℝ) (j : ℕ) : IsOpen (divBand Y₀ j) := by
  refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
  · exact isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  · exact isOpen_lt continuous_const UpperHalfPlane.continuous_im
  · exact isOpen_lt UpperHalfPlane.continuous_im continuous_const

private lemma divBand_subset_fd {Y₀ : ℝ} (hY : 1 ≤ Y₀) (j : ℕ) : divBand Y₀ j ⊆ 𝒟 := by
  rintro z ⟨hre, hlo, -⟩
  have h1 : (1 : ℝ) < z.im := by
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  refine ⟨?_, hre.le⟩
  calc (1 : ℝ) ≤ z.im ^ 2 := by nlinarith
    _ ≤ z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.re]
    _ = Complex.normSq (z : ℂ) := by
        rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring

private lemma pairwise_disjoint_divBand {Y₀ : ℝ} (hY : 0 < Y₀) :
    Pairwise (Function.onFun Disjoint (divBand Y₀)) := by
  intro i j hij

  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (by omega)).symm
  rw [Function.onFun, Set.disjoint_left]
  rintro z ⟨-, -, hi⟩ ⟨-, hj, -⟩
  have hij' : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  nlinarith

private lemma volume_obox (relo rehi imlo imhi : ℝ) :
    volume (Complex.measurableEquivRealProd ⁻¹'
      (Set.Ioo relo rehi ×ˢ Set.Ioo imlo imhi)) =
      ENNReal.ofReal (rehi - relo) * ENNReal.ofReal (imhi - imlo) := by
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]

private lemma volume_divBand_ge {Y₀ : ℝ} (hY : 0 < Y₀) (j : ℕ) :
    ENNReal.ofReal ((Y₀ * 2 ^ j) * (Y₀ * 2 ^ (j + 1))⁻¹ ^ 2) ≤ volume (divBand Y₀ j) := by
  have htop : (0 : ℝ) < Y₀ * 2 ^ (j + 1) := by positivity

  have himg : (UpperHalfPlane.coe '' divBand Y₀ j) =
      Complex.measurableEquivRealProd ⁻¹'
        (Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ioo (Y₀ * 2 ^ j) (Y₀ * 2 ^ (j + 1))) := by
    ext w
    simp only [Set.mem_image, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod, Set.mem_Ioo, divBand, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, ⟨hre, hlo, hhi⟩, rfl⟩
      rw [abs_lt] at hre
      exact ⟨⟨hre.1, hre.2⟩, hlo, hhi⟩
    · rintro ⟨⟨hre1, hre2⟩, hlo, hhi⟩
      have hwim : 0 < w.im := lt_trans (by positivity) hlo
      exact ⟨⟨w, hwim⟩, ⟨abs_lt.mpr ⟨hre1, hre2⟩, hlo, hhi⟩, rfl⟩
  rw [UpperHalfPlane.volume_eq_lintegral, himg]

  set obox := Complex.measurableEquivRealProd ⁻¹'
    (Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ioo (Y₀ * 2 ^ j) (Y₀ * 2 ^ (j + 1))) with hobox
  have hmeas : MeasurableSet obox :=
    Complex.measurableEquivRealProd.measurable (measurableSet_Ioo.prod measurableSet_Ioo)
  have hbound : ∀ w ∈ obox,
      ENNReal.ofReal ((Y₀ * 2 ^ (j + 1))⁻¹ ^ 2) ≤ (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    intro w hw
    simp only [hobox, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod,
      Set.mem_Ioo] at hw
    have hwim : (0 : ℝ) < w.im := lt_trans (by positivity) hw.2.1
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos hwim]
    have h1 : (Y₀ * 2 ^ (j + 1))⁻¹ ^ 2 = (1 / (Y₀ * 2 ^ (j + 1))) ^ 2 := by rw [one_div]
    rw [h1]
    gcongr
    exact hw.2.2.le
  calc ENNReal.ofReal ((Y₀ * 2 ^ j) * (Y₀ * 2 ^ (j + 1))⁻¹ ^ 2)
      = ENNReal.ofReal ((Y₀ * 2 ^ (j + 1))⁻¹ ^ 2) * volume obox := by
        rw [hobox, volume_obox]
        rw [show (1 : ℝ) / 2 - -(1 / 2) = 1 by ring,
          show Y₀ * 2 ^ (j + 1) - Y₀ * 2 ^ j = Y₀ * 2 ^ j by ring,
          ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ∫⁻ _ in obox, ENNReal.ofReal ((Y₀ * 2 ^ (j + 1))⁻¹ ^ 2) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ w in obox, (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        rw [← lintegral_indicator hmeas, ← lintegral_indicator hmeas]
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ obox
        · simpa [Set.indicator_of_mem hw] using hbound w hw
        · simp [Set.indicator_of_notMem hw]

private lemma le_unipotentDiagonalSum_of_mem_divBand
    (k : ℍ → ℍ → ℝ≥0∞) {δ : ℝ≥0∞} {c : ℝ}
    (hk : ∀ (z : ℍ) (n : ℤ), n ≠ 0 → |(n : ℝ)| ≤ c * z.im → δ ≤ k z ((n : ℝ) +ᵥ z))
    {Y₀ : ℝ} (hcY : 2 ≤ c * Y₀) (hY : 0 < Y₀)
    {j : ℕ} {z : ℍ} (hz : z ∈ divBand Y₀ j) :
    (2 ^ j : ℝ≥0∞) * δ ≤ unipotentDiagonalSum k z := by
  obtain ⟨-, hlo, -⟩ := hz

  have hinj : Function.Injective (fun m : ℕ => (m : ℤ) + 1) := fun a b h => by simpa using h
  set S : Finset ℤ := (Finset.range (2 ^ j)).map ⟨fun m : ℕ => (m : ℤ) + 1, hinj⟩ with hS
  have hScard : S.card = 2 ^ j := by rw [hS, Finset.card_map, Finset.card_range]

  have hmem : ∀ n ∈ S, n ≠ 0 ∧ |(n : ℝ)| ≤ c * z.im := by
    intro n hn
    rw [hS, Finset.mem_map] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    rw [Finset.mem_range] at hm
    constructor
    · simp only [Function.Embedding.coeFn_mk]; omega
    · simp only [Function.Embedding.coeFn_mk]
      push_cast
      rw [abs_of_pos (by positivity)]

      have h1 : (m : ℝ) + 1 ≤ 2 ^ j := by
        have : (m : ℝ) + 1 ≤ (2 ^ j : ℕ) := by exact_mod_cast hm
        simpa using this
      have h2 : (2 : ℝ) ^ j ≤ c * (Y₀ * 2 ^ j) := by nlinarith [pow_pos (zero_lt_two (α := ℝ)) j]
      have h3 : c * (Y₀ * 2 ^ j) ≤ c * z.im := by nlinarith
      linarith

  calc (2 ^ j : ℝ≥0∞) * δ
      = S.card • δ := by rw [hScard]; rw [nsmul_eq_mul]; norm_cast
    _ = ∑ _n ∈ S, δ := (Finset.sum_const δ).symm
    _ ≤ ∑ n ∈ S, (if n = 0 then 0 else k z ((n : ℝ) +ᵥ z)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hn0, hnle⟩ := hmem n hn
        rw [if_neg hn0]
        exact hk z n hn0 hnle
    _ ≤ unipotentDiagonalSum k z := ENNReal.sum_le_tsum S

theorem lintegral_fd_unipotentDiagonalSum_eq_top
    (k : ℍ → ℍ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) {c : ℝ} (hc : 0 < c)
    (hk : ∀ (z : ℍ) (n : ℤ), n ≠ 0 → |(n : ℝ)| ≤ c * z.im → δ ≤ k z ((n : ℝ) +ᵥ z)) :
    ∫⁻ z in 𝒟, unipotentDiagonalSum k z ∂volume = ⊤ := by

  set Y₀ : ℝ := max (2 / c) 1 with hY₀
  have hY1 : 1 ≤ Y₀ := le_max_right _ _
  have hY : 0 < Y₀ := lt_of_lt_of_le one_pos hY1
  have hcY : 2 ≤ c * Y₀ := by
    have : 2 / c ≤ Y₀ := le_max_left _ _
    rw [div_le_iff₀ hc] at this
    linarith [mul_comm c Y₀]

  refine top_unique ?_
  calc (⊤ : ℝ≥0∞)
      = ∑' _j : ℕ, δ * ENNReal.ofReal ((4 * Y₀)⁻¹) := by
        refine (ENNReal.tsum_const_eq_top_of_ne_zero ?_).symm
        refine mul_ne_zero hδ ?_
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity
    _ ≤ ∑' j : ℕ, ∫⁻ z in divBand Y₀ j, unipotentDiagonalSum k z ∂volume := by
        refine ENNReal.tsum_le_tsum fun j => ?_

        have hlow : ∀ z ∈ divBand Y₀ j,
            (2 ^ j : ℝ≥0∞) * δ ≤ unipotentDiagonalSum k z := fun z hz =>
          le_unipotentDiagonalSum_of_mem_divBand k hk hcY hY hz
        calc δ * ENNReal.ofReal ((4 * Y₀)⁻¹)
            = ((2 ^ j : ℝ≥0∞) * δ) *
                ENNReal.ofReal ((Y₀ * 2 ^ j) * (Y₀ * 2 ^ (j + 1))⁻¹ ^ 2) := by

              rw [show ((2 : ℝ≥0∞) ^ j) = ENNReal.ofReal ((2 : ℝ) ^ j) by
                  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
                mul_comm (ENNReal.ofReal ((2:ℝ) ^ j)) δ, mul_assoc,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 2
              have h2j : (0 : ℝ) < 2 ^ j := by positivity
              field_simp
              ring
          _ ≤ ((2 ^ j : ℝ≥0∞) * δ) * volume (divBand Y₀ j) := by
              gcongr
              exact volume_divBand_ge hY j
          _ = ∫⁻ _ in divBand Y₀ j, ((2 ^ j : ℝ≥0∞) * δ) ∂volume := by
              rw [setLIntegral_const]
          _ ≤ ∫⁻ z in divBand Y₀ j, unipotentDiagonalSum k z ∂volume := by
              rw [← lintegral_indicator (isOpen_divBand Y₀ j).measurableSet,
                ← lintegral_indicator (isOpen_divBand Y₀ j).measurableSet]
              refine lintegral_mono fun z => ?_
              by_cases hz : z ∈ divBand Y₀ j
              · simpa [Set.indicator_of_mem hz] using hlow z hz
              · simp [Set.indicator_of_notMem hz]
    _ = ∫⁻ z in ⋃ j : ℕ, divBand Y₀ j, unipotentDiagonalSum k z ∂volume :=
        (lintegral_iUnion (fun j => (isOpen_divBand Y₀ j).measurableSet)
          (pairwise_disjoint_divBand hY) _).symm
    _ ≤ ∫⁻ z in 𝒟, unipotentDiagonalSum k z ∂volume := by
        refine lintegral_mono_set ?_
        exact Set.iUnion_subset fun j => divBand_subset_fd hY1 j

private lemma unipotentDiagonalSum_le_of_bounded
    (k : ℍ → ℍ → ℝ≥0∞) {M : ℝ≥0∞} {c : ℝ}
    (hbd : ∀ z w, k z w ≤ M)
    (hsupp : ∀ (z : ℍ) (n : ℤ), c * z.im < |(n : ℝ)| → k z ((n : ℝ) +ᵥ z) = 0)
    {N : ℕ} {z : ℍ} (hzN : c * z.im ≤ N) :
    unipotentDiagonalSum k z ≤ (2 * N + 1) * M := by
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hS
  have hScard : S.card ≤ 2 * N + 1 := by
    rw [hS, Int.card_Icc]
    omega

  have hoff : ∀ n : ℤ, n ∉ S → (if n = 0 then 0 else k z ((n : ℝ) +ᵥ z)) = 0 := by
    intro n hn
    rw [hS, Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have hn0 : n ≠ 0 := by rcases hn with h | h <;> omega
    rw [if_neg hn0]
    refine hsupp z n ?_
    have hNn : (N : ℝ) < |(n : ℝ)| := by
      rcases hn with h | h
      ·
        have hneg : (n : ℝ) < 0 := by
          have : n < 0 := by omega
          exact_mod_cast this
        rw [abs_of_neg hneg]
        have : (N : ℤ) < -n := by omega
        exact_mod_cast this
      ·
        have hpos : (0 : ℝ) < n := by
          have : 0 < n := by omega
          exact_mod_cast this
        rw [abs_of_pos hpos]
        exact_mod_cast h
    linarith

  rw [unipotentDiagonalSum, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ n ∈ s, (if n = 0 then 0 else k z ((n : ℝ) +ᵥ z))
      = ∑ n ∈ s ∩ S, (if n = 0 then 0 else k z ((n : ℝ) +ᵥ z)) := by
        refine (Finset.sum_subset Finset.inter_subset_left fun n hn hn' => ?_).symm
        refine hoff n fun hnS => hn' (Finset.mem_inter.mpr ⟨hn, hnS⟩)
    _ ≤ (s ∩ S).card • M := by
        refine Finset.sum_le_card_nsmul _ _ _ fun n _ => ?_
        split
        · exact zero_le'
        · exact hbd z _
    _ ≤ ((2 * N + 1) : ℕ) • M := by
        refine nsmul_le_nsmul_left zero_le' ?_
        exact le_trans (Finset.card_le_card Finset.inter_subset_right) hScard
    _ = (2 * N + 1) * M := by
        rw [nsmul_eq_mul]
        push_cast
        ring

theorem lintegral_truncated_unipotentDiagonalSum_lt_top
    (k : ℍ → ℍ → ℝ≥0∞) {M : ℝ≥0∞} (hM : M ≠ ⊤) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ z w, k z w ≤ M)
    (hsupp : ∀ (z : ℍ) (n : ℤ), c * z.im < |(n : ℝ)| → k z ((n : ℝ) +ᵥ z) = 0)
    (T : ℝ) :
    ∫⁻ z in truncatedFundamentalDomain T, unipotentDiagonalSum k z ∂volume < ⊤ := by

  set N : ℕ := ⌈c * T⌉₊ with hN
  have hbound : ∀ z ∈ truncatedFundamentalDomain T,
      unipotentDiagonalSum k z ≤ (2 * N + 1) * M := by
    rintro z ⟨-, hzT⟩
    refine unipotentDiagonalSum_le_of_bounded k hbd hsupp ?_
    calc c * z.im ≤ c * T := by nlinarith
      _ ≤ N := Nat.le_ceil _
  calc ∫⁻ z in truncatedFundamentalDomain T, unipotentDiagonalSum k z ∂volume
      ≤ ∫⁻ _ in truncatedFundamentalDomain T, ((2 * N + 1) * M) ∂volume := by
        rw [← lintegral_indicator (measurableSet_truncatedFundamentalDomain T),
          ← lintegral_indicator (measurableSet_truncatedFundamentalDomain T)]
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ truncatedFundamentalDomain T
        · simpa [Set.indicator_of_mem hz] using hbound z hz
        · simp [Set.indicator_of_notMem hz]
    _ = (2 * N + 1) * M * volume (truncatedFundamentalDomain T) := setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ hM.lt_top) ?_
        · exact (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num)
            (ENNReal.natCast_lt_top N), ENNReal.one_lt_top⟩)
        · exact lt_of_le_of_lt
            (measure_mono fun z hz => hz.1) FLT.FundamentalDomainVolume.volume_fd_lt_top

def windowIndicator : ℍ → ℍ → ℝ≥0∞ := fun z w => if |w.re - z.re| ≤ z.im then 1 else 0

theorem windowIndicator_lower (z : ℍ) (n : ℤ) (_ : n ≠ 0) (hn : |(n : ℝ)| ≤ 1 * z.im) :
    (1 : ℝ≥0∞) ≤ windowIndicator z ((n : ℝ) +ᵥ z) := by
  rw [windowIndicator, if_pos]
  rw [UpperHalfPlane.vadd_re]
  simpa using hn

theorem windowIndicator_support (z : ℍ) (n : ℤ) (hn : 1 * z.im < |(n : ℝ)|) :
    windowIndicator z ((n : ℝ) +ᵥ z) = 0 := by
  rw [windowIndicator, if_neg]
  rw [UpperHalfPlane.vadd_re]
  simp only [add_sub_cancel_right, not_le]
  simpa using hn

theorem sat_windowIndicator :
    (∫⁻ z in 𝒟, unipotentDiagonalSum windowIndicator z ∂volume = ⊤) ∧
    ∀ T : ℝ, ∫⁻ z in truncatedFundamentalDomain T,
      unipotentDiagonalSum windowIndicator z ∂volume < ⊤ := by
  constructor
  · exact lintegral_fd_unipotentDiagonalSum_eq_top windowIndicator one_ne_zero one_pos
      windowIndicator_lower
  · intro T
    refine lintegral_truncated_unipotentDiagonalSum_lt_top windowIndicator ENNReal.one_ne_top
      one_pos (fun z w => ?_) windowIndicator_support T
    rw [windowIndicator]
    split <;> simp

theorem lintegral_fd_unipotentDiagonalSum_zero_ne_top :
    ∫⁻ z in 𝒟, unipotentDiagonalSum (fun _ _ => 0) z ∂volume ≠ ⊤ := by
  simp

example : ((Finset.range (2 ^ 2)).map
    (⟨fun m : ℕ => (m : ℤ) + 1, fun a b h => by simpa using h⟩ : ℕ ↪ ℤ)).card = 4 := by
  rw [Finset.card_map, Finset.card_range]
  norm_num

example : (UpperHalfPlane.I ∈ truncatedFundamentalDomain 2) ∧
    (UpperHalfPlane.mk ⟨0, 3⟩ (by norm_num) ∈ cuspNeighbourhood 2) := by
  refine ⟨⟨ModularGroup.I_mem_fd, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [UpperHalfPlane.I_im]; norm_num
  · show (1 : ℝ) ≤ Complex.normSq (⟨0, 3⟩ : ℂ)
    rw [Complex.normSq_apply]
    norm_num
  · show |(UpperHalfPlane.mk ⟨0, 3⟩ (by norm_num)).re| ≤ (1 : ℝ) / 2
    rw [UpperHalfPlane.mk_re]
    show |(0 : ℝ)| ≤ 1 / 2
    norm_num
  · show (2 : ℝ) < (UpperHalfPlane.mk ⟨0, 3⟩ (by norm_num)).im
    rw [UpperHalfPlane.mk_im]
    show (2 : ℝ) < 3
    norm_num

end FLT.TruncatedDomainPartition
end


