-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:35.296298+00:00
-- url     : https://prove2.me/theorems/1447e3e5-f9c1-4b77-a186-0a3aeb94f67f
-- title:
--   Residue Norm Valuation Subring Eq Zero Iff
-- statement:
--   Definitions and structural lemmas for Residue Norm Valuation Subring Eq Zero Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ResidueNormValuationSubringEqZeroIff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Filter Topology MvPowerSeries
section
variable {C : Type*} [NormedField C] [IsUltrametricDist C] {σ : Type*}
local notation "𝒪" => Valuation.valuationSubring (NormedField.valuation (K := C))
theorem mem_normValuationSubring_iff (x : C) : x ∈ 𝒪 ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
  rfl
theorem residue_normValuationSubring_eq_zero_iff (x : 𝒪) :
    IsLocalRing.residue 𝒪 x = 0 ↔ ‖(x : C)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, NormedField.valuation_apply]
  rfl
omit [IsUltrametricDist C] in
theorem norm_finsuppProd_pow (t : σ →₀ ℕ) (z : σ → C) :
    ‖t.prod (z · ^ ·)‖ = t.prod (fun i n => ‖z i‖ ^ n) := by
  simp [Finsupp.prod, norm_prod]
theorem finsuppProd_pow_mono (t : σ →₀ ℕ) {c d : σ → ℝ} (h0 : ∀ i, 0 ≤ c i) (h : ∀ i, c i ≤ d i) :
    t.prod (c · ^ ·) ≤ t.prod (d · ^ ·) :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (h0 i) _) fun i _ => pow_le_pow_left₀ (h0 i) (h i) _
theorem finsuppProd_const_pow (t : σ →₀ ℕ) (r : ℝ) : t.prod (fun _ n => r ^ n) = r ^ t.degree := by
  simp [Finsupp.prod, Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum]
theorem norm_lt_of_hasSum {ι : Type*} {f : ι → C} {s : C} {r : ℝ} (hr : 0 < r) (hf : HasSum f s)
    (h : ∀ i, ‖f i‖ < r) : ‖s‖ < r := by
  have hcl : IsClosed (Metric.ball (0 : C) r) := IsUltrametricDist.isClosed_ball _ _
  have : s ∈ Metric.ball (0 : C) r := by
    refine hcl.mem_of_tendsto hf (Eventually.of_forall fun F => ?_)
    rw [mem_ball_zero_iff]
    classical
    induction F using Finset.induction_on with
    | empty => simpa using hr
    | insert a F ha ih =>
      rw [Finset.sum_insert ha]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (h a) ih)
  simpa using this
theorem exists_norm_sum_monomial_eq_one [Infinite (IsLocalRing.ResidueField 𝒪)]
    (S : Finset (σ →₀ ℕ)) (b : (σ →₀ ℕ) → C) (hb : ∀ t, ‖b t‖ ≤ 1) {t₀ : σ →₀ ℕ} (h₀ : t₀ ∈ S)
    (hb₀ : ‖b t₀‖ = 1) :
    ∃ z : σ → C, (∀ i, ‖z i‖ ≤ 1) ∧ ‖∑ t ∈ S, b t * t.prod (z · ^ ·)‖ = 1 := by
  classical
  let b' : (σ →₀ ℕ) → 𝒪 := fun t => ⟨b t, (mem_normValuationSubring_iff _).2 (hb t)⟩
  let P : MvPolynomial σ (IsLocalRing.ResidueField 𝒪) :=
    ∑ t ∈ S, MvPolynomial.monomial t (IsLocalRing.residue 𝒪 (b' t))
  have hP : P ≠ 0 := by
    intro h
    have h1 : P.coeff t₀ = IsLocalRing.residue 𝒪 (b' t₀) := by
      simp [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, h₀]
    rw [h, MvPolynomial.coeff_zero, eq_comm, residue_normValuationSubring_eq_zero_iff] at h1
    exact absurd hb₀ h1.ne
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x P ≠ 0 := by
    by_contra! h
    exact hP (MvPolynomial.funext fun x => by simp [h x])
  choose y hy using fun i => IsLocalRing.residue_surjective (R := 𝒪) (x i)
  refine ⟨fun i => y i, fun i => (mem_normValuationSubring_iff _).1 (y i).2, ?_⟩
  let u : 𝒪 := ∑ t ∈ S, b' t * t.prod (y · ^ ·)
  have hu : (u : C) = ∑ t ∈ S, b t * t.prod (fun i n => (y i : C) ^ n) := by
    simp [u, b', Finsupp.prod]
  have hres : IsLocalRing.residue 𝒪 u = MvPolynomial.eval x P := by
    simp [u, P, MvPolynomial.eval_monomial, Finsupp.prod, hy]
  rw [← hu]
  refine le_antisymm ((mem_normValuationSubring_iff _).1 u.2) (not_lt.1 fun h => hx ?_)
  rw [← hres, residue_normValuationSubring_eq_zero_iff]
  exact h
theorem exists_norm_eq_of_tendsto_zero [Infinite (IsLocalRing.ResidueField 𝒪)]
    (a : (σ →₀ ℕ) → C) (ha : Tendsto a cofinite (𝓝 0)) {t₀ : σ →₀ ℕ} (h₀ : ∀ t, ‖a t‖ ≤ ‖a t₀‖) :
    ∃ z : σ → C, (∀ i, ‖z i‖ ≤ 1) ∧
      ∀ s, HasSum (fun t => a t * t.prod (z · ^ ·)) s → ‖s‖ = ‖a t₀‖ := by
  classical
  by_cases h00 : a t₀ = 0
  · refine ⟨0, by simp, fun s hs => ?_⟩
    have : ∀ t, a t = 0 := fun t => by simpa [h00] using h₀ t
    simp only [this, zero_mul] at hs
    simp [hs.unique hasSum_zero, h00]
  have hpos : 0 < ‖a t₀‖ := norm_pos_iff.2 h00
  have hfin : {t | ¬ ‖a t‖ < ‖a t₀‖}.Finite := by
    have := (NormedAddGroup.tendsto_nhds_zero.1 ha) _ hpos
    simpa [Filter.eventually_cofinite] using this
  obtain ⟨z, hz, hz1⟩ := exists_norm_sum_monomial_eq_one hfin.toFinset (fun t => a t / a t₀)
    (fun t => by rw [norm_div, div_le_one hpos]; exact h₀ t) (t₀ := t₀) (by simp)
    (by simp [h00])
  refine ⟨z, hz, fun s hs => ?_⟩
  set u := ∑ t ∈ hfin.toFinset, a t * t.prod (z · ^ ·) with hu
  have hun : ‖u‖ = ‖a t₀‖ := by
    have : u = a t₀ * ∑ t ∈ hfin.toFinset, a t / a t₀ * t.prod (z · ^ ·) := by
      rw [hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      field_simp
    rw [this, norm_mul, hz1, mul_one]
  have htail : HasSum (fun t : {t // t ∉ hfin.toFinset} => a t * t.1.prod (z · ^ ·)) (s - u) :=
    (Finset.hasSum_iff_compl hfin.toFinset).1 hs
  have hlt : ‖s - u‖ < ‖a t₀‖ := by
    refine norm_lt_of_hasSum hpos htail fun t => ?_
    have h1 : ‖a t‖ < ‖a t₀‖ := by simpa using t.2
    have h2 : ‖t.1.prod (z · ^ ·)‖ ≤ 1 := by
      rw [norm_finsuppProd_pow]
      simpa using finsuppProd_pow_mono t.1 (fun i => norm_nonneg (z i)) hz
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt h1
  have : s = u + (s - u) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hun]; exact hlt.ne'), hun,
    max_eq_left hlt.le]
theorem infinite_residueField_of_isAlgClosed [IsAlgClosed C] :
    Infinite (IsLocalRing.ResidueField 𝒪) := by
  by_contra hk
  rw [not_infinite_iff_finite] at hk
  have := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪)
  set q := Fintype.card (IsLocalRing.ResidueField 𝒪) with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial C) (by
    have : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial C).degree = q := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_sub_eq_left_of_degree_lt]
      · simp
      · simpa using hq1
      · rw [Polynomial.degree_sub_eq_left_of_degree_lt]
        · simpa using (zero_lt_one.trans hq1)
        · simpa using hq1
    rw [this]
    simpa using (zero_lt_one.trans hq1).ne')
  have hx' : x ^ q = x - 1 := by
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at hx
    linear_combination hx
  have hx1 : ‖x‖ ≤ 1 := by
    by_contra! h
    have h1 : ‖x - 1‖ ≤ ‖x‖ := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
      simpa using h.le
    have h2 : ‖x‖ ^ 1 < ‖x‖ ^ q := pow_lt_pow_right₀ h hq1
    rw [← hx', norm_pow] at h1
    linarith [pow_one ‖x‖]
  let y : 𝒪 := ⟨x, (mem_normValuationSubring_iff _).2 hx1⟩
  have hy : y ^ q = y - 1 := Subtype.ext (by simpa [y] using hx')
  have h3 := congrArg (IsLocalRing.residue 𝒪) hy
  rw [map_pow, map_sub, map_one, hq, FiniteField.pow_card] at h3
  simp [eq_sub_iff_add_eq] at h3
noncomputable def seriesValue {R : Type*} [CommSemiring R] [TopologicalSpace R]
    (g : MvPowerSeries σ R) (z : σ → R) : R :=
  ∑' t : σ →₀ ℕ, coeff t g * t.prod (z · ^ ·)
omit [IsUltrametricDist C] in

theorem isRestricted_const_iff (g : MvPowerSeries σ C) (r : ℝ) :
    IsRestricted (fun _ => r) g ↔
      Tendsto (fun t : σ →₀ ℕ => ‖coeff t g‖ * r ^ t.degree) cofinite (𝓝 0) := by
  simp only [IsRestricted, finsuppProd_const_pow]
omit [IsUltrametricDist C] in
theorem norm_term_le (g : MvPowerSeries σ C) {c : σ → ℝ} {z : σ → C} (hz : ∀ i, ‖z i‖ ≤ c i)
    (t : σ →₀ ℕ) : ‖coeff t g * t.prod (z · ^ ·)‖ ≤ ‖coeff t g‖ * t.prod (c · ^ ·) := by
  rw [norm_mul, norm_finsuppProd_pow]
  exact mul_le_mul_of_nonneg_left (finsuppProd_pow_mono t (fun i => norm_nonneg (z i)) hz)
    (norm_nonneg _)
theorem hasSum_seriesValue [CompleteSpace C] {g : MvPowerSeries σ C} {c : σ → ℝ}
    (hg : IsRestricted c g) {z : σ → C} (hz : ∀ i, ‖z i‖ ≤ c i) :
    HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) (seriesValue g z) := by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  exact squeeze_zero_norm (norm_term_le g hz) hg
omit [IsUltrametricDist C] in

theorem isRestricted_of_summable {g : MvPowerSeries σ C} {w : σ → C}
    (h : Summable fun t : σ →₀ ℕ => coeff t g * t.prod (w · ^ ·)) :
    IsRestricted (fun i => ‖w i‖) g := by
  have := h.tendsto_cofinite_zero.norm
  simpa only [IsRestricted, norm_mul, norm_finsuppProd_pow, norm_zero] using this
omit [IsUltrametricDist C] in

theorem exists_isGreatest_gaussNorm {g : MvPowerSeries σ C} {c : σ → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hg : IsRestricted c g) :
    IsGreatest (Set.range fun t : σ →₀ ℕ => ‖coeff t g‖ * t.prod (c · ^ ·))
      (gaussNorm norm c g) := by
  have hnn : ∀ t : σ →₀ ℕ, 0 ≤ ‖coeff t g‖ * t.prod (c · ^ ·) := fun t =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hc i) _)
  obtain ⟨t₀, h₀⟩ : ∃ t₀ : σ →₀ ℕ, ∀ t : σ →₀ ℕ,
      ‖coeff t g‖ * t.prod (c · ^ ·) ≤ ‖coeff t₀ g‖ * t₀.prod (c · ^ ·) := by
    by_cases h : ∃ t₁ : σ →₀ ℕ, 0 < ‖coeff t₁ g‖ * t₁.prod (c · ^ ·)
    · obtain ⟨t₁, h₁⟩ := h
      have hfin : {t : σ →₀ ℕ |
          ¬ ‖coeff t g‖ * t.prod (c · ^ ·) < ‖coeff t₁ g‖ * t₁.prod (c · ^ ·)}.Finite :=
        Filter.eventually_cofinite.1 (hg.eventually_lt_const h₁)
      obtain ⟨t₀, -, h₀⟩ := hfin.toFinset.exists_max_image
        (fun t => ‖coeff t g‖ * t.prod (c · ^ ·)) ⟨t₁, by simp⟩
      refine ⟨t₀, fun t => ?_⟩
      by_cases ht : t ∈ hfin.toFinset
      · exact h₀ t ht
      · have : ‖coeff t g‖ * t.prod (c · ^ ·) < ‖coeff t₁ g‖ * t₁.prod (c · ^ ·) := by
          simpa using ht
        exact this.le.trans (h₀ t₁ (by simp))
    · push Not at h
      exact ⟨0, fun t => (h t).trans (hnn 0)⟩
  have hG : IsGreatest (Set.range fun t : σ →₀ ℕ => ‖coeff t g‖ * t.prod (c · ^ ·))
      (‖coeff t₀ g‖ * t₀.prod (c · ^ ·)) := ⟨⟨t₀, rfl⟩, by rintro _ ⟨t, rfl⟩; exact h₀ t⟩
  have : gaussNorm norm c g = ‖coeff t₀ g‖ * t₀.prod (c · ^ ·) := hG.csSup_eq
  rwa [this]
theorem norm_le_gaussNorm_of_hasSum {g : MvPowerSeries σ C} {c : σ → ℝ}
    (hg : IsRestricted c g) {z : σ → C} (hz : ∀ i, ‖z i‖ ≤ c i) {s : C}
    (hs : HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) s) :
    ‖s‖ ≤ gaussNorm norm c g := by
  have hG := exists_isGreatest_gaussNorm (fun i => (norm_nonneg _).trans (hz i)) hg
  rw [← hs.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le fun t =>
    (norm_term_le g hz t).trans (hG.2 ⟨t, rfl⟩)
theorem exists_norm_eq_gaussNorm_of_hasSum [Infinite (IsLocalRing.ResidueField 𝒪)]
    {g : MvPowerSeries σ C} {w : σ → C} (hg : IsRestricted (fun i => ‖w i‖) g) :
    ∃ z : σ → C, (∀ i, ‖z i‖ ≤ ‖w i‖) ∧
      ∀ s, HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) s →
        ‖s‖ = gaussNorm norm (fun i => ‖w i‖) g := by
  obtain ⟨⟨t₀, ht₀⟩, hG⟩ := exists_isGreatest_gaussNorm (fun i => norm_nonneg (w i)) hg
  have hn : ∀ t : σ →₀ ℕ, ‖coeff t g * t.prod (w · ^ ·)‖ =
      ‖coeff t g‖ * t.prod (fun i n => ‖w i‖ ^ n) := fun t => by
    rw [norm_mul, norm_finsuppProd_pow]
  obtain ⟨z, hz, hs⟩ := exists_norm_eq_of_tendsto_zero
    (fun t : σ →₀ ℕ => coeff t g * t.prod (w · ^ ·))
    (squeeze_zero_norm (norm_term_le g fun i => le_rfl) hg) (t₀ := t₀) (fun t => by
      rw [hn, hn]
      exact (hG ⟨t, rfl⟩).trans ht₀.ge)
  refine ⟨fun i => w i * z i, fun i => ?_, fun s h => ?_⟩
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hz i)
  · refine (hs s ?_).trans ((hn t₀).trans ht₀)
    simpa only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, mul_assoc] using h
theorem isGreatest_norm_seriesValue [CompleteSpace C] [Infinite (IsLocalRing.ResidueField 𝒪)]
    {g : MvPowerSeries σ C} {w : σ → C} (hg : IsRestricted (fun i => ‖w i‖) g) :
    IsGreatest ((fun z => ‖seriesValue g z‖) '' {z | ∀ i, ‖z i‖ ≤ ‖w i‖})
      (gaussNorm norm (fun i => ‖w i‖) g) := by
  obtain ⟨z, hz, hs⟩ := exists_norm_eq_gaussNorm_of_hasSum hg
  refine ⟨⟨z, hz, hs _ (hasSum_seriesValue hg hz)⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact norm_le_gaussNorm_of_hasSum hg hy (hasSum_seriesValue hg hy)
theorem norm_coeff_le_of_hasSum [Infinite (IsLocalRing.ResidueField 𝒪)]
    (hd : ∀ r : ℝ, r < 1 → ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1) {g : MvPowerSeries σ C} {M : ℝ}
    (h : ∀ x : C, ‖x‖ < 1 → ∀ z : σ → C, (∀ i, ‖z i‖ ≤ ‖x‖) →
      ∃ s, HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) s ∧ ‖s‖ ≤ M)
    (t : σ →₀ ℕ) : ‖coeff t g‖ ≤ M := by
  have key : ∀ x : C, ‖x‖ < 1 → ‖coeff t g‖ * ‖x‖ ^ t.degree ≤ M := fun x hx => by
    obtain ⟨s₀, hs₀, -⟩ := h x hx (fun _ => x) fun _ => le_rfl
    have hg := isRestricted_of_summable hs₀.summable
    obtain ⟨z, hz, hs⟩ := exists_norm_eq_gaussNorm_of_hasSum hg
    obtain ⟨s, hs1, hs2⟩ := h x hx z hz
    rw [← finsuppProd_const_pow]
    exact ((exists_isGreatest_gaussNorm (fun _ => norm_nonneg x) hg).2 ⟨t, rfl⟩).trans
      ((hs s hs1).ge.trans hs2)
  by_contra! hM
  have hc : ContinuousAt (fun r : ℝ => ‖coeff t g‖ * r ^ t.degree) 1 := by fun_prop
  have hev : ∀ᶠ r : ℝ in 𝓝 1, M < ‖coeff t g‖ * r ^ t.degree :=
    hc.eventually_const_lt (by simpa using hM)
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hev
  obtain ⟨x, hx1, hx2⟩ := hd l hl
  exact absurd (key x hx2) (not_le.2 (hlu ⟨hx1, hx2.trans hu⟩))
theorem norm_coeff_le_of_norm_seriesValue_le [CompleteSpace C]
    [Infinite (IsLocalRing.ResidueField 𝒪)]
    (hd : ∀ r : ℝ, r < 1 → ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1) {g : MvPowerSeries σ C}
    (hg : ∀ r : ℝ, 0 ≤ r → r < 1 → IsRestricted (fun _ => r) g) {M : ℝ}
    (h : ∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖seriesValue g z‖ ≤ M) (t : σ →₀ ℕ) :
    ‖coeff t g‖ ≤ M :=
  norm_coeff_le_of_hasSum hd (fun x hx z hz =>
    ⟨_, hasSum_seriesValue (hg _ (norm_nonneg x) hx) hz, h z fun i => (hz i).trans_lt hx⟩) t
theorem exists_map_eq_iff_norm_coeff_le_one (g : MvPowerSeries σ C) :
    (∃ g₀ : MvPowerSeries σ 𝒪, MvPowerSeries.map (𝒪).subtype g₀ = g) ↔ ∀ t, ‖coeff t g‖ ≤ 1 := by
  constructor
  · rintro ⟨g₀, rfl⟩ t
    rw [coeff_map]
    exact (mem_normValuationSubring_iff _).1 (coeff t g₀).2
  · intro h
    refine ⟨fun t => ⟨coeff t g, (mem_normValuationSubring_iff _).2 (h t)⟩, ?_⟩
    ext t
    rfl
omit [IsUltrametricDist C] in

theorem isRestricted_of_norm_coeff_le [Finite σ] {g : MvPowerSeries σ C} {M : ℝ}
    (h : ∀ t, ‖coeff t g‖ ≤ M) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    IsRestricted (fun _ => r) g := by
  rw [isRestricted_const_iff]
  have hdeg : Tendsto (fun t : σ →₀ ℕ => t.degree) cofinite atTop := by
    refine tendsto_atTop.2 fun n => Filter.eventually_cofinite.2 ?_
    exact (Finsupp.finite_of_degree_le n).subset fun t ht => (not_le.1 ht).le
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp hdeg).const_mul M
  rw [mul_zero] at this
  exact squeeze_zero (fun t => by positivity)
    (fun t => mul_le_mul_of_nonneg_right (h t) (pow_nonneg h0 _)) this
omit [IsUltrametricDist C] in

theorem exists_radius_lt_one [Finite σ] {z : σ → C} (hz : ∀ i, ‖z i‖ < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ i, ‖z i‖ ≤ r := by
  have := Fintype.ofFinite σ
  exact ⟨‖z‖, norm_nonneg _, (pi_norm_lt_iff one_pos).2 hz, norm_le_pi_norm z⟩
theorem hasSum_seriesValue_of_norm_lt_one [CompleteSpace C] [Finite σ] {g : MvPowerSeries σ C}
    (hg : ∀ r : ℝ, 0 ≤ r → r < 1 → IsRestricted (fun _ => r) g) {z : σ → C}
    (hz : ∀ i, ‖z i‖ < 1) :
    HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) (seriesValue g z) := by
  obtain ⟨r, h0, h1, hr⟩ := exists_radius_lt_one hz
  exact hasSum_seriesValue (hg r h0 h1) hr
theorem norm_le_of_hasSum_of_norm_coeff_le {g : MvPowerSeries σ C} {M : ℝ}
    (h : ∀ t, ‖coeff t g‖ ≤ M) {z : σ → C} (hz : ∀ i, ‖z i‖ ≤ 1) {s : C}
    (hs : HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) s) : ‖s‖ ≤ M := by
  rw [← hs.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun t => (norm_term_le g hz t).trans ?_
  simpa using h t
theorem bounded_series_integral_of_dense [CompleteSpace C] [Infinite (IsLocalRing.ResidueField 𝒪)]
    (hd : ∀ r : ℝ, r < 1 → ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1) [Finite σ] (g : MvPowerSeries σ C)
    (hg : ∀ r : ℝ, 0 ≤ r → r < 1 →
      Tendsto (fun t : σ →₀ ℕ => ‖coeff t g‖ * r ^ t.degree) cofinite (𝓝 0)) :
    (∀ z : σ → C, (∀ i, ‖z i‖ < 1) →
      HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) (seriesValue g z)) ∧
    (∀ x : C, ‖x‖ < 1 → ∃ m : ℝ,
      IsGreatest ((fun z => ‖seriesValue g z‖) '' {z : σ → C | ∀ i, ‖z i‖ ≤ ‖x‖}) m ∧
      IsGreatest (Set.range fun t : σ →₀ ℕ => ‖coeff t g‖ * ‖x‖ ^ t.degree) m) ∧
    (∀ M : ℝ, (∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖seriesValue g z‖ ≤ M) ↔ ∀ t, ‖coeff t g‖ ≤ M) ∧
    ((∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖seriesValue g z‖ ≤ 1) ↔
      ∃ g₀ : MvPowerSeries σ 𝒪, MvPowerSeries.map (𝒪).subtype g₀ = g) := by
  have hg' : ∀ r : ℝ, 0 ≤ r → r < 1 → IsRestricted (fun _ => r) g := fun r h0 h1 =>
    (isRestricted_const_iff g r).2 (hg r h0 h1)
  have h3 : ∀ M : ℝ, (∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖seriesValue g z‖ ≤ M) ↔
      ∀ t, ‖coeff t g‖ ≤ M := fun M =>
    ⟨fun h => norm_coeff_le_of_norm_seriesValue_le hd hg' h, fun h z hz =>
      norm_le_of_hasSum_of_norm_coeff_le h (fun i => (hz i).le)
        (hasSum_seriesValue_of_norm_lt_one hg' hz)⟩
  refine ⟨fun z hz => hasSum_seriesValue_of_norm_lt_one hg' hz, fun x hx => ?_, h3,
    (h3 1).trans (exists_map_eq_iff_norm_coeff_le_one g).symm⟩
  have hx' := hg' _ (norm_nonneg x) hx
  refine ⟨_, isGreatest_norm_seriesValue (w := fun _ => x) hx', ?_⟩
  simpa only [finsuppProd_const_pow] using
    exists_isGreatest_gaussNorm (fun _ => norm_nonneg x) hx'
end
theorem exists_lt_norm_lt_one_of_isAlgClosed {C : Type*} [NontriviallyNormedField C]
    [IsAlgClosed C] (r : ℝ) (hr : r < 1) : ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1 := by
  obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one C
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right r 0)
    (max_lt hr one_pos)).eventually_lt_const hy0
  obtain ⟨n, hn, hn1⟩ := (h.and (eventually_gt_atTop 0)).exists
  obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y hn1
  rw [norm_pow] at hn hy1
  exact ⟨x, (le_max_left r 0).trans_lt (lt_of_pow_lt_pow_left₀ n (norm_nonneg x) hn),
    (pow_lt_one_iff_of_nonneg (norm_nonneg x) hn1.ne').1 hy1⟩
theorem bounded_series_integral {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] {σ : Type*} [Finite σ] (g : MvPowerSeries σ C)
    (hg : ∀ r : ℝ, 0 ≤ r → r < 1 →
      Tendsto (fun t : σ →₀ ℕ => ‖coeff t g‖ * r ^ t.degree) cofinite (𝓝 0)) :
    (∀ z : σ → C, (∀ i, ‖z i‖ < 1) →
      HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) (seriesValue g z)) ∧
    (∀ x : C, ‖x‖ < 1 → ∃ m : ℝ,
      IsGreatest ((fun z => ‖seriesValue g z‖) '' {z : σ → C | ∀ i, ‖z i‖ ≤ ‖x‖}) m ∧
      IsGreatest (Set.range fun t : σ →₀ ℕ => ‖coeff t g‖ * ‖x‖ ^ t.degree) m) ∧
    (∀ M : ℝ, (∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖seriesValue g z‖ ≤ M) ↔ ∀ t, ‖coeff t g‖ ≤ M) ∧
    ((∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖seriesValue g z‖ ≤ 1) ↔
      ∃ g₀ : MvPowerSeries σ (NormedField.valuation (K := C)).valuationSubring,
        MvPowerSeries.map (NormedField.valuation (K := C)).valuationSubring.subtype g₀ = g) :=
  haveI := infinite_residueField_of_isAlgClosed (C := C)
  bounded_series_integral_of_dense exists_lt_norm_lt_one_of_isAlgClosed g hg
example (p : ℕ) [Fact p.Prime] (n : ℕ) (z : Fin n → ℂ_[p]) (hz : ∀ i, ‖z i‖ < 1) :
    ‖seriesValue (fun _ => 1 : MvPowerSeries (Fin n) ℂ_[p]) z‖ ≤ 1 := by
  have h : ∀ t, ‖coeff t (fun _ => 1 : MvPowerSeries (Fin n) ℂ_[p])‖ ≤ 1 := fun t =>
    norm_one.le
  exact ((bounded_series_integral _ fun r h0 h1 => (isRestricted_const_iff _ r).1
    (isRestricted_of_norm_coeff_le h h0 h1)).2.2.1 1).2 h z hz
end GlobalTheory


