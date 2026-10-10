-- Prove2me | solution 1 for ArtinPrimitiveRoots.norm_dyadPairingSTS_sub_dyadPairingA_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:06:39.113816+00:00
-- url     : https://prove2.me/submissions/ab581756-4a3d-4162-83a9-a3f84d069b09

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_abs_card_specialLinearGroup_box_sub_le

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

/-- The product of all labels of a list. -/
def listProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ∏ j, ℓ i j

end ArtinPrimitiveRoots
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D8a** ([21] §4.9, (4.56)–(4.57)): removing the goodness projections from the pairing. -/
def GoodnessRemovalStmt (δ C c₁ c₂ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ A : ℝ, 0 < A →
    ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ α β : ℕ → ℂ,
        (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
          ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
        ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
            c * (2 ^ k * Y * Hm * Hn * log x ^ (-A))

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

lemma circNorm_eq_norm (t : ℝ) : circNorm t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]; rfl

lemma continuous_circNorm : Continuous circNorm := by
  have : circNorm = fun t : ℝ => ‖(t : UnitAddCircle)‖ := funext circNorm_eq_norm
  rw [this]
  exact continuous_norm.comp (AddCircle.continuous_mk' 1)

/-- For a nonzero integer `n`, `{r ∈ (0,1] : ‖n r‖ ≤ ε}` has measure at most `2ε`
(multiplication by `n` preserves Haar measure on `ℝ/ℤ`). -/
lemma volume_circNorm_le (n : ℤ) (hn : n ≠ 0) (ε : ℝ) :
    volume ({r : ℝ | circNorm (n * r) ≤ ε} ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * ε) := by
  set f : ℝ → UnitAddCircle := fun r => n • (r : UnitAddCircle)
  have hf : MeasurePreserving f (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    have := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hn).comp
      (AddCircle.measurePreserving_mk (1 : ℝ) 0)
    simpa [f, Function.comp_def] using this
  have hset : {r : ℝ | circNorm (n * r) ≤ ε} = f ⁻¹' Metric.closedBall 0 ε := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, f]
    rw [circNorm_eq_norm, ← AddCircle.coe_zsmul]
    simp
  have hmeas : MeasurableSet (f ⁻¹' Metric.closedBall 0 ε) :=
    hf.measurable measurableSet_closedBall
  rw [hset, ← Measure.restrict_apply hmeas, hf.measure_preimage
    measurableSet_closedBall.nullMeasurableSet, AddCircle.volume_closedBall]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- The `{r : ‖n r‖ < ε}` level sets are measurable. -/
lemma measurableSet_circNorm_lt (n : ℝ) (ε : ℝ) : MeasurableSet {r : ℝ | circNorm (n * r) < ε} :=
  measurableSet_lt (continuous_circNorm.comp (continuous_const.mul continuous_id)).measurable
    measurable_const

lemma omitProd_pos {K M : ℕ} (ℓ : Fin K → Fin M → ℕ) (hℓ : ∀ i j, 0 < ℓ i j)
    (o : Fin K → Fin M) : 0 < omitProd ℓ o :=
  prod_pos fun i _ => prod_pos fun j _ => hℓ i j

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

lemma volume_weighted_gt_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (S : ι → Set ℝ) (hS : ∀ i ∈ s, MeasurableSet (S i)) (ε τ : ℝ) (hτ : 0 < τ)
    (hSε : ∀ i ∈ s, volume (S i ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal ε) [∀ i r, Decidable (r ∈ S i)] :
    volume ({r | τ < ∑ i ∈ s, w i * (if r ∈ S i then 1 else 0)} ∩ Set.Ioc 0 1) ≤
      ENNReal.ofReal ((∑ i ∈ s, w i) * ε / τ) := by
  set μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  set g : ℝ → ENNReal := fun r => ∑ i ∈ s, ENNReal.ofReal (w i) * (S i).indicator 1 r
  have hg : ∀ r, ENNReal.ofReal (∑ i ∈ s, w i * (if r ∈ S i then 1 else 0)) = g r := by
    intro r
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (hw i hi) (by split_ifs <;> norm_num))]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : r ∈ S i <;> simp [h, Set.indicator]
  have hsub : {r | τ < ∑ i ∈ s, w i * (if r ∈ S i then 1 else 0)} ⊆
      {r | ENNReal.ofReal τ ≤ g r} := by
    intro r hr
    simp only [Set.mem_ofPred_eq] at hr ⊢
    rw [← hg]
    exact ENNReal.ofReal_le_ofReal hr.le
  have hmi : ∀ i ∈ s, Measurable fun r => ENNReal.ofReal (w i) * (S i).indicator 1 r :=
    fun i hi => measurable_const.mul (measurable_one.indicator (hS i hi))
  have hmeas : Measurable g := Finset.measurable_sum _ hmi
  have hint : ∫⁻ r, g r ∂μ ≤ ∑ i ∈ s, ENNReal.ofReal (w i) * ENNReal.ofReal ε := by
    show ∫⁻ r, (∑ i ∈ s, ENNReal.ofReal (w i) * (S i).indicator 1 r) ∂μ ≤ _
    rw [lintegral_finsetSum _ hmi]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [lintegral_const_mul _ (measurable_one.indicator (hS i hi)), lintegral_indicator_one
      (hS i hi), Measure.restrict_apply (hS i hi)]
    exact mul_le_mul_right (hSε i hi) _
  have hmk := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable (μ := μ) (ENNReal.ofReal τ)
  have h1 : volume ({r | τ < ∑ i ∈ s, w i * (if r ∈ S i then 1 else 0)} ∩ Set.Ioc 0 1) ≤
      μ {r | ENNReal.ofReal τ ≤ g r} := by
    rw [Measure.restrict_apply' measurableSet_Ioc]
    exact measure_mono (Set.inter_subset_inter_left _ hsub)
  have hsum : ∑ i ∈ s, ENNReal.ofReal (w i) * ENNReal.ofReal ε =
      ENNReal.ofReal ((∑ i ∈ s, w i) * ε) := by
    rw [ENNReal.ofReal_mul (sum_nonneg hw), ENNReal.ofReal_sum_of_nonneg hw, sum_mul]
  have hτ' : ENNReal.ofReal τ ≠ 0 := by simpa using hτ
  rw [ENNReal.ofReal_div_of_pos hτ]
  refine h1.trans ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl hτ') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hmk.trans (hint.trans hsum.le)

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

lemma pos_of_mem_primeGroup {x b : ℝ} {p : ℕ} (h : p ∈ primeGroup x b) : 0 < p := by
  unfold primeGroup at h
  exact (Finset.mem_filter.1 h).2.1.pos

lemma freshWeight_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (I : Finset (Fin K))
    (T : Fin K → ℕ) : 0 ≤ freshWeight x a I T := by
  unfold freshWeight
  refine prod_nonneg fun i _ => ?_
  split_ifs
  · norm_num
  · have : 0 ≤ groupReciprocalSum x (a i) :=
      sum_nonneg fun p _ => by positivity
    positivity

lemma sum_freshWeight_le_one (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (I : Finset (Fin K)) :
    ∑ T ∈ freshTuples x a I, freshWeight x a I T ≤ 1 := by
  unfold freshTuples freshWeight
  rw [← Finset.prod_univ_sum (fun i => if i ∈ I then ({1} : Finset ℕ) else primeGroup x (a i))
    (fun i (j : ℕ) => if i ∈ I then (1 : ℝ) else 1 / ((j : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_le_one (fun i _ => ?_) fun i _ => ?_
  · refine sum_nonneg fun p _ => ?_
    split_ifs
    · norm_num
    · have : 0 ≤ groupReciprocalSum x (a i) := sum_nonneg fun p _ => by positivity
      positivity
  · by_cases hi : i ∈ I
    · simp [hi]
    · simp only [hi, if_false]
      have hV : groupReciprocalSum x (a i) = ∑ p ∈ primeGroup x (a i), 1 / (p : ℝ) := rfl
      rw [show ∑ p ∈ primeGroup x (a i), 1 / ((p : ℝ) * groupReciprocalSum x (a i)) =
          (∑ p ∈ primeGroup x (a i), 1 / (p : ℝ)) / groupReciprocalSum x (a i) by
        rw [sum_div]; refine sum_congr rfl fun p _ => by rw [div_div], ← hV]
      exact div_self_le_one _

lemma mem_freshTuples_pos {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {I : Finset (Fin K)}
    {T : Fin K → ℕ} (hT : T ∈ freshTuples x a I) (i : Fin K) : 0 < T i := by
  have := Fintype.mem_piFinset.1 hT i
  split_ifs at this with hi
  · simp at this; omega
  · exact pos_of_mem_primeGroup this

/-! ## Counting and asymptotics -/

lemma card_primeGroup_le (x b : ℝ) : ((primeGroup x b).card : ℝ) ≤ exp (2 * log x ^ b) + 1 := by
  unfold primeGroup
  have h1 := card_filter_le (range (⌊exp (2 * log x ^ b)⌋₊ + 1))
    (fun p : ℕ => p.Prime ∧ exp (log x ^ b) ≤ (p : ℝ))
  rw [card_range] at h1
  have h2 : ((⌊exp (2 * log x ^ b)⌋₊ : ℕ) : ℝ) ≤ exp (2 * log x ^ b) := Nat.floor_le (exp_pos _).le
  have h3 : (((range (⌊exp (2 * log x ^ b)⌋₊ + 1)).filter
      (fun p : ℕ => p.Prime ∧ exp (log x ^ b) ≤ (p : ℝ))).card : ℝ) ≤
      ((⌊exp (2 * log x ^ b)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

lemma card_zTuples_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (I : Finset (Fin K)) (i₀ : Fin K)
    (B : ℝ) (hB1 : 1 ≤ B) (hB : ∀ i ∈ I, i ≠ i₀ → exp (2 * log x ^ a i) + 1 ≤ B) :
    ((zTuples x a I i₀).card : ℝ) ≤ B ^ K := by
  unfold zTuples
  rw [Fintype.card_piFinset]
  push_cast
  calc ∏ i, ((if i ∈ I ∧ i ≠ i₀ then primeGroup x (a i) else {1}).card : ℝ)
      ≤ ∏ _i : Fin K, B := by
        refine prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        split_ifs with h
        · exact (card_primeGroup_le x (a i)).trans (hB i h.1 h.2)
        · simpa using hB1
    _ = B ^ K := by simp

/-- `C log L + D ≤ ε L^a` eventually, for `a, ε > 0`. -/
lemma eventually_log_le_rpow {a : ℝ} (ha : 0 < a) (C D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, C * log L + D ≤ ε * L ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := ε / (2 * (|C| + 1))) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * |D| / ε)
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with L hL1 hL2 hL3
  have hpos : 0 ≤ L ^ a := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos] at hL1
  have hlog : 0 ≤ log L := log_nonneg hL3
  rw [abs_of_nonneg hlog] at hL1
  have hC : C * log L ≤ |C| * log L := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hC2 : |C| * log L ≤ |C| * (ε / (2 * (|C| + 1)) * L ^ a) :=
    mul_le_mul_of_nonneg_left hL1 (abs_nonneg C)
  have hC3 : |C| * (ε / (2 * (|C| + 1)) * L ^ a) ≤ ε / 2 * L ^ a := by
    have : |C| / (|C| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc |C| * (ε / (2 * (|C| + 1)) * L ^ a) = (|C| / (|C| + 1)) * (ε / 2 * L ^ a) := by
          field_simp
      _ ≤ 1 * (ε / 2 * L ^ a) := by gcongr
      _ = ε / 2 * L ^ a := one_mul _
  have hD : D ≤ ε / 2 * L ^ a := by
    have : 2 * |D| / ε * ε = 2 * |D| := by field_simp
    have h' : 2 * |D| ≤ ε * L ^ a := by
      calc 2 * |D| = 2 * |D| / ε * ε := this.symm
        _ ≤ L ^ a * ε := by gcongr
        _ = ε * L ^ a := mul_comm _ _
    linarith [le_abs_self D]
  linarith

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102E: fattened goodness ([21] Lemma 3.2 with doubled thresholds)

A ratio failing goodness stays "weakly bad" (thresholds `2 Y^{-0.7}` and `200 e^{-L^{a}}`) on a
whole window `[r − ε, r + ε]` once `ε` is below the reciprocal of every test integer; the weakly
bad set still has measure `≤ exp(−L^{0.1}/4)` (D's proof of Lemma 3.2 with the constants doubled).
Goodness depends only on the unordered lists (`isGoodRatio_congr`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots ArtinPrimitiveRoots.L102D

/-! ## The circle norm is `1`-Lipschitz -/

lemma circNorm_add_le (t s : ℝ) : circNorm (t + s) ≤ circNorm t + |s| := by
  unfold circNorm
  calc |t + s - (round (t + s) : ℝ)| ≤ |t + s - ((round t : ℤ) : ℝ)| := round_le (t + s) (round t)
    _ = |(t - round t) + s| := by ring_nf
    _ ≤ |t - round t| + |s| := abs_add_le _ _

lemma circNorm_mul_le (n r r' : ℝ) : circNorm (n * r') ≤ circNorm (n * r) + |n| * |r' - r| := by
  have := circNorm_add_le (n * r) (n * (r' - r))
  rw [show n * r + n * (r' - r) = n * r' by ring, abs_mul] at this
  exact this

/-! ## The weak (fattened) tests -/

/-- Test (i) with the threshold doubled. -/
def GoodTestOneW {K M : ℕ} (Y : ℝ) (ℓ : Fin K → Fin M → ℕ) (r : ℝ) : Prop :=
  ∀ o : Fin K → Fin M, ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) →
    2 * Y ^ (-0.7 : ℝ) < circNorm (((l * omitProd ℓ o : ℕ) : ℝ) * r)

/-- The separation failure of test (ii) with the threshold doubled. -/
def SepFailsW (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) (I : Finset (Fin K))
    (i₀ : Fin K) (T : Fin K → ℕ) (r : ℝ) : Prop :=
  ∃ o o' : Fin K → Fin M, ∃ Z Z' : Fin K → ℕ, Z ∈ zTuples x a I i₀ ∧ Z' ∈ zTuples x a I i₀ ∧
    omitProd ℓ o * ∏ i, Z i ≠ omitProd ℓ o' * ∏ i, Z' i ∧
    circNorm (((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
      ((∏ i, T i : ℕ) : ℤ) : ℤ) * r) < 200 * exp (-(log x ^ a i₀))

open Classical in
/-- Test (ii) with the separation threshold doubled. -/
def GoodTestTwoW (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) (r : ℝ) : Prop :=
  ∀ I : Finset (Fin K), ∀ hI : I.Nonempty,
    ∑ T ∈ freshTuples x a I,
      freshWeight x a I T * (if SepFailsW x a ℓ I (I.max' hI) T r then 1 else 0) ≤
      exp (-(log x ^ a (I.max' hI)) / 4)

/-- Weak goodness. -/
def IsGoodRatioW (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) (r : ℝ) : Prop :=
  GoodTestOneW Y ℓ r ∧ GoodTestTwoW x a ℓ r

/-- **Fattening.** If `r` fails goodness and `|r' − r| ≤ ε` with `ε` times every test integer
below the corresponding threshold, then `r'` fails weak goodness. -/
lemma not_goodW_of_not_good {x Y ε r r' : ℝ} {K M : ℕ} {a : Fin K → ℝ}
    {ℓ : Fin K → Fin M → ℕ}
    (h1 : ∀ o : Fin K → Fin M, ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) →
      ((l * omitProd ℓ o : ℕ) : ℝ) * ε ≤ Y ^ (-0.7 : ℝ))
    (h2 : ∀ I : Finset (Fin K), ∀ i₀ : Fin K, ∀ o o' : Fin K → Fin M, ∀ Z Z' T : Fin K → ℕ,
      Z ∈ zTuples x a I i₀ → Z' ∈ zTuples x a I i₀ → T ∈ freshTuples x a I →
      |(((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
        ((∏ i, T i : ℕ) : ℤ) : ℤ) : ℝ)| * ε ≤ 100 * exp (-(log x ^ a i₀)))
    (hr : |r' - r| ≤ ε) (hbad : ¬ IsGoodRatio x Y a ℓ r) : ¬ IsGoodRatioW x Y a ℓ r' := by
  classical
  intro hW
  apply hbad
  refine ⟨fun o l hl1 hlY => ?_, fun I hI => ?_⟩
  · have hW1 := hW.1 o l hl1 hlY
    have hlip := circNorm_mul_le (((l * omitProd ℓ o : ℕ) : ℝ)) r r'
    have hn : |(((l * omitProd ℓ o : ℕ) : ℝ))| * |r' - r| ≤ Y ^ (-0.7 : ℝ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)).trans (h1 o l hl1 hlY)
    linarith
  · refine le_trans ?_ (hW.2 I hI)
    refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left ?_ (freshWeight_nonneg x a I T)
    by_cases hs : SepFails x a ℓ I (I.max' hI) T r
    · rw [if_pos hs, if_pos]
      obtain ⟨o, o', Z, Z', hZ, hZ', hne, hlt⟩ := hs
      refine ⟨o, o', Z, Z', hZ, hZ', hne, ?_⟩
      have hlip := circNorm_mul_le ((((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) -
        ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) * ((∏ i, T i : ℕ) : ℤ) : ℤ) : ℝ)) r r'
      have hb := h2 I (I.max' hI) o o' Z Z' T hZ hZ' hT
      have hn := (mul_le_mul_of_nonneg_left hr (abs_nonneg _)).trans hb
      linarith
    · rw [if_neg hs]; split_ifs <;> norm_num

/-! ## The measure of the weakly bad set -/

lemma volume_not_goodTestOneW {K M : ℕ} (Y : ℝ) (hY : 0 < Y) (ℓ : Fin K → Fin M → ℕ)
    (hℓ : ∀ i j, 0 < ℓ i j) :
    volume ({r | ¬ GoodTestOneW Y ℓ r} ∩ Set.Ioc 0 1) ≤
      ENNReal.ofReal ((M : ℝ) ^ K * Y ^ (0.2 : ℝ) * (2 * (2 * Y ^ (-0.7 : ℝ)))) := by
  set Lm := ⌊Y ^ (0.2 : ℝ)⌋₊
  have hsub : {r | ¬ GoodTestOneW Y ℓ r} ∩ Set.Ioc 0 1 ⊆
      ⋃ o ∈ (univ : Finset (Fin K → Fin M)), ⋃ l ∈ Icc 1 Lm,
        ({r : ℝ | circNorm ((((l * omitProd ℓ o : ℕ) : ℤ) : ℝ) * r) ≤ 2 * Y ^ (-0.7 : ℝ)} ∩
          Set.Ioc 0 1) := by
    rintro r ⟨hr, hr01⟩
    simp only [GoodTestOneW, Set.mem_ofPred_eq, not_forall, not_lt] at hr
    obtain ⟨o, l, hl1, hlY, hle⟩ := hr
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_univ, mem_Icc,
      exists_true_left]
    refine ⟨o, l, ⟨hl1, Nat.le_floor hlY⟩, ?_, hr01⟩
    simpa using hle
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun o _ => measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ o : Fin K → Fin M, ∀ l ∈ Icc 1 Lm,
      volume ({r : ℝ | circNorm ((((l * omitProd ℓ o : ℕ) : ℤ) : ℝ) * r) ≤
        2 * Y ^ (-0.7 : ℝ)} ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * (2 * Y ^ (-0.7 : ℝ))) := by
    intro o l hl
    apply volume_circNorm_le
    have : 0 < l * omitProd ℓ o := Nat.mul_pos (mem_Icc.1 hl).1 (omitProd_pos ℓ hℓ o)
    exact_mod_cast this.ne'
  refine (Finset.sum_le_sum fun o _ => Finset.sum_le_sum (hterm o)).trans ?_
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Nat.card_Icc,
    add_tsub_cancel_right, nsmul_eq_mul]
  have hLm : (Lm : ℝ) ≤ Y ^ (0.2 : ℝ) := Nat.floor_le (by positivity)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have h7 : 0 ≤ 2 * (2 * Y ^ (-0.7 : ℝ)) := by positivity
  have hMK : (0 : ℝ) ≤ (M : ℝ) ^ K := by positivity
  calc (M : ℝ) ^ K * ((Lm : ℝ) * (2 * (2 * Y ^ (-0.7 : ℝ))))
      ≤ (M : ℝ) ^ K * (Y ^ (0.2 : ℝ) * (2 * (2 * Y ^ (-0.7 : ℝ)))) := by gcongr
    _ = _ := by ring

lemma measurableSet_sepFailsW (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    (I : Finset (Fin K)) (i₀ : Fin K) (T : Fin K → ℕ) :
    MeasurableSet {r | SepFailsW x a ℓ I i₀ T r} := by
  refine measurableSet_setOfPred.2 ?_
  unfold SepFailsW
  refine Measurable.exists fun o => Measurable.exists fun o' => Measurable.exists fun Z =>
    Measurable.exists fun Z' => measurable_const.and (measurable_const.and
      (measurable_const.and (measurableSet_setOfPred.1 (measurableSet_circNorm_lt _ _))))

lemma volume_sepFailsW_le (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    (I : Finset (Fin K)) (i₀ : Fin K) (T : Fin K → ℕ) (hT : ∀ i, 0 < T i) :
    volume ({r | SepFailsW x a ℓ I i₀ T r} ∩ Set.Ioc 0 1) ≤
      ENNReal.ofReal (((M : ℝ) ^ K) ^ 2 * ((zTuples x a I i₀).card : ℝ) ^ 2 *
        (2 * (200 * exp (-(log x ^ a i₀))))) := by
  classical
  set zT := zTuples x a I i₀
  set c := 200 * exp (-(log x ^ a i₀))
  set n : (Fin K → Fin M) × (Fin K → Fin M) × (Fin K → ℕ) × (Fin K → ℕ) → ℤ := fun q =>
    (((omitProd ℓ q.1 * ∏ i, q.2.2.1 i : ℕ) : ℤ) - ((omitProd ℓ q.2.1 * ∏ i, q.2.2.2 i : ℕ) : ℤ)) *
      ((∏ i, T i : ℕ) : ℤ)
  set Q := ((univ : Finset (Fin K → Fin M)) ×ˢ (univ : Finset (Fin K → Fin M)) ×ˢ zT ×ˢ zT).filter
    fun q => omitProd ℓ q.1 * ∏ i, q.2.2.1 i ≠ omitProd ℓ q.2.1 * ∏ i, q.2.2.2 i
  have hsub : {r | SepFailsW x a ℓ I i₀ T r} ∩ Set.Ioc 0 1 ⊆
      ⋃ q ∈ Q, ({r : ℝ | circNorm ((n q : ℝ) * r) ≤ c} ∩ Set.Ioc 0 1) := by
    rintro r ⟨⟨o, o', Z, Z', hZ, hZ', hne, hlt⟩, hr⟩
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨(o, o', Z, Z'), ?_, ?_, hr⟩
    · simp [Q, hZ, hZ', hne, zT]
    · exact hlt.le
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ q ∈ Q, volume ({r : ℝ | circNorm ((n q : ℝ) * r) ≤ c} ∩ Set.Ioc 0 1) ≤
      ENNReal.ofReal (2 * c) := by
    intro q hq
    apply volume_circNorm_le
    have hne := (Finset.mem_filter.1 hq).2
    have hTp : (0 : ℤ) < ((∏ i, T i : ℕ) : ℤ) := by
      exact_mod_cast prod_pos fun i _ => hT i
    refine mul_ne_zero ?_ hTp.ne'
    intro h
    apply hne
    exact_mod_cast sub_eq_zero.1 h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hQ : (Q.card : ℝ) ≤ ((M : ℝ) ^ K) ^ 2 * (zT.card : ℝ) ^ 2 := by
    have : Q.card ≤ (M ^ K) ^ 2 * zT.card ^ 2 := by
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      simp only [card_product, card_univ, Fintype.card_fun, Fintype.card_fin]
      ring
    exact_mod_cast this
  have hc : 0 ≤ 2 * c := by positivity
  nlinarith

open Classical in
lemma volume_testTwoW_I_le (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    (I : Finset (Fin K)) (i₀ : Fin K) :
    volume ({r | exp (-(log x ^ a i₀) / 4) < ∑ T ∈ freshTuples x a I,
        freshWeight x a I T * (if SepFailsW x a ℓ I i₀ T r then 1 else 0)} ∩ Set.Ioc 0 1) ≤
      ENNReal.ofReal ((((M : ℝ) ^ K) ^ 2 * ((zTuples x a I i₀).card : ℝ) ^ 2 *
        (2 * (200 * exp (-(log x ^ a i₀))))) / exp (-(log x ^ a i₀) / 4)) := by
  set ε := ((M : ℝ) ^ K) ^ 2 * ((zTuples x a I i₀).card : ℝ) ^ 2 *
    (2 * (200 * exp (-(log x ^ a i₀))))
  have h := volume_weighted_gt_le (freshTuples x a I) (freshWeight x a I)
    (fun T _ => freshWeight_nonneg x a I T) (fun T => {r | SepFailsW x a ℓ I i₀ T r})
    (fun T _ => measurableSet_sepFailsW x a ℓ I i₀ T) ε (exp (-(log x ^ a i₀) / 4))
    (exp_pos _) (fun T hT => volume_sepFailsW_le x a ℓ I i₀ T (mem_freshTuples_pos hT))
  refine (le_of_eq_of_le ?_ h).trans (ENNReal.ofReal_le_ofReal ?_)
  · congr 2
  · have hε : 0 ≤ ε := by positivity
    have := sum_freshWeight_le_one x a I
    have hsum0 : 0 ≤ ∑ T ∈ freshTuples x a I, freshWeight x a I T :=
      sum_nonneg fun T _ => freshWeight_nonneg x a I T
    gcongr
    calc (∑ T ∈ freshTuples x a I, freshWeight x a I T) * ε ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε

/-- **Lemma 3.2 for weak goodness.** -/
theorem goodness_measureW {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a)
    (hab : ∀ i, (0.1 : ℝ) < a i) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ M : ℕ, (M : ℝ) ≤ log x → ∀ Y : ℝ, 0 < Y →
      log x ^ (0.1 : ℝ) - 2 ≤ log Y → ∀ ℓ : Fin K → Fin M → ℕ,
        (∀ i j, ℓ i j ∈ primeGroup x (a i)) →
        volume ({r | ¬ IsGoodRatioW x Y a ℓ r} ∩ Set.Ioc 0 1) ≤
          ENNReal.ofReal (exp (-(log x ^ (0.1 : ℝ)) / 4)) := by
  classical
  have hE1 : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j →
      log 2 + 2 * L ^ a i ≤ L ^ a j / (16 * K) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · have hK0 : (0 : ℝ) < K := by exact_mod_cast Fin.pos i
      have hK : (0 : ℝ) < 16 * K := by positivity
      have hj : 0 < a j := (by norm_num : (0 : ℝ) < 0.1).trans (hab j)
      have e1 := eventually_rpow_le_rpow hij (ε := 1 / (64 * K)) (by positivity)
      have e2 := eventually_log_le_rpow hj 0 (log 2) (ε := 1 / (32 * K)) (by positivity)
      filter_upwards [e1, e2] with L h1 h2 _
      have : L ^ a j / (16 * K) = 2 * (1 / (64 * K) * L ^ a j) + 1 / (32 * K) * L ^ a j := by
        field_simp; ring
      rw [this]; linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  have hE2 : ∀ᶠ L : ℝ in Filter.atTop, ∀ j : Fin K, 2 * K * log L + log 400 ≤ L ^ a j / 8 := by
    refine Filter.eventually_all.2 fun j => ?_
    have hj : 0 < a j := (by norm_num : (0 : ℝ) < 0.1).trans (hab j)
    filter_upwards [eventually_log_le_rpow hj (2 * K) (log 400) (ε := 1 / 8) (by norm_num)]
      with L h
    linarith
  have hE3 : ∀ᶠ L : ℝ in Filter.atTop,
      K * log L + log (4 * exp 1 + 2 ^ K) ≤ 1 / 4 * L ^ (0.1 : ℝ) :=
    eventually_log_le_rpow (by norm_num) _ _ (by norm_num)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1
    (hE1.and (hE2.and (hE3.and (Filter.eventually_ge_atTop 1))))
  refine ⟨exp (max L₀ 1), fun x hx M hM Y hY hYL ℓ hℓ => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  have hL : max L₀ 1 ≤ log x := (Real.le_log_iff_exp_le hxpos).2 hx
  obtain ⟨h1, h2, h3, hL1⟩ := hL₀ (log x) (le_of_max_le_left hL)
  set L := log x with hLdef
  have hLpos : 0 < L := by linarith
  have hℓpos : ∀ i j, 0 < ℓ i j := fun i j => pos_of_mem_primeGroup (hℓ i j)
  have hL01 : ∀ j, L ^ (0.1 : ℝ) ≤ L ^ a j := fun j =>
    Real.rpow_le_rpow_of_exponent_le hL1 (hab j).le
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMK : (M : ℝ) ^ K ≤ L ^ K := pow_le_pow_left₀ hM0 hM K
  set τ0 := exp (-(L ^ (0.1 : ℝ)) / 2)
  have hI : ∀ I : Finset (Fin K), ∀ hI : I.Nonempty,
      volume ({r | exp (-(L ^ a (I.max' hI)) / 4) < ∑ T ∈ freshTuples x a I,
        freshWeight x a I T * (if SepFailsW x a ℓ I (I.max' hI) T r then 1 else 0)} ∩
          Set.Ioc 0 1) ≤ ENNReal.ofReal τ0 := by
    intro I hI
    set i₀ := I.max' hI
    refine (volume_testTwoW_I_le x a ℓ I i₀).trans (ENNReal.ofReal_le_ofReal ?_)
    set A := L ^ a i₀
    have hA0 : 0 ≤ A := by positivity
    have hK : 0 < K := Fin.pos i₀
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    set B := exp (A / (16 * K))
    have hB1 : 1 ≤ B := one_le_exp (by positivity)
    have hB : ∀ i ∈ I, i ≠ i₀ → exp (2 * log x ^ a i) + 1 ≤ B := by
      intro i hiI hne
      have hlt : i < i₀ := lt_of_le_of_ne (I.le_max' i hiI) hne
      have := h1 i i₀ (ha hlt)
      have hge : 1 ≤ exp (2 * L ^ a i) := one_le_exp (by positivity)
      calc exp (2 * log x ^ a i) + 1 ≤ 2 * exp (2 * L ^ a i) := by linarith
        _ = exp (log 2 + 2 * L ^ a i) := by rw [exp_add, exp_log (by norm_num)]
        _ ≤ B := exp_le_exp.2 this
    have hcard := card_zTuples_le x a I i₀ B hB1 hB
    have hBK : B ^ K = exp (A / 16) := by
      rw [← exp_nat_mul]; congr 1; field_simp
    have hc0 : (0 : ℝ) ≤ (zTuples x a I i₀).card := Nat.cast_nonneg _
    have hcard2 : ((zTuples x a I i₀).card : ℝ) ^ 2 ≤ exp (A / 8) := by
      calc ((zTuples x a I i₀).card : ℝ) ^ 2 ≤ (B ^ K) ^ 2 := pow_le_pow_left₀ hc0 hcard 2
        _ = exp (A / 8) := by rw [hBK, ← exp_nat_mul]; congr 1; push_cast; ring
    have hM2 : ((M : ℝ) ^ K) ^ 2 ≤ exp (2 * K * log L) := by
      calc ((M : ℝ) ^ K) ^ 2 ≤ (L ^ K) ^ 2 := pow_le_pow_left₀ (by positivity) hMK 2
        _ = exp (2 * K * log L) := by
          rw [← pow_mul, ← exp_log (pow_pos hLpos (K * 2)), Real.log_pow]
          congr 1; push_cast; ring
    have hE := h2 i₀
    rw [div_le_iff₀ (exp_pos _)]
    calc ((M : ℝ) ^ K) ^ 2 * ((zTuples x a I i₀).card : ℝ) ^ 2 *
          (2 * (200 * exp (-(log x ^ a i₀))))
        ≤ exp (2 * K * log L) * exp (A / 8) * (400 * exp (-A)) := by
          have : 2 * (200 * exp (-(log x ^ a i₀))) = 400 * exp (-A) := by ring
          rw [this]
          gcongr
      _ = exp (2 * K * log L + log 400 + A / 8 - A) := by
          rw [show 2 * K * log L + log 400 + A / 8 - A =
            2 * K * log L + A / 8 + log 400 + -A by ring, exp_add, exp_add, exp_add,
            exp_log (by norm_num)]
          ring
      _ ≤ exp (-(L ^ (0.1 : ℝ)) / 2 + -A / 4) := by
          apply exp_le_exp.2
          have := hL01 i₀
          linarith
      _ = τ0 * exp (-A / 4) := by rw [exp_add]
  set S2 : Finset (Fin K) → Set ℝ := fun I => if hI : I.Nonempty then
      {r | exp (-(L ^ a (I.max' hI)) / 4) < ∑ T ∈ freshTuples x a I,
        freshWeight x a I T * (if SepFailsW x a ℓ I (I.max' hI) T r then 1 else 0)} ∩
          Set.Ioc 0 1 else ∅
  have hsub : {r | ¬ IsGoodRatioW x Y a ℓ r} ∩ Set.Ioc 0 1 ⊆
      ({r | ¬ GoodTestOneW Y ℓ r} ∩ Set.Ioc 0 1) ∪
        ⋃ I ∈ (univ : Finset (Finset (Fin K))), S2 I := by
    rintro r ⟨hr, hr01⟩
    simp only [IsGoodRatioW, Set.mem_ofPred_eq, not_and_or] at hr
    rcases hr with hr | hr
    · exact Or.inl ⟨hr, hr01⟩
    · right
      simp only [GoodTestTwoW, not_forall, not_le] at hr
      obtain ⟨I, hI, hlt⟩ := hr
      simp only [Set.mem_iUnion]
      refine ⟨I, mem_univ _, ?_⟩
      simp only [S2, dif_pos hI]
      exact ⟨hlt, hr01⟩
  have hS2 : ∀ I ∈ (univ : Finset (Finset (Fin K))), volume (S2 I) ≤ ENNReal.ofReal τ0 := by
    intro I _
    by_cases hI' : I.Nonempty
    · simp only [S2, dif_pos hI']; exact hI I hI'
    · simp [S2, dif_neg hI']
  have hT1 := volume_not_goodTestOneW Y hY ℓ hℓpos
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add hT1 ((measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum hS2))).trans ?_
  rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hY1 : Y ^ (0.2 : ℝ) * (2 * (2 * Y ^ (-0.7 : ℝ))) ≤ 4 * exp 1 * τ0 := by
    have : Y ^ (0.2 : ℝ) * Y ^ (-0.7 : ℝ) = exp (-(1 / 2) * log Y) := by
      rw [← Real.rpow_add hY, Real.rpow_def_of_pos hY]; congr 1; norm_num; ring
    calc Y ^ (0.2 : ℝ) * (2 * (2 * Y ^ (-0.7 : ℝ))) = 4 * exp (-(1 / 2) * log Y) := by
          rw [← this]; ring
      _ ≤ 4 * exp (1 + -(L ^ (0.1 : ℝ)) / 2) := by
          gcongr; linarith
      _ = 4 * exp 1 * τ0 := by rw [exp_add]; ring
  have hLK1 : 1 ≤ L ^ K := one_le_pow₀ hL1
  have hfin : (4 * exp 1 + 2 ^ K) * L ^ K ≤ exp (1 / 4 * L ^ (0.1 : ℝ)) := by
    have e1 : L ^ K = exp (K * log L) := by rw [← Real.log_pow, exp_log (pow_pos hLpos K)]
    calc (4 * exp 1 + 2 ^ K) * L ^ K = exp (K * log L + log (4 * exp 1 + 2 ^ K)) := by
          rw [exp_add, exp_log (by positivity), e1]; ring
      _ ≤ _ := exp_le_exp.2 h3
  have hτ0 : 0 ≤ τ0 := (exp_pos _).le
  calc (M : ℝ) ^ K * Y ^ (0.2 : ℝ) * (2 * (2 * Y ^ (-0.7 : ℝ))) + ((2 ^ K : ℕ) : ℝ) * τ0
      ≤ L ^ K * (4 * exp 1 * τ0) + 2 ^ K * L ^ K * τ0 := by
        rw [mul_assoc]
        push_cast
        have : (2 : ℝ) ^ K ≤ 2 ^ K * L ^ K := le_mul_of_one_le_right (by positivity) hLK1
        gcongr
    _ = ((4 * exp 1 + 2 ^ K) * L ^ K) * τ0 := by ring
    _ ≤ exp (1 / 4 * L ^ (0.1 : ℝ)) * τ0 := by gcongr
    _ = exp (-(L ^ (0.1 : ℝ)) / 4) := by
        rw [← exp_add]; congr 1; ring

/-! ## Goodness depends only on the unordered lists -/

lemma prod_erase_eq_of_range {M : ℕ} {f g : Fin M → ℕ} (hf : Function.Injective f)
    (hg : Function.Injective g) (h : Set.range f = Set.range g) (o o' : Fin M)
    (ho : f o = g o') : ∏ j ∈ univ.erase o, f j = ∏ j ∈ univ.erase o', g j := by
  classical
  have him : univ.image f = univ.image g := by
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      have : f j ∈ Set.range g := h ▸ ⟨j, rfl⟩
      exact this
    · rintro ⟨j, rfl⟩
      have : g j ∈ Set.range f := h.symm ▸ ⟨j, rfl⟩
      exact this
  have e1 : ∏ j ∈ univ.erase o, f j = ∏ v ∈ (univ.erase o).image f, v :=
    (prod_image (f := fun v => v) hf.injOn).symm
  have e2 : ∏ j ∈ univ.erase o', g j = ∏ v ∈ (univ.erase o').image g, v :=
    (prod_image (f := fun v => v) hg.injOn).symm
  rw [e1, e2, image_erase hf, image_erase hg, him, ho]

lemma exists_omitProd_eq {K M : ℕ} {ℓ ℓ' : Fin K → Fin M → ℕ}
    (hinj : ∀ i, Function.Injective (ℓ i)) (hinj' : ∀ i, Function.Injective (ℓ' i))
    (hran : ∀ i, Set.range (ℓ' i) = Set.range (ℓ i)) (o : Fin K → Fin M) :
    ∃ o' : Fin K → Fin M, omitProd ℓ' o = omitProd ℓ o' := by
  have hex : ∀ i, ∃ j, ℓ i j = ℓ' i (o i) := fun i => by
    have : ℓ' i (o i) ∈ Set.range (ℓ i) := hran i ▸ ⟨o i, rfl⟩
    exact this
  choose o' ho' using hex
  refine ⟨o', ?_⟩
  unfold omitProd
  exact prod_congr rfl fun i _ =>
    prod_erase_eq_of_range (hinj' i) (hinj i) (hran i) (o i) (o' i) (ho' i).symm

lemma goodTestOne_imp {K M : ℕ} {ℓ ℓ' : Fin K → Fin M → ℕ}
    (hinj : ∀ i, Function.Injective (ℓ i)) (hinj' : ∀ i, Function.Injective (ℓ' i))
    (hran : ∀ i, Set.range (ℓ' i) = Set.range (ℓ i)) {Y r : ℝ} (h : GoodTestOne Y ℓ r) :
    GoodTestOne Y ℓ' r := by
  intro o l hl hlY
  obtain ⟨o', ho'⟩ := exists_omitProd_eq hinj hinj' hran o
  rw [ho']
  exact h o' l hl hlY

lemma sepFails_imp {x : ℝ} {K M : ℕ} {a : Fin K → ℝ} {ℓ ℓ' : Fin K → Fin M → ℕ}
    (hinj : ∀ i, Function.Injective (ℓ i)) (hinj' : ∀ i, Function.Injective (ℓ' i))
    (hran : ∀ i, Set.range (ℓ' i) = Set.range (ℓ i)) {I : Finset (Fin K)} {i₀ : Fin K}
    {T : Fin K → ℕ} {r : ℝ} (h : SepFails x a ℓ' I i₀ T r) : SepFails x a ℓ I i₀ T r := by
  obtain ⟨o, o', Z, Z', hZ, hZ', hne, hlt⟩ := h
  obtain ⟨p, hp⟩ := exists_omitProd_eq hinj hinj' hran o
  obtain ⟨p', hp'⟩ := exists_omitProd_eq hinj hinj' hran o'
  rw [hp, hp'] at hne hlt
  exact ⟨p, p', Z, Z', hZ, hZ', hne, hlt⟩

lemma sepFails_iff {x : ℝ} {K M : ℕ} {a : Fin K → ℝ} {ℓ ℓ' : Fin K → Fin M → ℕ}
    (hinj : ∀ i, Function.Injective (ℓ i)) (hinj' : ∀ i, Function.Injective (ℓ' i))
    (hran : ∀ i, Set.range (ℓ' i) = Set.range (ℓ i)) (I : Finset (Fin K)) (i₀ : Fin K)
    (T : Fin K → ℕ) (r : ℝ) : SepFails x a ℓ I i₀ T r ↔ SepFails x a ℓ' I i₀ T r :=
  ⟨sepFails_imp hinj' hinj (fun i => (hran i).symm), sepFails_imp hinj hinj' hran⟩

/-- **Goodness is a property of the unordered lists.** -/
theorem isGoodRatio_congr {x Y : ℝ} {K M : ℕ} {a : Fin K → ℝ} {ℓ ℓ' : Fin K → Fin M → ℕ}
    (hinj : ∀ i, Function.Injective (ℓ i)) (hinj' : ∀ i, Function.Injective (ℓ' i))
    (hran : ∀ i, Set.range (ℓ' i) = Set.range (ℓ i)) (r : ℝ) :
    IsGoodRatio x Y a ℓ r ↔ IsGoodRatio x Y a ℓ' r := by
  classical
  have h2 : GoodTestTwo x a ℓ r ↔ GoodTestTwo x a ℓ' r := by
    unfold GoodTestTwo
    simp only [sepFails_iff (x := x) (a := a) hinj hinj' hran]
  exact and_congr ⟨goodTestOne_imp hinj hinj' hran,
    goodTestOne_imp hinj' hinj (fun i => (hran i).symm)⟩ h2

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102K: the Kloosterman fourth moment ([21] Lemma 3.3, (3.24))

`K_m(h, k) = ∑_{y ∈ (ℤ/m)ˣ} e((h y + k y⁻¹)/m)`. Orthogonality gives
`∑_{h,k} |K_m(h,k)|⁴ = m² T_m`, where `T_m` counts unit quadruples with equal sums and equal
inverse sums, and `T_m ≤ 2 τ₃(m) m²`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset

noncomputable section

/-- `#{x ∈ ℤ/m : d ∣ x.val} = m/d` for `d ∣ m`. -/
lemma card_dvd_val (m d : ℕ) [NeZero m] (hd0 : 0 < d) (hd : d ∣ m) :
    #{x : ZMod m | d ∣ x.val} = m / d := by
  classical
  have him : (Finset.univ.filter fun x : ZMod m => d ∣ x.val).image ZMod.val =
      (Finset.range (m / d)).image (· * d) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨x, ⟨j, hj⟩, rfl⟩
      refine ⟨j, ?_, by rw [hj, mul_comm]⟩
      have hlt := ZMod.val_lt x
      rw [hj] at hlt
      rw [Nat.lt_div_iff_mul_lt' hd]
      linarith [mul_comm d j]
    · rintro ⟨j, hj, rfl⟩
      have hlt : j * d < m := by
        rw [Nat.lt_div_iff_mul_lt' hd] at hj; rw [mul_comm]; exact hj
      refine ⟨(j * d : ℕ), ?_, ?_⟩
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]; exact Dvd.intro_left j rfl
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have h1 := congrArg Finset.card him
  rw [Finset.card_image_of_injective _ (ZMod.val_injective m),
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hd0 h),
    Finset.card_range] at h1
  exact h1

/-! ### The pointwise bound -/

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the Euler-factor average and the constant `1/ζ(2)`

`P(S) = ∑_{(l,S)=1} μ(l)/l²` and `J(S) = ∑_{d ∣ S} μ(d)/d²` satisfy `J(S) P(S) = 6/π²`, and
`∑_{A ≤ u < B, u ≡ u₀ (S)} ∑_{l ∣ u, (l,S)=1} μ(l)/l = (B − A)/S · P(S) + O(1 + log B)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- `μ(n)/n²`. -/
def mu2 (n : ℕ) : ℝ := (μ n : ℝ) / (n : ℝ) ^ 2

/-- `P(S) = ∑_{(l,S)=1} μ(l)/l²`. -/
def PS (S : ℕ) : ℝ := ∑' n : ℕ, if Nat.Coprime n S then mu2 n else 0

/-- `J(S) = ∑_{d ∣ S} μ(d)/d²`. -/
def JS (S : ℕ) : ℝ := ∑ d ∈ S.divisors, mu2 d

lemma abs_moebius_real_le (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  have := abs_moebius_le_one (n := n)
  rw [← Int.cast_abs]
  exact_mod_cast this

lemma abs_mu2_le (n : ℕ) : |mu2 n| ≤ 1 / (n : ℝ) ^ 2 := by
  rw [mu2, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
  exact div_le_div_of_nonneg_right (abs_moebius_real_le n) (by positivity)

lemma summable_inv_sq : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

lemma summable_of_le_mu2 {f : ℕ → ℝ} (h : ∀ n, |f n| ≤ |mu2 n|) : Summable f :=
  Summable.of_norm_bounded summable_inv_sq fun n => by
    rw [Real.norm_eq_abs]; exact (h n).trans (abs_mu2_le n)

/-- `∑ μ(n)/n² = 6/π²`. -/
theorem tsum_mu2 : ∑' n : ℕ, mu2 n = 6 / π ^ 2 := by
  have h := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_zeta_eq_riemannZeta (by norm_num), riemannZeta_two] at h
  have hL : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 = ((∑' n : ℕ, mu2 n : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1
    ext n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [mu2]
    · rw [LSeries.term_of_ne_zero hn.ne', mu2]
      have : ((n : ℂ) ^ (2 : ℂ)) = ((n : ℝ) ^ 2 : ℝ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; push_cast; ring
      rw [this]; push_cast; ring
  rw [hL] at h
  have hpi0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 : ((∑' n : ℕ, mu2 n : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by
    field_simp
    linear_combination 6 * h
  have h4 : ((6 / π ^ 2 : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by push_cast; ring
  exact_mod_cast h3.trans h4.symm

/-- For squarefree `n ≠ 0` and `d ∣ S`: `d ∣ n ∧ (n/d, S) = 1 ↔ d = (n, S)`. -/
lemma dvd_coprime_iff (n S d : ℕ) (hn : Squarefree n) (hn0 : n ≠ 0) (hdS : d ∣ S) :
    (d ∣ n ∧ Nat.Coprime (n / d) S) ↔ d = Nat.gcd n S := by
  constructor
  · rintro ⟨hdn, hcop⟩
    have hdg : d ∣ Nat.gcd n S := Nat.dvd_gcd hdn hdS
    obtain ⟨e, he⟩ := hdg
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hdn; exact hn0 hdn)
    have hen : e ∣ n / d := by
      have hgn : Nat.gcd n S ∣ n := Nat.gcd_dvd_left n S
      rw [he] at hgn
      obtain ⟨k, hk⟩ := hgn
      rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hd0]
      exact Dvd.intro k rfl
    have heS : e ∣ S := by
      have : e ∣ Nat.gcd n S := by rw [he]; exact Dvd.intro_left d rfl
      exact this.trans (Nat.gcd_dvd_right n S)
    have he1 : e = 1 := Nat.eq_one_of_dvd_coprimes hcop hen heS
    rw [he, he1, mul_one]
  · rintro rfl
    refine ⟨Nat.gcd_dvd_left n S, ?_⟩
    apply Nat.coprime_of_dvd
    intro p hp hpn hpS
    have hg0 : 0 < Nat.gcd n S := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn0)
    have hpn' : p ∣ n := hpn.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n S))
    have hpg : p ∣ Nat.gcd n S := Nat.dvd_gcd hpn' hpS
    have hsq : p * p ∣ n := by
      have := Nat.mul_dvd_mul hpn hpg
      rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left n S)] at this
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hn p hsq))

/-- **`J(S) P(S) = 6/π²`.** -/
theorem JS_mul_PS (S : ℕ) (hS : 0 < S) : JS S * PS S = 6 / π ^ 2 := by
  classical
  set c : ℕ → ℝ := fun n => if Nat.Coprime n S then mu2 n else 0 with hc
  have hcs : Summable c := summable_of_le_mu2 fun n => by
    simp only [c]; split_ifs <;> simp
  let F : ℕ → ℕ → ℝ := fun d n => if d ∣ n ∧ Nat.Coprime (n / d) S then mu2 n else 0
  have hFs : ∀ d, Summable (F d) := fun d => summable_of_le_mu2 fun n => by
    simp only [F]; split_ifs <;> simp
  have hstep : ∀ d ∈ S.divisors, mu2 d * PS S = ∑' n, F d n := by
    intro d hd
    have hdS : d ∣ S := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdS hS
    rw [PS, ← tsum_mul_left]
    have hinj : Function.Injective (fun l : ℕ => d * l) := fun a b h =>
      Nat.eq_of_mul_eq_mul_left hd0 h
    have hsupp : Function.support (F d) ⊆ Set.range (fun l : ℕ => d * l) := by
      intro n hn
      simp only [Function.mem_support, F] at hn
      split_ifs at hn with h
      · exact ⟨n / d, Nat.mul_div_cancel' h.1⟩
      · exact absurd rfl hn
    symm
    rw [← hinj.tsum_eq (f := F d) hsupp]
    · refine tsum_congr fun l => ?_
      simp only [F, Nat.mul_div_cancel_left _ hd0, dvd_mul_right, true_and]
      split_ifs with hl
      · have hdl : Nat.Coprime d l := Nat.Coprime.coprime_dvd_left hdS hl.symm
        simp only [mu2]
        rw [isMultiplicative_moebius.map_mul_of_coprime hdl]
        push_cast; ring
      · ring
  have hsum : ∀ n, ∑ d ∈ S.divisors, F d n = mu2 n := by
    intro n
    by_cases hmu : μ n = 0
    · have : mu2 n = 0 := by simp [mu2, hmu]
      rw [this]
      exact Finset.sum_eq_zero fun d _ => by simp only [F]; split_ifs <;> simp [this]
    · have hsq : Squarefree n := moebius_ne_zero_iff_squarefree.mp hmu
      have hn0 : n ≠ 0 := by rintro rfl; simp at hmu
      rw [Finset.sum_eq_single (Nat.gcd n S)]
      · simp only [F]
        rw [if_pos ((dvd_coprime_iff n S _ hsq hn0 (Nat.gcd_dvd_right n S)).mpr rfl)]
      · intro d hd hne
        simp only [F]
        rw [if_neg]
        intro h
        exact hne ((dvd_coprime_iff n S d hsq hn0 (Nat.dvd_of_mem_divisors hd)).mp h)
      · intro h
        exact absurd (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n S, hS.ne'⟩) h
  calc JS S * PS S = ∑ d ∈ S.divisors, mu2 d * PS S := by rw [JS, Finset.sum_mul]
    _ = ∑ d ∈ S.divisors, ∑' n, F d n := Finset.sum_congr rfl hstep
    _ = ∑' n, ∑ d ∈ S.divisors, F d n := (Summable.tsum_finsetSum fun d _ => hFs d).symm
    _ = ∑' n, mu2 n := tsum_congr hsum
    _ = 6 / π ^ 2 := tsum_mu2

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: `|SL₂(ℤ/S)| = S³ ∑_{d ∣ S} μ(d)/d²` ([21] (3.29))

Unimodular columns are counted by Möbius inversion (`#{d ∣ u, d ∣ v} = (S/d)²`), and each
unimodular column has exactly `S` completions. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- A column `(u, v)` is unimodular iff `(u, v, S) = 1`. -/
lemma exists_completion_iff (S : ℕ) [NeZero S] (u v : ZMod S) :
    (∃ c d : ZMod S, u * d - c * v = 1) ↔ Nat.gcd (Nat.gcd u.val v.val) S = 1 := by
  set g := Nat.gcd (Nat.gcd u.val v.val) S with hg
  constructor
  · rintro ⟨c, d, h⟩
    have hgS : g ∣ S := Nat.gcd_dvd_right _ _
    let π := ZMod.castHom hgS (ZMod g)
    have hu : π u = 0 := by
      have : π u = ((u.val : ℕ) : ZMod g) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val u]
        rw [map_natCast]
      rw [this, ZMod.natCast_eq_zero_iff]
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hv : π v = 0 := by
      have : π v = ((v.val : ℕ) : ZMod g) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val v]
        rw [map_natCast]
      rw [this, ZMod.natCast_eq_zero_iff]
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h1 := congrArg π h
    rw [map_sub, map_mul, map_mul, hu, hv, map_one] at h1
    simp only [zero_mul, mul_zero, sub_zero] at h1
    have h01 : (0 : ZMod g) = 1 := h1
    have := ZMod.natCast_self g
    by_contra hne
    have hg1 : 1 < g ∨ g = 0 := by omega
    rcases hg1 with hg1 | hg0
    · have : Fact (1 < g) := ⟨hg1⟩
      exact zero_ne_one h01
    · have h0 : Nat.gcd (Nat.gcd u.val v.val) S = 0 := hg0
      exact NeZero.ne S (Nat.gcd_eq_zero_iff.mp h0).2
  · intro h1
    -- Bezout in `ℤ`
    have hcop : IsCoprime ((Nat.gcd u.val v.val : ℕ) : ℤ) (S : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]; exact h1
    obtain ⟨a, b, hab⟩ := hcop
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, ((Nat.gcd u.val v.val : ℕ) : ℤ) = x * u.val + y * v.val := by
      refine ⟨Nat.gcdA u.val v.val, Nat.gcdB u.val v.val, ?_⟩
      rw [Nat.gcd_eq_gcd_ab]; ring
    refine ⟨-((a * y : ℤ) : ZMod S), ((a * x : ℤ) : ZMod S), ?_⟩
    have h2 : (((a * (x * u.val + y * v.val) + b * S : ℤ)) : ZMod S) = 1 := by
      rw [← hxy, hab]; simp
    push_cast at h2
    rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
    rw [← h2]; push_cast; ring

/-- A unimodular column has exactly `S` completions. -/
lemma card_completions (S : ℕ) [NeZero S] (u v : ZMod S) (c₀ d₀ : ZMod S)
    (h₀ : u * d₀ - c₀ * v = 1) :
    #((univ : Finset (ZMod S × ZMod S)).filter (fun q => u * q.2 - q.1 * v = 1)) = S := by
  classical
  suffices h : #(univ : Finset (ZMod S)) =
      #((univ : Finset (ZMod S × ZMod S)).filter (fun q => u * q.2 - q.1 * v = 1)) by
    rw [← h, Finset.card_univ, ZMod.card]
  refine Finset.card_bij (fun t _ => (c₀ + t * u, d₀ + t * v)) ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination h₀
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    have e1 : (t - t') * u = 0 := by linear_combination h.1
    have e2 : (t - t') * v = 0 := by linear_combination h.2
    have : t - t' = 0 := by
      have : (t - t') * (u * d₀ - c₀ * v) = 0 := by linear_combination d₀ * e1 - c₀ * e2
      rwa [h₀, mul_one] at this
    exact sub_eq_zero.mp this
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨d₀ * (q.1 - c₀) - c₀ * (q.2 - d₀), Finset.mem_univ _, ?_⟩
    ext
    · simp only
      linear_combination q.1 * h₀ - c₀ * hq
    · simp only
      linear_combination q.2 * h₀ - d₀ * hq

/-- `#{(u, v) : (u, v, S) = 1} = ∑_{d ∣ S} μ(d) (S/d)²`. -/
lemma card_unimodular (S : ℕ) [NeZero S] :
    ((#((univ : Finset (ZMod S × ZMod S)).filter
        (fun p => Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1)) : ℕ) : ℤ) =
      ∑ d ∈ S.divisors, μ d * (((S / d) ^ 2 : ℕ) : ℤ) := by
  classical
  have hS : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  rw [Finset.card_filter, Nat.cast_sum]
  have h1 : ∀ p : ZMod S × ZMod S, (((if Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1 then 1 else 0 :
      ℕ)) : ℤ) = ∑ d ∈ S.divisors, if d ∣ p.1.val ∧ d ∣ p.2.val then μ d else 0 := by
    intro p
    have hg0 : Nat.gcd (Nat.gcd p.1.val p.2.val) S ≠ 0 := (Nat.gcd_pos_of_pos_right _ hS).ne'
    rw [← Finset.sum_filter]
    have hset : S.divisors.filter (fun d => d ∣ p.1.val ∧ d ∣ p.2.val) =
        (Nat.gcd (Nat.gcd p.1.val p.2.val) S).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hdS, _⟩, h1, h2⟩; exact ⟨⟨⟨h1, h2⟩, hdS⟩, hg0⟩
      · rintro ⟨⟨⟨h1, h2⟩, hdS⟩, _⟩; exact ⟨⟨hdS, hS.ne'⟩, h1, h2⟩
    rw [hset, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdS : d ∣ S := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdS hS
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have : (univ : Finset (ZMod S × ZMod S)).filter (fun p => d ∣ p.1.val ∧ d ∣ p.2.val) =
      (univ.filter fun x : ZMod S => d ∣ x.val) ×ˢ (univ.filter fun x : ZMod S => d ∣ x.val) := by
    ext p; simp
  rw [this, Finset.card_product, card_dvd_val S d hd0 hdS]
  push_cast; ring

/-- The matrix entries `((a, c), (b, d))` of `!![a, b; c, d]`. -/
def matPairs (R : Type*) : Matrix (Fin 2) (Fin 2) R ≃ (R × R) × (R × R) where
  toFun M := ((M 0 0, M 1 0), (M 0 1, M 1 1))
  invFun x := !![x.1.1, x.2.1; x.1.2, x.2.2]
  left_inv M := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  right_inv x := rfl

/-- **(3.29)**: `|SL₂(ℤ/S)| = S³ ∑_{d ∣ S} μ(d)/d²`. -/
theorem card_SL2 (S : ℕ) (hS : 0 < S) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) = (S : ℝ) ^ 3 * JS S := by
  classical
  have : NeZero S := ⟨hS.ne'⟩
  -- `SL₂` as quadruples
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) =
      #((univ : Finset ((ZMod S × ZMod S) × (ZMod S × ZMod S))).filter
        (fun x => x.1.1 * x.2.2 - x.2.1 * x.1.2 = 1)) := by
    rw [Nat.card_eq_fintype_card]
    rw [show Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) =
      Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod S) // M.det = 1} from rfl]
    rw [Fintype.card_subtype]
    refine Finset.card_bij (fun M _ => matPairs (ZMod S) M) ?_ ?_ ?_
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
      simp only [matPairs]
      rw [Matrix.det_fin_two] at hM
      linear_combination hM
    · intro M _ M' _ h; exact (matPairs (ZMod S)).injective h
    · intro x hx
      refine ⟨(matPairs (ZMod S)).symm x, ?_, (matPairs (ZMod S)).apply_symm_apply x⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hm : (matPairs (ZMod S)).symm x = !![x.1.1, x.2.1; x.1.2, x.2.2] := rfl
      rw [hm, Matrix.det_fin_two_of]
      linear_combination hx
  -- fibre over the first column
  have h2 : #((univ : Finset ((ZMod S × ZMod S) × (ZMod S × ZMod S))).filter
        (fun x => x.1.1 * x.2.2 - x.2.1 * x.1.2 = 1)) =
      S * #((univ : Finset (ZMod S × ZMod S)).filter
        (fun p => Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1)) := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product, Finset.card_filter,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.card_filter]
    by_cases hp : Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1
    · rw [if_pos hp, mul_one]
      obtain ⟨c₀, d₀, h₀⟩ := (exists_completion_iff S p.1 p.2).mpr hp
      exact card_completions S p.1 p.2 c₀ d₀ h₀
    · rw [if_neg hp, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hp ((exists_completion_iff S p.1 p.2).mp ⟨q.1, q.2, hq⟩)
  rw [h1, h2]
  have h3 := card_unimodular S
  have h4 : ((#((univ : Finset (ZMod S × ZMod S)).filter
      (fun p => Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1)) : ℕ) : ℝ) =
      ∑ d ∈ S.divisors, (μ d : ℝ) * (((S / d) ^ 2 : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) h3
    push_cast at this ⊢
    exact this
  push_cast
  rw [h4, JS, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdS : d ∣ S := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_dvd_of_pos hdS hS
  rw [mu2, Nat.cast_pow, Nat.cast_div hdS hd0.ne']
  field_simp

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102E: the root basis and residue counting in `SL₂(ℤ/S)`

* `rootC u v` (`= c`, `c ≡ −v⁻¹ (mod u)`, `0 ≤ c < u`) and `rootD u v = (1 + v c)/u` complete a
  primitive `(u, v)` to `g = (u c; v d) ∈ SL₂(ℤ)`, and `rootRatio u v = c/u`.
* `crt_column`: for coprime `A₁, A₂` and a primitive `(z₁, N₀)` there are integers `α, β, x, y`
  with `A₁A₂ ∣ uα + cβ ⟺ (A₁ ∣ u ∧ A₂ ∣ u z₁ + c N₀)` and `A₁A₂ ∣ αx + βy − 1`.
* `card_filter_mul_zero_le`: `#{g₀ ∈ SL₂(ℤ/S) : (g₀N)₀₀ = 0} ≤ S²` for every `N`.
* `card_SL2_ge`: `|SL₂(ℤ/S)| ≥ (36/π⁴) S³` (from K's `card_SL2`, `JS_mul_PS`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset
open ArtinPrimitiveRoots

/-! ## The root basis -/

/-- `c ≡ −v⁻¹ (mod u)`, `0 ≤ c < u`. -/
noncomputable def rootC (u v : ℕ) : ℕ := (-(v : ZMod u)⁻¹ : ZMod u).val

/-- `d = (1 + v c)/u`. -/
noncomputable def rootD (u v : ℕ) : ℕ := (1 + v * rootC u v) / u

lemma rootRatio_eq (u v : ℕ) : rootRatio u v = (rootC u v : ℝ) / u := rfl

lemma rootC_lt {u : ℕ} (hu : 0 < u) (v : ℕ) : rootC u v < u := by
  have : NeZero u := ⟨hu.ne'⟩
  exact ZMod.val_lt _

lemma dvd_one_add_rootC {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    u ∣ 1 + v * rootC u v := by
  have : NeZero u := ⟨hu.ne'⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [rootC, ZMod.natCast_zmod_val, mul_neg, ZMod.coe_mul_inv_eq_one v hcop.symm]
  ring

lemma rootDet {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (u : ℤ) * rootD u v - rootC u v * v = 1 := by
  have h := Nat.div_mul_cancel (dvd_one_add_rootC hu hcop)
  have : (u : ℤ) * (rootD u v : ℤ) = 1 + v * rootC u v := by
    unfold rootD; rw [mul_comm]; exact_mod_cast h
  rw [this]; ring

/-- The matrix `(u c; v d)`. -/
noncomputable def rootMat (u v : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(u : ℤ), (rootC u v : ℤ); (v : ℤ), (rootD u v : ℤ)]

lemma rootMat_det {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) : (rootMat u v).det = 1 := by
  rw [Matrix.det_fin_two]; simp only [rootMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  exact rootDet hu hcop

/-- The root element `g ∈ SL₂(ℤ)` (the identity if `(u, v)` is not primitive). -/
noncomputable def rootG (u v : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if h : (rootMat u v).det = 1 then (⟨rootMat u v, h⟩ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
  else 1

lemma rootG_coe {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (rootG u v : Matrix (Fin 2) (Fin 2) ℤ) = rootMat u v := by
  simp [rootG, rootMat_det hu hcop]

lemma rootG_apply {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    rootG u v 0 0 = u ∧ rootG u v 0 1 = rootC u v ∧ rootG u v 1 0 = v ∧
      rootG u v 1 1 = rootD u v := by
  have h := rootG_coe hu hcop
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h] <;> simp [rootMat]

/-! ## The CRT column -/

/-- For coprime `A₁, A₂` and a primitive `(z₁, N₀)`: integers `α, β, x, y` with
`A₁A₂ ∣ uα + cβ ⟺ (A₁ ∣ u ∧ A₂ ∣ u z₁ + c N₀)` and `A₁A₂ ∣ αx + βy − 1`. -/
lemma crt_column {A₁ A₂ : ℕ} (hA : Nat.Coprime A₁ A₂) {z₁ N₀ : ℤ} (hz : IsCoprime z₁ N₀) :
    ∃ α β x y : ℤ, (∀ u c : ℤ, ((A₁ * A₂ : ℕ) : ℤ) ∣ u * α + c * β ↔
        ((A₁ : ℤ) ∣ u ∧ (A₂ : ℤ) ∣ u * z₁ + c * N₀)) ∧
      ((A₁ * A₂ : ℕ) : ℤ) ∣ α * x + β * y - 1 := by
  have hA' : IsCoprime (A₂ : ℤ) (A₁ : ℤ) := Nat.isCoprime_iff_coprime.2 hA.symm
  obtain ⟨e, f, hb⟩ := hA'
  obtain ⟨x₂, y₂, hb2⟩ := hz
  have hc : IsCoprime (A₁ : ℤ) (A₂ : ℤ) := Nat.isCoprime_iff_coprime.2 hA
  have hS : ∀ w : ℤ, ((A₁ * A₂ : ℕ) : ℤ) ∣ w ↔ (A₁ : ℤ) ∣ w ∧ (A₂ : ℤ) ∣ w := by
    intro w
    push_cast
    exact ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
      fun h => hc.mul_dvd h.1 h.2⟩
  refine ⟨e * A₂ + f * A₁ * z₁, f * A₁ * N₀, e * A₂ + f * A₁ * x₂, f * A₁ * y₂,
    fun u c => ?_, ?_⟩
  · rw [hS]
    have e1 : u * (e * A₂ + f * A₁ * z₁) + c * (f * A₁ * N₀) =
        A₁ * (f * (u * z₁ + c * N₀ - u)) + u := by linear_combination u * hb
    have e2 : u * (e * A₂ + f * A₁ * z₁) + c * (f * A₁ * N₀) =
        A₂ * (e * (u - u * z₁ - c * N₀)) + (u * z₁ + c * N₀) := by
      linear_combination (u * z₁ + c * N₀) * hb
    rw [e1, dvd_add_right (dvd_mul_right _ _)]
    rw [← e1, e2, dvd_add_right (dvd_mul_right _ _)]
  · rw [hS]
    constructor
    · refine ⟨-f * (e * A₂ + 1) + e * A₂ * f * (z₁ + x₂) + f ^ 2 * A₁ * (z₁ * x₂ + N₀ * y₂), ?_⟩
      linear_combination (e * A₂ + 1) * hb
    · refine ⟨e ^ 2 * A₂ + e * f * A₁ * (z₁ + x₂) - e * (f * A₁ + 1), ?_⟩
      linear_combination (f * A₁) ^ 2 * hb2 + (f * A₁ + 1) * hb

/-! ## Counting in `SL₂(ℤ/S)` -/

lemma card_filter_mul_zero_le (S : ℕ) [NeZero S]
    (N : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    (univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) => (g * N) 0 0 = 0).card ≤
      S ^ 2 := by
  classical
  set F := univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) => (g * N) 0 0 = 0
  have h := Finset.card_le_card_of_injOn
    (s := F) (t := (univ : Finset (ZMod S × ZMod S)))
    (fun g => ((g * N) 0 1, (g * N) 1 1)) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  · simpa [Finset.card_univ, ZMod.card, sq] using h
  intro g hg g' hg' heq
  simp only [F, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hg hg'
  simp only [Prod.mk.injEq] at heq
  have hdet : ∀ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := fun h => by
    rw [← Matrix.det_fin_two]; exact h.2
  have d1 := hdet (g * N)
  have d2 := hdet (g' * N)
  rw [hg] at d1; rw [hg'] at d2
  have h10 : (g * N) 1 0 = (g' * N) 1 0 := by
    rw [heq.1] at d1
    linear_combination ((g' * N) 1 0) * d1 - ((g * N) 1 0) * d2
  have hmat : g * N = g' * N := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hg, hg']
    · exact heq.1
    · exact h10
    · exact heq.2
  exact mul_right_cancel hmat

/-- `P(S) ≤ π²/6`. -/
lemma PS_le (S : ℕ) : L102K.PS S ≤ π ^ 2 / 6 := by
  unfold L102K.PS
  rw [← hasSum_zeta_two.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) ?_ L102K.summable_inv_sq
  · split_ifs
    · exact (le_abs_self _).trans (L102K.abs_mu2_le n)
    · positivity
  · exact L102K.summable_of_le_mu2 fun n => by split_ifs <;> simp

/-- `|SL₂(ℤ/S)| ≥ (36/π⁴) S³`. -/
lemma card_SL2_ge (S : ℕ) (hS : 0 < S) :
    36 / π ^ 4 * (S : ℝ) ^ 3 ≤ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) := by
  have hc := L102K.card_SL2 S hS
  have hJP := L102K.JS_mul_PS S hS
  have : NeZero S := ⟨hS.ne'⟩
  have hpos : (0 : ℝ) < Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) := by
    exact_mod_cast Nat.card_pos
  have hS3 : (0 : ℝ) < (S : ℝ) ^ 3 := by positivity
  have hJ : 0 < L102K.JS S := by
    rw [hc] at hpos; exact pos_of_mul_pos_right hpos hS3.le
  have hpi : 0 < π ^ 2 := by positivity
  have hP : 0 < L102K.PS S := by
    have : 0 < L102K.JS S * L102K.PS S := by rw [hJP]; positivity
    exact pos_of_mul_pos_right this hJ.le
  have hPle := PS_le S
  have hJge : 36 / π ^ 4 ≤ L102K.JS S := by
    have e : L102K.JS S = 6 / π ^ 2 / L102K.PS S := by
      rw [← hJP]; field_simp
    rw [e, le_div_iff₀ hP]
    calc 36 / π ^ 4 * L102K.PS S ≤ 36 / π ^ 4 * (π ^ 2 / 6) := by gcongr
      _ = 6 / π ^ 2 := by field_simp; ring
  rw [hc, mul_comm ((S : ℝ) ^ 3)]
  exact mul_le_mul_of_nonneg_right hJge hS3.le

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E: the core count of the single-edge root replacement

For coprime `A₁, A₂` with `S = A₁A₂` squarefree, `N₀ ∈ ℤ`, a set `B` of ratios and its
`ε`-fattening `B⁺`,

`ε · #{(P, Q) ∈ Ω² : A₁ ∣ P₁, A₂ ∣ Q₁, det(P, Q) = N₀, r_P ∈ B} ≤ 19 Λ vol(B⁺ ∩ (0,1])`,

`Λ = S²(30 ε U V/(ζ(2)|SL₂(ℤ/S)|) + U V x^{-c})`, when `|N₀| ε ≤ 1`. The ingredients: the root
basis `Q = z₁ P + N₀ (c, d)` with `z₁` in a window of `≤ 19` integers; the CRT column, which turns
`A₁ ∣ u, A₂ ∣ u z₁ + c N₀` into `(g₀ N̄)₀₀ = 0` for `g₀ = g mod S`; `#{g₀ : (g₀N̄)₀₀ = 0} ≤ S²`;
[21] Lemma 3.3 (K's `rootResidues`) for each `g₀`; and averaging the indicator of `B` over windows
inside `B⁺`. -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots

/-! ## Lemma 3.3 at one `x` -/

/-- The count of [21] Lemma 3.3 with `I₁ = [1, 16]`, `I₂ = [1, 2]`, `I₃ = [a₃, b₃]`. -/
def RootPredE (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V a₃ b₃ : ℝ)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  (g 0 0 : ℝ) / U ∈ Set.Icc (1 : ℝ) 16 ∧ (g 1 0 : ℝ) / V ∈ Set.Icc (1 : ℝ) 2 ∧ 0 ≤ g 0 1 ∧
    g 0 1 < g 0 0 ∧ (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ Set.Icc a₃ b₃ ∧
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀

/-- The upper half of [21] Lemma 3.3 at one `x` and one pair `U, V`. -/
def RootCountAt (x U V c : ℝ) : Prop :=
  ∀ S : ℕ, 0 < S → Squarefree S → (S : ℝ) ≤ exp (log x ^ (0.98 : ℝ)) →
    ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), ∀ a₃ b₃ : ℝ, 0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
      (Nat.card {g // RootPredE S g₀ U V a₃ b₃ g} : ℝ) ≤
        U * V * 15 * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
          U * V * x ^ (-c)

/-- [21] Lemma 3.3 (K's `rootResidues`) in the form used here. -/
lemma rootCountAt_of {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ U V : ℝ, x ^ δ ≤ U → x ^ δ ≤ V →
      RootCountAt x U V c := by
  obtain ⟨c, hc, hall⟩ := ArtinPrimitiveRoots.abs_card_specialLinearGroup_box_sub_le δ hδ
  obtain ⟨x₀, hx₀⟩ := hall 1
  refine ⟨c, hc, x₀, fun x hx U V hU hV S hS0 hS hSx g₀ a₃ b₃ ha₃ hab₃ hb₃ => ?_⟩
  have h := hx₀ x hx U V hU hV S hS0 hS (by simpa using hSx) g₀ 1 16 1 2 a₃ b₃
    le_rfl (by norm_num) le_rfl le_rfl (by norm_num) le_rfl ha₃ hab₃ hb₃
    (Set.Icc 1 16) (Set.Icc 1 2) (Set.Icc a₃ b₃) Set.Ioo_subset_Icc_self subset_rfl
    Set.Ioo_subset_Icc_self subset_rfl Set.Ioo_subset_Icc_self subset_rfl
  have h' := (abs_le.1 h).2
  unfold RootPredE
  have e : U * V * (16 - 1) * (2 - 1) * (b₃ - a₃) = U * V * 15 * (b₃ - a₃) := by ring
  rw [e] at h'
  linarith

/-! ## Finiteness of the counted sets -/

lemma finite_rootPredE (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    {U V a₃ b₃ : ℝ} (hU : 0 < U) (hV : 0 < V) :
    Finite {g // RootPredE S g₀ U V a₃ b₃ g} := by
  set s : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ) := {g | RootPredE S g₀ U V a₃ b₃ g}
  set f : Matrix.SpecialLinearGroup (Fin 2) ℤ → ℤ × ℤ × ℤ := fun g => (g 0 0, g 1 0, g 0 1)
  set B₁ : ℤ := ⌊16 * U⌋
  set B₂ : ℤ := ⌊2 * V⌋
  have himg : f '' s ⊆ ↑(Finset.Icc 0 B₁ ×ˢ Finset.Icc 0 B₂ ×ˢ Finset.Icc 0 B₁) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, -, -⟩ := hg
    rw [le_div_iff₀ hU] at h1
    rw [div_le_iff₀ hU] at h2
    rw [le_div_iff₀ hV] at h3
    rw [div_le_iff₀ hV] at h4
    have a1 : (0 : ℝ) ≤ g 0 0 := by nlinarith
    have a2 : (0 : ℝ) ≤ g 1 0 := by nlinarith
    have b1 : g 0 0 ≤ B₁ := Int.le_floor.2 (by linarith)
    have b2 : g 1 0 ≤ B₂ := Int.le_floor.2 (by linarith)
    simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc, f]
    exact ⟨⟨by exact_mod_cast a1, b1⟩, ⟨by exact_mod_cast a2, b2⟩, h5, by omega⟩
  have hinj : Set.InjOn f s := by
    intro g hg g' hg' heq
    simp only [Prod.mk.injEq, f] at heq
    obtain ⟨e00, e10, e01⟩ := heq
    have hu : 0 < g 0 0 := lt_of_le_of_lt hg.2.2.1 hg.2.2.2.1
    have d1 : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact g.2
    have d2 : g' 0 0 * g' 1 1 - g' 0 1 * g' 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact g'.2
    rw [← e00, ← e10, ← e01] at d2
    have e11 : g 1 1 = g' 1 1 := by
      have : g 0 0 * (g 1 1 - g' 1 1) = 0 := by linear_combination d1 - d2
      rcases mul_eq_zero.1 this with h | h
      · omega
      · linarith
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11
  have hfin : s.Finite :=
    Set.Finite.of_finite_image ((Finset.finite_toSet _).subset himg) hinj
  exact hfin.to_subtype

/-! ## Positions -/

lemma posBox_bounds {U V : ℝ} (hU : 0 < U) (hV : 0 < V) {P : ℕ × ℕ} (hP : P ∈ posBox U V) :
    U ≤ P.1 ∧ (P.1 : ℝ) ≤ 16 * U ∧ V ≤ P.2 ∧ (P.2 : ℝ) ≤ 2 * V ∧ Nat.Coprime P.1 P.2 := by
  simp only [posBox, mem_filter, mem_product, mem_Icc] at hP
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hP
  exact ⟨(Nat.le_ceil U).trans (by exact_mod_cast h1),
    (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith)),
    (Nat.le_ceil V).trans (by exact_mod_cast h3),
    (Nat.cast_le.2 h4).trans (Nat.floor_le (by linarith)), h5⟩

lemma rootRatio_mem {u : ℕ} (hu : 0 < u) (v : ℕ) : 0 ≤ rootRatio u v ∧ rootRatio u v < 1 := by
  rw [rootRatio_eq]
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  refine ⟨by positivity, (div_lt_one hu').2 (by exact_mod_cast rootC_lt hu v)⟩

/-! ## One residue condition: Lemma 3.3 summed over the admissible classes -/

/-- For a fixed `z₁` with `(z₁, N₀)` primitive, the positions `P` with `A₁ ∣ P₁`,
`A₂ ∣ P₁ z₁ + c_P N₀` and `r_P ∈ [a₃, b₃]` number at most `S² (main + error)`. -/
lemma count_P_le {x U V c : ℝ} (hRC : RootCountAt x U V c) (hx0 : 0 < x) (hU : 0 < U) (hV : 0 < V)
    {A₁ A₂ : ℕ} (hA : Nat.Coprime A₁ A₂) (hS0 : 0 < A₁ * A₂) (hSq : Squarefree (A₁ * A₂))
    (hSx : ((A₁ * A₂ : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ))) {z₁ N₀ : ℤ} (hz : IsCoprime z₁ N₀)
    {a₃ b₃ : ℝ} (ha₃ : 0 ≤ a₃) (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1) :
    ((((posBox U V).filter fun P => A₁ ∣ P.1 ∧
        (A₂ : ℤ) ∣ (P.1 : ℤ) * z₁ + (rootC P.1 P.2 : ℤ) * N₀ ∧
        rootRatio P.1 P.2 ∈ Set.Icc a₃ b₃).card : ℕ) : ℝ) ≤
      ((A₁ * A₂ : ℕ) : ℝ) ^ 2 * (U * V * 15 * (b₃ - a₃) /
          ((riemannZeta 2).re *
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (A₁ * A₂))) : ℝ)) +
          U * V * x ^ (-c)) := by
  classical
  set S := A₁ * A₂ with hSdef
  have : NeZero S := ⟨hS0.ne'⟩
  obtain ⟨α, β, x', y', hiff, hdet⟩ := crt_column hA hz
  -- the matrix `N̄`
  set Nm : Matrix (Fin 2) (Fin 2) (ZMod S) := !![(α : ZMod S), -(y' : ZMod S); (β : ZMod S),
    (x' : ZMod S)]
  have hNdet : Nm.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Nm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (α * x' + β * y' - 1) S).2 (by exact_mod_cast hdet)
    push_cast at this
    linear_combination this
  set N : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) := ⟨Nm, hNdet⟩
  set Adm := univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) => (g * N) 0 0 = 0
  have hAdm : Adm.card ≤ S ^ 2 := card_filter_mul_zero_le S N
  set F := (posBox U V).filter fun P => A₁ ∣ P.1 ∧
    (A₂ : ℤ) ∣ (P.1 : ℤ) * z₁ + (rootC P.1 P.2 : ℤ) * N₀ ∧ rootRatio P.1 P.2 ∈ Set.Icc a₃ b₃
  set φ : ℕ × ℕ → Matrix.SpecialLinearGroup (Fin 2) (ZMod S) := fun P =>
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (rootG P.1 P.2)
  have hPpos : ∀ P ∈ F, 0 < P.1 ∧ Nat.Coprime P.1 P.2 := by
    intro P hP
    have hb := posBox_bounds hU hV (mem_filter.1 hP).1
    refine ⟨?_, hb.2.2.2.2⟩
    have : (0 : ℝ) < P.1 := lt_of_lt_of_le hU hb.1
    exact_mod_cast this
  have hmaps : Set.MapsTo φ ↑F ↑Adm := by
    intro P hP
    have hP' := mem_filter.1 (mem_coe.1 hP)
    obtain ⟨hu, hcop⟩ := hPpos P hP
    obtain ⟨g00, g01, -, -⟩ := rootG_apply hu hcop
    simp only [Adm, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, φ]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom, N, Nm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, g00, g01]
    have hdv := (hiff P.1 (rootC P.1 P.2)).2 ⟨by exact_mod_cast hP'.2.1, hP'.2.2.1⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ S).2 hdv
    push_cast at this
    exact_mod_cast this
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ g₀ ∈ Adm, ((F.filter fun P => φ P = g₀).card : ℝ) ≤
      U * V * 15 * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
          U * V * x ^ (-c) := by
    intro g₀ _
    have hfin := finite_rootPredE S g₀ hU hV (a₃ := a₃) (b₃ := b₃)
    refine le_trans ?_ (hRC S hS0 hSq hSx g₀ a₃ b₃ ha₃ hab₃ hb₃)
    have hle : (F.filter fun P => φ P = g₀).card ≤ Nat.card {g // RootPredE S g₀ U V a₃ b₃ g} := by
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_le_card_of_injective
        (fun P => ⟨rootG P.1.1 P.1.2, ?_⟩) ?_
      · obtain ⟨hPF, hφ⟩ := mem_filter.1 P.2
        obtain ⟨hu, hcop⟩ := hPpos P.1 hPF
        obtain ⟨g00, g01, g10, -⟩ := rootG_apply hu hcop
        have hb := posBox_bounds hU hV (mem_filter.1 hPF).1
        have hr := (mem_filter.1 hPF).2.2.2
        refine ⟨?_, ?_, ?_, ?_, ?_, hφ⟩
        · rw [g00]; push_cast
          exact ⟨(le_div_iff₀ hU).2 (by linarith [hb.1]), (div_le_iff₀ hU).2 (by linarith [hb.2.1])⟩
        · rw [g10]; push_cast
          exact ⟨(le_div_iff₀ hV).2 (by linarith [hb.2.2.1]),
            (div_le_iff₀ hV).2 (by linarith [hb.2.2.2.1])⟩
        · rw [g01]; positivity
        · rw [g01, g00]; exact_mod_cast rootC_lt hu P.1.2
        · rw [g01, g00]; push_cast; rw [← rootRatio_eq]; exact hr
      · intro P P' h
        have h' := congrArg (fun g : {g // RootPredE S g₀ U V a₃ b₃ g} =>
          ((g.1 0 0 : ℤ), (g.1 1 0 : ℤ))) h
        simp only at h'
        obtain ⟨hu, hcop⟩ := hPpos P.1 (mem_filter.1 P.2).1
        obtain ⟨hu', hcop'⟩ := hPpos P'.1 (mem_filter.1 P'.2).1
        rw [(rootG_apply hu hcop).1, (rootG_apply hu' hcop').1, (rootG_apply hu hcop).2.2.1,
          (rootG_apply hu' hcop').2.2.1] at h'
        simp only [Prod.mk.injEq, Nat.cast_inj] at h'
        exact Subtype.ext (Prod.ext h'.1 h'.2)
    exact_mod_cast hle
  push_cast
  calc ∑ g₀ ∈ Adm, ((F.filter fun P => φ P = g₀).card : ℝ)
      ≤ ∑ _g₀ ∈ Adm, (U * V * 15 * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
          U * V * x ^ (-c)) := sum_le_sum hfib
    _ = Adm.card * (U * V * 15 * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
          U * V * x ^ (-c)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (S : ℝ) ^ 2 * (U * V * 15 * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
          U * V * x ^ (-c)) := by
        have hz2 : 0 < (riemannZeta 2).re := by
          rw [riemannZeta_two]
          rw [show (π : ℂ) ^ 2 / 6 = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
          positivity
        have : (0 : ℝ) ≤ U * V * 15 * (b₃ - a₃) /
            ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
            U * V * x ^ (-c) := by
          have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
          have hb : 0 ≤ b₃ - a₃ := by linarith
          positivity
        gcongr
        exact_mod_cast hAdm

/-! ## The root basis of an edge -/

/-- `det(P, Q) = P₁ Q₂ − P₂ Q₁`. -/
def detPQ (P Q : ℕ × ℕ) : ℤ := (P.1 : ℤ) * Q.2 - (P.2 : ℤ) * Q.1

/-- The first root coordinate `z₁ = d Q₁ − c Q₂` of `Q` in the basis `g_P`. -/
noncomputable def zOne (P Q : ℕ × ℕ) : ℤ := (rootD P.1 P.2 : ℤ) * Q.1 - (rootC P.1 P.2 : ℤ) * Q.2

lemma root_coords {P Q : ℕ × ℕ} (hu : 0 < P.1) (hcop : Nat.Coprime P.1 P.2) :
    (Q.1 : ℤ) = zOne P Q * P.1 + detPQ P Q * rootC P.1 P.2 ∧
      (Q.2 : ℤ) = zOne P Q * P.2 + detPQ P Q * rootD P.1 P.2 := by
  have h := rootDet hu hcop
  unfold zOne detPQ
  constructor
  · linear_combination -(Q.1 : ℤ) * h
  · linear_combination -(Q.2 : ℤ) * h

/-- For fixed `P`, the targets `Q` of determinant `N₀` with `A₂ ∣ Q₁` and `|r_P − r| ≤ ε` inject
into the window of `z₁`. -/
lemma card_Q_le (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (A₁ A₂ : ℕ) (N₀ : ℤ) (ε r : ℝ)
    (hN : |(N₀ : ℝ)| * ε ≤ 1) (P : ℕ × ℕ) (hP : P ∈ posBox U V) :
    ((posBox U V).filter fun Q => A₁ ∣ P.1 ∧ A₂ ∣ Q.1 ∧ detPQ P Q = N₀ ∧
        |rootRatio P.1 P.2 - r| ≤ ε).card ≤
      ((Finset.Icc ⌈-(N₀ : ℝ) * r - 1⌉ ⌊-(N₀ : ℝ) * r + 17⌋).filter fun z₁ : ℤ =>
        A₁ ∣ P.1 ∧ (A₂ : ℤ) ∣ (P.1 : ℤ) * z₁ + (rootC P.1 P.2 : ℤ) * N₀ ∧
        |rootRatio P.1 P.2 - r| ≤ ε ∧ IsCoprime z₁ N₀).card := by
  obtain ⟨hPu, hPu', -, -, hcop⟩ := posBox_bounds hU hV hP
  have hu : 0 < P.1 := by
    have : (0 : ℝ) < P.1 := lt_of_lt_of_le hU hPu
    exact_mod_cast this
  refine card_le_card_of_injOn (zOne P) ?_ ?_
  · intro Q hQ
    obtain ⟨hQb, hA₁, hA₂, hdet, hr⟩ := mem_filter.1 (mem_coe.1 hQ)
    obtain ⟨hQ1, hQ1', hQ2, -, hQcop⟩ := posBox_bounds hU hV hQb
    obtain ⟨e1, e2⟩ := root_coords (Q := Q) hu hcop
    rw [hdet] at e1 e2
    refine mem_coe.2 (mem_filter.2 ⟨?_, hA₁, ?_, hr, ?_⟩)
    · -- the window
      have hc : (rootC P.1 P.2 : ℝ) = rootRatio P.1 P.2 * P.1 := by
        rw [rootRatio_eq]; field_simp
      have e1r : (Q.1 : ℝ) = (zOne P Q : ℝ) * P.1 + (N₀ : ℝ) * rootC P.1 P.2 := by
        exact_mod_cast e1
      have hup : (P.1 : ℝ) > 0 := by exact_mod_cast hu
      have hdiff : |(N₀ : ℝ) * (rootRatio P.1 P.2 - r)| ≤ 1 := by
        rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_left hr (abs_nonneg _)) hN
      have hd1 := (abs_le.1 hdiff).1
      have hd2 := (abs_le.1 hdiff).2
      set z := (zOne P Q : ℝ)
      set ρ := rootRatio P.1 P.2
      have key : z * P.1 = Q.1 - N₀ * ρ * P.1 := by rw [e1r, hc]; ring
      rw [mem_Icc]
      constructor
      · apply Int.ceil_le.2
        have : (-(N₀ : ℝ) * r - 1) * P.1 ≤ z * P.1 := by
          rw [key]
          have hQ0 : (0 : ℝ) ≤ Q.1 := Nat.cast_nonneg _
          nlinarith
        exact le_of_mul_le_mul_right this hup
      · apply Int.le_floor.2
        have : z * P.1 ≤ (-(N₀ : ℝ) * r + 17) * P.1 := by
          rw [key]
          nlinarith
        exact le_of_mul_le_mul_right this hup
    · rw [show (P.1 : ℤ) * zOne P Q + (rootC P.1 P.2 : ℤ) * N₀ =
        zOne P Q * P.1 + N₀ * rootC P.1 P.2 by ring, ← e1]
      exact_mod_cast hA₂
    · -- `(z₁, N₀)` is primitive since `Q` is
      have hQc : IsCoprime (Q.1 : ℤ) (Q.2 : ℤ) := Nat.isCoprime_iff_coprime.2 hQcop
      obtain ⟨s, t, hst⟩ := hQc
      refine ⟨s * P.1 + t * P.2, s * rootC P.1 P.2 + t * rootD P.1 P.2, ?_⟩
      rw [e1, e2] at hst
      linear_combination hst
  · intro Q hQ Q' hQ' heq
    obtain ⟨-, -, -, hdet, -⟩ := mem_filter.1 (mem_coe.1 hQ)
    obtain ⟨-, -, -, hdet', -⟩ := mem_filter.1 (mem_coe.1 hQ')
    obtain ⟨e1, e2⟩ := root_coords (Q := Q) hu hcop
    obtain ⟨e1', e2'⟩ := root_coords (Q := Q') hu hcop
    rw [hdet, heq] at e1 e2
    rw [hdet'] at e1' e2'
    have h1 : (Q.1 : ℤ) = Q'.1 := by rw [e1, e1']
    have h2 : (Q.2 : ℤ) = Q'.2 := by rw [e2, e2']
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

lemma card_window_le (t : ℝ) : (Finset.Icc ⌈t - 1⌉ ⌊t + 17⌋).card ≤ 19 := by
  rw [Int.card_Icc]
  have h1 : (⌊t + 17⌋ : ℝ) ≤ t + 17 := Int.floor_le _
  have h2 : t - 1 ≤ (⌈t - 1⌉ : ℝ) := Int.le_ceil _
  have : ⌊t + 17⌋ + 1 - ⌈t - 1⌉ ≤ 19 := by
    have : ((⌊t + 17⌋ + 1 - ⌈t - 1⌉ : ℤ) : ℝ) < 20 := by push_cast; linarith
    have : (⌊t + 17⌋ + 1 - ⌈t - 1⌉ : ℤ) < 20 := by exact_mod_cast this
    omega
  omega

/-- The main term of Lemma 3.3 with `|I₁||I₂||I₃| ≤ 15 · 2ε`, times `S²`, plus the error. -/
noncomputable def lam (x U V c ε : ℝ) (S : ℕ) : ℝ :=
  (S : ℝ) ^ 2 * (U * V * 15 * (2 * ε) /
    ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) +
    U * V * x ^ (-c))

lemma zeta_two_re : (riemannZeta 2).re = π ^ 2 / 6 := by
  rw [riemannZeta_two]
  rw [show (π : ℂ) ^ 2 / 6 = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- **The pointwise count.** For `r ∈ [0, 1]`, the pairs with `|r_P − r| ≤ ε` number `≤ 19 Λ`. -/
lemma count_pairs_r_le {x U V c : ℝ} (hRC : RootCountAt x U V c) (hx0 : 0 < x) (hU : 0 < U)
    (hV : 0 < V) {A₁ A₂ : ℕ} (hA : Nat.Coprime A₁ A₂) (hS0 : 0 < A₁ * A₂)
    (hSq : Squarefree (A₁ * A₂)) (hSx : ((A₁ * A₂ : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ)))
    (N₀ : ℤ) {ε : ℝ} (hε : 0 ≤ ε) (hN : |(N₀ : ℝ)| * ε ≤ 1) (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    ((((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        |rootRatio PQ.1.1 PQ.1.2 - r| ≤ ε).card : ℕ) : ℝ) ≤ 19 * lam x U V c ε (A₁ * A₂) := by
  classical
  set W := Finset.Icc ⌈-(N₀ : ℝ) * r - 1⌉ ⌊-(N₀ : ℝ) * r + 17⌋
  set cond : ℕ × ℕ → ℤ → Prop := fun P z₁ => A₁ ∣ P.1 ∧
    (A₂ : ℤ) ∣ (P.1 : ℤ) * z₁ + (rootC P.1 P.2 : ℤ) * N₀ ∧
    |rootRatio P.1 P.2 - r| ≤ ε ∧ IsCoprime z₁ N₀
  -- step A/B: from pairs to `(z₁, P)`
  have hAB : ((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        |rootRatio PQ.1.1 PQ.1.2 - r| ≤ ε).card ≤
      ∑ z₁ ∈ W, ((posBox U V).filter fun P => cond P z₁).card := by
    rw [card_filter, sum_product]
    calc ∑ P ∈ posBox U V, ∑ Q ∈ posBox U V,
          (if A₁ ∣ (P, Q).1.1 ∧ A₂ ∣ (P, Q).2.1 ∧ detPQ (P, Q).1 (P, Q).2 = N₀ ∧
            |rootRatio (P, Q).1.1 (P, Q).1.2 - r| ≤ ε then 1 else 0)
        = ∑ P ∈ posBox U V, ((posBox U V).filter fun Q => A₁ ∣ P.1 ∧ A₂ ∣ Q.1 ∧
            detPQ P Q = N₀ ∧ |rootRatio P.1 P.2 - r| ≤ ε).card := by
          refine sum_congr rfl fun P _ => ?_
          rw [card_filter]
      _ ≤ ∑ P ∈ posBox U V, (W.filter fun z₁ => cond P z₁).card :=
          sum_le_sum fun P hP => card_Q_le U V hU hV A₁ A₂ N₀ ε r hN P hP
      _ = ∑ z₁ ∈ W, ((posBox U V).filter fun P => cond P z₁).card := by
          simp only [card_filter]
          exact sum_comm
  -- step C: one `z₁`
  set a₃ := max 0 (r - ε)
  set b₃ := min 1 (r + ε)
  have ha₃ : 0 ≤ a₃ := le_max_left _ _
  have hab₃ : a₃ ≤ b₃ := max_le (le_min zero_le_one (by linarith)) (le_min (by linarith)
    (by linarith))
  have hb₃ : b₃ ≤ 1 := min_le_left _ _
  have hlen : b₃ - a₃ ≤ 2 * ε := by
    have : b₃ ≤ r + ε := min_le_right _ _
    have : r - ε ≤ a₃ := le_max_right _ _
    linarith
  have hC : ∀ z₁ ∈ W, ((((posBox U V).filter fun P => cond P z₁).card : ℕ) : ℝ) ≤
      lam x U V c ε (A₁ * A₂) := by
    intro z₁ _
    by_cases hz : IsCoprime z₁ N₀
    · have hsub : ((posBox U V).filter fun P => cond P z₁) ⊆ (posBox U V).filter fun P =>
          A₁ ∣ P.1 ∧ (A₂ : ℤ) ∣ (P.1 : ℤ) * z₁ + (rootC P.1 P.2 : ℤ) * N₀ ∧
          rootRatio P.1 P.2 ∈ Set.Icc a₃ b₃ := by
        intro P hP
        obtain ⟨hPb, h1, h2, h3, -⟩ := mem_filter.1 hP
        have hb := posBox_bounds hU hV hPb
        have hu : 0 < P.1 := by
          have : (0 : ℝ) < P.1 := lt_of_lt_of_le hU hb.1
          exact_mod_cast this
        have hm := rootRatio_mem hu P.2
        obtain ⟨h3a, h3b⟩ := abs_le.1 h3
        refine mem_filter.2 ⟨hPb, h1, h2, max_le hm.1 (by linarith),
          le_min hm.2.le (by linarith)⟩
      have h := count_P_le hRC hx0 hU hV hA hS0 hSq hSx hz ha₃ hab₃ hb₃
      refine (Nat.cast_le.2 (card_le_card hsub)).trans (h.trans ?_)
      unfold lam
      have hz2 : 0 < (riemannZeta 2).re := by rw [zeta_two_re]; positivity
      have : NeZero (A₁ * A₂) := ⟨hS0.ne'⟩
      have hc : (0 : ℝ) < Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (A₁ * A₂))) := by
        exact_mod_cast Nat.card_pos
      gcongr
    · have : ((posBox U V).filter fun P => cond P z₁) = ∅ :=
        filter_false_of_mem fun P _ h => hz h.2.2.2
      rw [this, card_empty, Nat.cast_zero]
      unfold lam
      have hz2 : 0 < (riemannZeta 2).re := by rw [zeta_two_re]; positivity
      have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
      positivity
  calc ((((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        |rootRatio PQ.1.1 PQ.1.2 - r| ≤ ε).card : ℕ) : ℝ)
      ≤ ∑ z₁ ∈ W, ((((posBox U V).filter fun P => cond P z₁).card : ℕ) : ℝ) := by
        exact_mod_cast hAB
    _ ≤ ∑ _z₁ ∈ W, lam x U V c ε (A₁ * A₂) := sum_le_sum hC
    _ = W.card * lam x U V c ε (A₁ * A₂) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 19 * lam x U V c ε (A₁ * A₂) := by
        have hl : 0 ≤ lam x U V c ε (A₁ * A₂) := by
          unfold lam
          have hz2 : 0 < (riemannZeta 2).re := by rw [zeta_two_re]; positivity
          have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
          positivity
        have hW : (W.card : ℝ) ≤ 19 := by
          have h := card_window_le (-(N₀ : ℝ) * r)
          have : W.card ≤ 19 := h
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right hW hl

/-! ## Averaging the bad indicator over windows -/

/-- **Averaging over windows.** If every point `e i` (`i ∈ F`) has its `ε`-window inside `B⁺`, and
every `r ∈ (0, 1]` has at most `H` points within `ε`, then `ε #F ≤ H vol(B⁺ ∩ (0, 1])`.
No measurability of `B⁺` is needed. -/
lemma card_le_of_fatten {ι : Type*} (F : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ F, 0 ≤ e i ∧ e i < 1) (Bp : Set ℝ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hfat : ∀ i ∈ F, ∀ r, |r - e i| ≤ ε → r ∈ Bp) {H : ℝ} (hH : 0 ≤ H)
    (hcount : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ((F.filter fun i => |e i - r| ≤ ε).card : ℝ) ≤ H) :
    ε * F.card ≤ H * (volume (Bp ∩ Set.Ioc 0 1)).toReal := by
  classical
  set M := toMeasurable volume (Bp ∩ Set.Ioc 0 1) ∩ Set.Ioc (0 : ℝ) 1
  have hvolM : volume M ≤ volume (Bp ∩ Set.Ioc 0 1) := by
    calc volume M ≤ volume (toMeasurable volume (Bp ∩ Set.Ioc 0 1)) :=
          measure_mono Set.inter_subset_left
      _ = _ := measure_toMeasurable _
  have hfin : volume (Bp ∩ Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  -- the windows
  have hwin : ∀ i ∈ F, ENNReal.ofReal ε ≤ volume (M ∩ Set.Icc (e i - ε) (e i + ε)) := by
    intro i hi
    obtain ⟨h0, h1⟩ := he i hi
    by_cases h : e i ≤ 1 / 2
    · have hsub : Set.Ioc (e i) (e i + ε) ⊆ M ∩ Set.Icc (e i - ε) (e i + ε) := by
        intro r hr
        rw [Set.mem_Ioc] at hr
        have hr2 : |r - e i| ≤ ε := abs_le.2 ⟨by linarith, by linarith⟩
        have hr1 : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        exact ⟨⟨subset_toMeasurable _ _ ⟨hfat i hi r hr2, hr1⟩, hr1⟩, by linarith, by linarith⟩
      calc ENNReal.ofReal ε = volume (Set.Ioc (e i) (e i + ε)) := by
            rw [Real.volume_Ioc]; congr 1; ring
        _ ≤ _ := measure_mono hsub
    · push Not at h
      have hsub : Set.Ioc (e i - ε) (e i) ⊆ M ∩ Set.Icc (e i - ε) (e i + ε) := by
        intro r hr
        rw [Set.mem_Ioc] at hr
        have hr2 : |r - e i| ≤ ε := abs_le.2 ⟨by linarith, by linarith⟩
        have hr1 : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        exact ⟨⟨subset_toMeasurable _ _ ⟨hfat i hi r hr2, hr1⟩, hr1⟩, by linarith, by linarith⟩
      calc ENNReal.ofReal ε = volume (Set.Ioc (e i - ε) (e i)) := by
            rw [Real.volume_Ioc]; congr 1; ring
        _ ≤ _ := measure_mono hsub
  have hsum : ENNReal.ofReal ε * F.card ≤ ∑ i ∈ F, volume (M ∩ Set.Icc (e i - ε) (e i + ε)) := by
    calc ENNReal.ofReal ε * F.card = ∑ _i ∈ F, ENNReal.ofReal ε := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hwin
  have hint : ∑ i ∈ F, volume (M ∩ Set.Icc (e i - ε) (e i + ε)) =
      ∫⁻ r in M, ∑ i ∈ F, (Set.Icc (e i - ε) (e i + ε)).indicator (1 : ℝ → ENNReal) r := by
    rw [lintegral_finsetSum _ (fun i _ => measurable_one.indicator measurableSet_Icc)]
    refine sum_congr rfl fun i _ => ?_
    rw [lintegral_indicator_one measurableSet_Icc, Measure.restrict_apply measurableSet_Icc,
      Set.inter_comm]
  have hpt : ∀ r ∈ M, ∑ i ∈ F, (Set.Icc (e i - ε) (e i + ε)).indicator (1 : ℝ → ENNReal) r ≤
      ENNReal.ofReal H := by
    intro r hr
    have hind : ∀ i, (Set.Icc (e i - ε) (e i + ε)).indicator (1 : ℝ → ENNReal) r =
        if |e i - r| ≤ ε then 1 else 0 := by
      intro i
      rw [Set.indicator_apply]
      by_cases hh : |e i - r| ≤ ε
      · obtain ⟨a1, a2⟩ := abs_le.1 hh
        rw [if_pos ⟨by linarith, by linarith⟩, if_pos hh]; rfl
      · rw [if_neg hh, if_neg]
        rintro ⟨a1, a2⟩
        exact hh (abs_le.2 ⟨by linarith, by linarith⟩)
    rw [sum_congr rfl fun i _ => hind i, sum_boole, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcount r hr.2)
  have hle : ∫⁻ r in M, ∑ i ∈ F, (Set.Icc (e i - ε) (e i + ε)).indicator (1 : ℝ → ENNReal) r ≤
      ENNReal.ofReal H * volume M := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono measurable_const hpt
  have htot : ENNReal.ofReal ε * F.card ≤ ENNReal.ofReal H * volume (Bp ∩ Set.Ioc 0 1) :=
    hsum.trans (hint.le.trans (hle.trans (by gcongr)))
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) htot
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
    ENNReal.toReal_ofReal hH, ENNReal.toReal_natCast] at this
  exact this

/-! ## The core count -/

open Classical in
/-- **Core count** of the single-edge root replacement. -/
theorem core_count {x U V c : ℝ} (hRC : RootCountAt x U V c) (hx0 : 0 < x) (hU : 0 < U)
    (hV : 0 < V) {A₁ A₂ : ℕ} (hA : Nat.Coprime A₁ A₂) (hS0 : 0 < A₁ * A₂)
    (hSq : Squarefree (A₁ * A₂)) (hSx : ((A₁ * A₂ : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ)))
    (N₀ : ℤ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hN : |(N₀ : ℝ)| * ε ≤ 1) (B Bp : Set ℝ)
    (hfat : ∀ r ∈ B, 0 ≤ r → r < 1 → ∀ r', |r' - r| ≤ ε → r' ∈ Bp) :
    ε * ((((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        rootRatio PQ.1.1 PQ.1.2 ∈ B).card : ℕ) : ℝ) ≤
      19 * lam x U V c ε (A₁ * A₂) * (volume (Bp ∩ Set.Ioc 0 1)).toReal := by
  classical
  set F := (posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
    A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧ rootRatio PQ.1.1 PQ.1.2 ∈ B
  have hpos : ∀ PQ ∈ F, 0 < PQ.1.1 := by
    intro PQ hPQ
    have hb := posBox_bounds hU hV (mem_product.1 (mem_filter.1 hPQ).1).1
    have : (0 : ℝ) < PQ.1.1 := lt_of_lt_of_le hU hb.1
    exact_mod_cast this
  have hl : 0 ≤ lam x U V c ε (A₁ * A₂) := by
    unfold lam
    have hz2 : 0 < (riemannZeta 2).re := by rw [zeta_two_re]; positivity
    have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
    positivity
  refine card_le_of_fatten F (fun PQ => rootRatio PQ.1.1 PQ.1.2)
    (fun PQ h => rootRatio_mem (hpos PQ h) _) Bp hε hε2 ?_ (by positivity) ?_
  · intro PQ hPQ r hr
    have hm := rootRatio_mem (hpos PQ hPQ) PQ.1.2
    exact hfat _ (mem_filter.1 hPQ).2.2.2.2 hm.1 hm.2 r hr
  · intro r hr
    refine le_trans ?_ (count_pairs_r_le hRC hx0 hU hV hA hS0 hSq hSx N₀ hε.le hN r hr.1.le hr.2)
    have hsub : (F.filter fun PQ => |rootRatio PQ.1.1 PQ.1.2 - r| ≤ ε) ⊆
        (posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
          A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
          |rootRatio PQ.1.1 PQ.1.2 - r| ≤ ε := by
      intro PQ h
      obtain ⟨h1, h2⟩ := mem_filter.1 h
      obtain ⟨h3, h4, h5, h6, -⟩ := mem_filter.1 h1
      exact mem_filter.2 ⟨h3, h4, h5, h6, h2⟩
    exact_mod_cast card_le_card hsub

open Classical in
/-- **Core count, explicit form:** `#F ≤ 1000 UV vol(B⁺)/S + 19 S² UV x^{-c}/ε`. -/
theorem core_count_bound {x U V c : ℝ} (hRC : RootCountAt x U V c) (hx0 : 0 < x) (hU : 0 < U)
    (hV : 0 < V) {A₁ A₂ : ℕ} (hA : Nat.Coprime A₁ A₂) (hS0 : 0 < A₁ * A₂)
    (hSq : Squarefree (A₁ * A₂)) (hSx : ((A₁ * A₂ : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ)))
    (N₀ : ℤ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hN : |(N₀ : ℝ)| * ε ≤ 1) (B Bp : Set ℝ)
    (hfat : ∀ r ∈ B, 0 ≤ r → r < 1 → ∀ r', |r' - r| ≤ ε → r' ∈ Bp) :
    ((((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        rootRatio PQ.1.1 PQ.1.2 ∈ B).card : ℕ) : ℝ) ≤
      1000 * (U * V) * (volume (Bp ∩ Set.Ioc 0 1)).toReal / ((A₁ * A₂ : ℕ) : ℝ) +
        19 * ((A₁ * A₂ : ℕ) : ℝ) ^ 2 * (U * V * x ^ (-c)) / ε := by
  have h := core_count hRC hx0 hU hV hA hS0 hSq hSx N₀ hε hε2 hN B Bp hfat
  set S := A₁ * A₂
  set v := (volume (Bp ∩ Set.Ioc (0 : ℝ) 1)).toReal
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hv1 : v ≤ 1 := by
    have : volume (Bp ∩ Set.Ioc (0 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
      calc volume (Bp ∩ Set.Ioc (0 : ℝ) 1) ≤ volume (Set.Ioc (0 : ℝ) 1) :=
            measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal 1 := by rw [Real.volume_Ioc]; norm_num
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rwa [ENNReal.toReal_ofReal zero_le_one] at this
  have : NeZero S := ⟨hS0.ne'⟩
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS0
  have hcard := card_SL2_ge S hS0
  set cS := (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)
  have hpi : 0 < π := Real.pi_pos
  have hcS : 0 < cS := lt_of_lt_of_le (by positivity) hcard
  have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
  -- `1/(ζ(2)|SL₂|) ≤ π²/(6 S³)`
  have hz : (riemannZeta 2).re * cS ≥ 6 / π ^ 2 * (S : ℝ) ^ 3 := by
    rw [zeta_two_re]
    calc π ^ 2 / 6 * cS ≥ π ^ 2 / 6 * (36 / π ^ 4 * (S : ℝ) ^ 3) := by gcongr
      _ = 6 / π ^ 2 * (S : ℝ) ^ 3 := by field_simp; ring
  have hpi2 : π ^ 2 < 10 := by
    have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  unfold lam at h
  set Fc := ((((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        rootRatio PQ.1.1 PQ.1.2 ∈ B).card : ℕ) : ℝ)
  have hz0 : 0 < (riemannZeta 2).re * cS := lt_of_lt_of_le (by positivity) hz.le
  have hinv : 1 / ((riemannZeta 2).re * cS) ≤ π ^ 2 / 6 / (S : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hz0 (by positivity)]
    calc 1 * (S : ℝ) ^ 3 = π ^ 2 / 6 * (6 / π ^ 2 * (S : ℝ) ^ 3) := by field_simp
      _ ≤ π ^ 2 / 6 * ((riemannZeta 2).re * cS) := by gcongr
  set Z := U * V * x ^ (-c)
  have hZ : 0 ≤ Z := by positivity
  have hUV : 0 ≤ U * V := by positivity
  have hm : (S : ℝ) ^ 2 * (U * V * 15 * (2 * ε) / ((riemannZeta 2).re * cS)) ≤
      ε * (50 * (U * V) / S) := by
    calc (S : ℝ) ^ 2 * (U * V * 15 * (2 * ε) / ((riemannZeta 2).re * cS))
        = 30 * ε * (U * V) * (S : ℝ) ^ 2 * (1 / ((riemannZeta 2).re * cS)) := by ring
      _ ≤ 30 * ε * (U * V) * (S : ℝ) ^ 2 * (π ^ 2 / 6 / (S : ℝ) ^ 3) := by gcongr
      _ = 5 * π ^ 2 * (ε * (U * V) / S) := by field_simp; ring
      _ ≤ 50 * (ε * (U * V) / S) := by gcongr; linarith
      _ = ε * (50 * (U * V) / S) := by ring
  have key : ε * Fc ≤ ε * (1000 * (U * V) * v / S + 19 * (S : ℝ) ^ 2 * Z / ε) := by
    calc ε * Fc ≤ 19 * ((S : ℝ) ^ 2 * (U * V * 15 * (2 * ε) / ((riemannZeta 2).re * cS) + Z)) *
          v := h
      _ = 19 * ((S : ℝ) ^ 2 * (U * V * 15 * (2 * ε) / ((riemannZeta 2).re * cS)) +
          (S : ℝ) ^ 2 * Z) * v := by ring
      _ ≤ 19 * (ε * (50 * (U * V) / S) + (S : ℝ) ^ 2 * Z) * v := by gcongr
      _ = 950 * (ε * (U * V) * v / S) + 19 * (S : ℝ) ^ 2 * Z * v := by ring
      _ ≤ 1000 * (ε * (U * V) * v / S) + 19 * (S : ℝ) ^ 2 * Z * 1 := by
          have h1 : 0 ≤ ε * (U * V) * v / S := by positivity
          have h2 : 0 ≤ 19 * (S : ℝ) ^ 2 * Z := by positivity
          gcongr
          norm_num
      _ = ε * (1000 * (U * V) * v / S + 19 * (S : ℝ) ^ 2 * Z / ε) := by
          field_simp
  exact le_of_mul_le_mul_left key hε

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

/-- `∫_{[0,1)} e(θ n) dθ = 1_{n = 0}`. -/
lemma integral_Ico_exp_int (n : ℤ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((θ * n : ℝ) : ℂ)) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [show (fun θ : ℝ => Complex.exp (2 * π * Complex.I * ((θ : ℂ) * n))) =
        fun θ : ℝ => Complex.exp (2 * π * Complex.I * n * θ) by
      funext θ; ring_nf]
    rw [this]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

lemma majorArcs_subset (x A₀ Y : ℝ) : majorArcs x A₀ Y ⊆ Set.Ico 0 1 :=
  fun _ h => ⟨h.1, h.2.1⟩

lemma measurableSet_majorArcs (x A₀ Y : ℝ) : MeasurableSet (majorArcs x A₀ Y) := by
  have : majorArcs x A₀ Y = Set.Ico 0 1 ∩ ⋃ k : ℕ, ⋃ c : ℤ,
      {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
    ext θ
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩; exact ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩
    · rintro ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩; exact ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩
  rw [this]
  refine measurableSet_Ico.inter (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun c => ?_)
  by_cases hP : 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = {θ : ℝ | |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
      ext θ; simp only [Set.mem_ofPred_eq]; tauto
    rw [this]
    exact measurableSet_le (by fun_prop) measurable_const
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = ∅ := by
      ext θ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; tauto
    rw [this]; exact MeasurableSet.empty

/-- `H_𝔪 = ψ(t/Y) 1_{t = b − a} − H_𝔐`. -/
lemma minorKernel_eq (x A₀ Y : ℝ) (t a b : ℤ) :
    minorKernel x A₀ Y t a b =
      (arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0) - majorKernel x A₀ Y t a b := by
  unfold minorKernel majorKernel
  have hint : IntegrableOn (fun θ : ℝ =>
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))) (Set.Ico 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ico_subset_Icc_self
  rw [setIntegral_sdiff (measurableSet_majorArcs x A₀ Y) hint (majorArcs_subset x A₀ Y), mul_sub]
  congr 2
  have := integral_Ico_exp_int (t - b + a)
  push_cast at this ⊢
  rw [this]

lemma dyadicBump_ne_zero {u : ℝ} (h : dyadicBump u ≠ 0) : 1 < u ∧ u < 4 := by
  unfold dyadicBump at h
  constructor
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    simp

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102E: auxiliary facts about the operator model

Small facts copied (with proofs) from prover D's heavier modules, so that the D8a chain imports
only `L102D_OpDefs`, `L102D_Good` and `L102D_Reduce`: the cutoffs, `vol 𝔐 ≤ 4L^{3A₀}/Y`, the
minor kernel bound, disjointness of the groups, the slot symmetrization as an averaging matrix,
list products, and the harmonic list sums. -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots ArtinPrimitiveRoots.L102D

/-! ## Cutoffs and kernels -/

lemma dyadicBump_nonneg' (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma abs_dyadicBump_le_one' (u : ℝ) : |dyadicBump u| ≤ 1 := by
  rw [abs_of_nonneg (dyadicBump_nonneg' u)]
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma abs_arcCutoff_le' (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

/-- `vol 𝔐 ≤ 4 L^{3A₀}/Y` (D's `volume_majorArcs_le`). -/
lemma volume_majorArcs_le' (x A₀ Y : ℝ) (hL : 1 ≤ log x) (hA₀ : 0 ≤ A₀) (hY : 0 < Y) :
    volume (majorArcs x A₀ Y) ≤ ENNReal.ofReal (4 * log x ^ (3 * A₀) / Y) := by
  set Q := log x ^ A₀
  set K₀ := ⌊Q⌋₊
  set ρ := 2 * Q / Y
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL hA₀
  have hsub : majorArcs x A₀ Y ⊆ {0} ∪ ⋃ k ∈ Icc 1 K₀,
      ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩ Set.Ioc 0 1) := by
    rintro θ ⟨h0, h1, k, hk1, hkQ, c, -, hc⟩
    rcases h0.lt_or_eq with h0 | h0
    · right
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Icc]
      refine ⟨k, ⟨hk1, Nat.le_floor hkQ⟩, ?_, h0, h1.le⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      calc circNorm (((k : ℤ) : ℝ) * θ) ≤ |((k : ℤ) : ℝ) * θ - c| := round_le _ c
        _ = k * |θ - c / k| := by
            have e : ((k : ℤ) : ℝ) * θ - c = k * (θ - c / k) := by
              push_cast; field_simp
            rw [e, abs_mul, abs_of_pos hk0]
        _ ≤ k * ρ := by gcongr
    · left; exact h0.symm
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ k ∈ Icc 1 K₀, volume ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩
      Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * (k * ρ)) := fun k hk =>
    volume_circNorm_le k (by have := (mem_Icc.1 hk).1; omega) _
  refine (sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK₀ : (K₀ : ℝ) ≤ Q := Nat.floor_le (by positivity)
  have hsum : ∑ k ∈ Icc 1 K₀, 2 * ((k : ℝ) * ρ) ≤ ∑ _k ∈ Icc 1 K₀, 2 * (Q * ρ) := by
    refine sum_le_sum fun k hk => ?_
    have : (k : ℝ) ≤ Q := (Nat.cast_le.2 (mem_Icc.1 hk).2).trans hK₀
    gcongr
  refine hsum.trans ?_
  rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  have h3 : log x ^ (3 * A₀) = Q * Q * Q := by
    rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add (by linarith),
      Real.rpow_add (by linarith)]
  rw [h3]
  have hρ : 0 ≤ ρ := by positivity
  calc (K₀ : ℝ) * (2 * (Q * ρ)) ≤ Q * (2 * (Q * ρ)) := by gcongr
    _ = 4 * (Q * Q * Q) / Y := by simp only [ρ]; ring

/-- `‖H_𝔪(t; a, b)‖ ≤ 1_{t = b − a} + 1_{|t| < 5Y} vol 𝔐`. -/
lemma norm_minorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖minorKernel x A₀ Y t a b‖ ≤ (if t - b + a = 0 then 1 else 0) +
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (volume (majorArcs x A₀ Y)).toReal := by
  rw [minorKernel_eq]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |arcCutoff ((t : ℝ) / Y)| ≤ 1 :=
      (abs_arcCutoff_le' _).trans (by split_ifs <;> norm_num)
    split_ifs <;> simp [h1]
  · unfold majorKernel
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hfin : volume (majorArcs x A₀ Y) < ⊤ :=
      (measure_mono (majorArcs_subset x A₀ Y)).trans_lt (by simp)
    have hint : ‖∫ θ in majorArcs x A₀ Y,
        Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤
        1 * volume.real (majorArcs x A₀ Y) := by
      refine norm_setIntegral_le_of_norm_le_const hfin fun θ _ => ?_
      rw [Complex.norm_exp]
      simp
    rw [one_mul] at hint
    exact mul_le_mul (abs_arcCutoff_le' _) hint (norm_nonneg _) (by split_ifs <;> norm_num)

/-! ## The groups for large `x` -/

lemma le_of_mem_primeGroup' {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

lemma prime_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) : q.Prime := by
  unfold primeGroup at h; exact (mem_filter.1 h).2.1

/-- For large `x` the prime groups are pairwise disjoint (D's `eventually_disjoint_groups`). -/
lemma eventually_disjoint_groups' {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · filter_upwards [eventually_rpow_le_rpow hij (ε := 1 / 3) (by norm_num),
        Filter.eventually_gt_atTop 0] with L h1 h2 _
      have : 0 < L ^ a j := by positivity
      linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup' hp).2
    have h2 := (le_of_mem_primeGroup' hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-! ## The slot symmetrization averages over orbits -/

section SlotSym

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

/-- The orbit relation of the slot permutations. -/
def orbRelE (s t : PhysState x a J U V) : Prop :=
  t.1.1 = s.1.1 ∧ ∀ i, Set.range (t.1.2 i) = Set.range (s.1.2 i)

lemma orbRelE_symm {s t : PhysState x a J U V} (h : orbRelE s t) : orbRelE t s :=
  ⟨h.1.symm, fun i => (h.2 i).symm⟩

lemma orbRelE_trans {s t u : PhysState x a J U V} (h1 : orbRelE s t) (h2 : orbRelE t u) :
    orbRelE s u :=
  ⟨h2.1.trans h1.1, fun i => (h2.2 i).trans (h1.2 i)⟩

open Classical in
lemma slotSym_apply' (s s' : PhysState x a J U V) :
    slotSym x a J U V s s' = if orbRelE s s' then
      ((univ.filter fun t => orbRelE s t).card : ℂ)⁻¹ else 0 := by
  unfold slotSym orbRelE
  by_cases h : s'.1.1 = s.1.1 ∧ ∀ i, Set.range (s'.1.2 i) = Set.range (s.1.2 i)
  · rw [if_pos ⟨h.1.symm, h.2⟩, if_pos h]; congr 2; convert rfl
  · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), if_neg h]

open Classical in
lemma orbit_card_eq' {s s' : PhysState x a J U V} (h : orbRelE s s') :
    (univ.filter fun t => orbRelE s t).card = (univ.filter fun t => orbRelE s' t).card := by
  congr 1; ext t; simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun ht => orbRelE_trans (orbRelE_symm h) ht, fun ht => orbRelE_trans h ht⟩

lemma slotSym_symm (s s' : PhysState x a J U V) :
    slotSym x a J U V s s' = slotSym x a J U V s' s := by
  classical
  simp only [slotSym_apply']
  by_cases h : orbRelE s s'
  · rw [if_pos h, if_pos (orbRelE_symm h), orbit_card_eq' h]
  · rw [if_neg h, if_neg (fun h' => h (orbRelE_symm h'))]

lemma norm_slotSym (s s' : PhysState x a J U V) :
    ‖slotSym x a J U V s s'‖ = (slotSym x a J U V s s').re := by
  classical
  rw [slotSym_apply']
  split_ifs
  · rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.norm_real, Complex.ofReal_re,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · simp

lemma sum_norm_slotSym_row (s : PhysState x a J U V) : ∑ s', ‖slotSym x a J U V s s'‖ = 1 := by
  classical
  simp only [norm_slotSym]
  rw [← Complex.re_sum]
  simp only [slotSym_apply']
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hpos : 0 < (univ.filter fun t => orbRelE s t).card :=
    card_pos.2 ⟨s, mem_filter.2 ⟨mem_univ _, rfl, fun i => rfl⟩⟩
  have : ((univ.filter fun t => orbRelE s t).card : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [mul_inv_cancel₀ this, Complex.one_re]

lemma sum_norm_slotSym_col (s' : PhysState x a J U V) : ∑ s, ‖slotSym x a J U V s s'‖ = 1 := by
  simp only [fun s => slotSym_symm (x := x) (a := a) (J := J) (U := U) (V := V) s s']
  exact sum_norm_slotSym_row s'

lemma slotSym_ne_zero' {s s' : PhysState x a J U V} (h : slotSym x a J U V s s' ≠ 0) :
    s.1.1 = s'.1.1 ∧ ∀ i, Set.range (s'.1.2 i) = Set.range (s.1.2 i) := by
  unfold slotSym at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

/-- Averaging an orbit-invariant function over a column of `S` returns its value. -/
lemma sum_norm_slotSym_mul_col (φ : PhysState x a J U V → ℝ)
    (hφ : ∀ s t, slotSym x a J U V s t ≠ 0 → φ s = φ t) (t : PhysState x a J U V) :
    ∑ s, ‖slotSym x a J U V s t‖ * φ s = φ t := by
  calc ∑ s, ‖slotSym x a J U V s t‖ * φ s = ∑ s, ‖slotSym x a J U V s t‖ * φ t := by
        refine sum_congr rfl fun s _ => ?_
        by_cases h : slotSym x a J U V s t = 0
        · rw [h, norm_zero, zero_mul, zero_mul]
        · rw [hφ s t h]
    _ = φ t := by rw [← sum_mul, sum_norm_slotSym_col, one_mul]

lemma sum_norm_slotSym_mul_row (φ : PhysState x a J U V → ℝ)
    (hφ : ∀ s t, slotSym x a J U V s t ≠ 0 → φ s = φ t) (t : PhysState x a J U V) :
    ∑ s, ‖slotSym x a J U V t s‖ * φ s = φ t := by
  calc ∑ s, ‖slotSym x a J U V t s‖ * φ s = ∑ s, ‖slotSym x a J U V t s‖ * φ t := by
        refine sum_congr rfl fun s _ => ?_
        by_cases h : slotSym x a J U V t s = 0
        · rw [h, norm_zero, zero_mul, zero_mul]
        · rw [hφ t s h]
    _ = φ t := by rw [← sum_mul, sum_norm_slotSym_row, one_mul]

end SlotSym

/-! ## List products -/

section Lists

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

lemma listProd_eq_pad_mul_last (ℓ : Fin K → Fin (J + 1) → ℕ) :
    listProd ℓ = padProd ℓ * lastProd ℓ := by
  unfold listProd padProd lastProd
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => Fin.prod_univ_castSucc (ℓ i)

lemma mem_listCands_grp {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ℓ ∈ listCands x a J) (i j) :
    ℓ i j ∈ primeGroup x (a i) :=
  Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 h i) j

/-- A list of distinct primes (disjoint groups, injective in each group) divides every common
multiple of its entries. -/
lemma listProd_dvd_of
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    {ℓ : Fin K → Fin (J + 1) → ℕ} (hℓ : ℓ ∈ listCands x a J)
    (hinj : ∀ i, Function.Injective (ℓ i)) {n : ℕ} (hdvd : ∀ i j, ℓ i j ∣ n) :
    listProd ℓ ∣ n := by
  have hgrp := mem_listCands_grp hℓ
  have hprime : ∀ i j, (ℓ i j).Prime := fun i j => prime_of_mem_primeGroup (hgrp i j)
  have hne : ∀ q q' : Fin K × Fin (J + 1), q ≠ q' → ℓ q.1 q.2 ≠ ℓ q'.1 q'.2 := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hq heq
    by_cases hi : i = i'
    · subst hi
      have : j = j' := hinj i heq
      exact hq (by rw [this])
    · exact Finset.disjoint_left.1 (hdisj i i' hi) (hgrp i j) (heq ▸ hgrp i' j')
  have hZ : (∏ q : Fin K × Fin (J + 1), ((ℓ q.1 q.2 : ℕ) : ℤ)) ∣ (n : ℤ) := by
    refine Fintype.prod_dvd_of_coprime (fun q q' hqq => ?_) fun q => ?_
    · simp only [Function.onFun]
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes (hprime q.1 q.2) (hprime q'.1 q'.2)).2 (hne q q' hqq)
    · exact_mod_cast hdvd q.1 q.2
  have : ((listProd ℓ : ℕ) : ℤ) ∣ (n : ℤ) := by
    unfold listProd; push_cast
    have e := Fintype.prod_prod_type' (fun (i : Fin K) (j : Fin (J + 1)) => ((ℓ i j : ℕ) : ℤ))
    rw [e] at hZ
    exact hZ
  exact_mod_cast this

lemma listProd_pos {ℓ : Fin K → Fin (J + 1) → ℕ} (hℓ : ℓ ∈ listCands x a J) : 0 < listProd ℓ :=
  prod_pos fun i _ => prod_pos fun j _ =>
    (prime_of_mem_primeGroup (mem_listCands_grp hℓ i j)).pos

lemma lastProd_pos {ℓ : Fin K → Fin (J + 1) → ℕ} (hℓ : ℓ ∈ listCands x a J) : 0 < lastProd ℓ :=
  prod_pos fun i _ => (prime_of_mem_primeGroup (mem_listCands_grp hℓ i (Fin.last J))).pos

lemma sum_inv_listProd' (J : ℕ) :
    ∑ ℓ ∈ listCands x a J, (1 : ℝ) / listProd ℓ =
      ∏ i, (groupReciprocalSum x (a i)) ^ (J + 1) := by
  unfold listCands listProd
  calc ∑ ℓ ∈ Fintype.piFinset (fun i => Fintype.piFinset fun _ : Fin (J + 1) => primeGroup x (a i)),
        (1 : ℝ) / ((∏ i, ∏ j, ℓ i j : ℕ) : ℝ)
      = ∑ ℓ ∈ Fintype.piFinset (fun i => Fintype.piFinset fun _ : Fin (J + 1) => primeGroup x (a i)),
          ∏ i, ∏ j, (1 : ℝ) / (ℓ i j : ℝ) := by
        refine sum_congr rfl fun ℓ _ => ?_
        push_cast
        simp only [one_div, prod_inv_distrib]
    _ = ∏ i, ∑ ℓi ∈ Fintype.piFinset (fun _ : Fin (J + 1) => primeGroup x (a i)),
          ∏ j, (1 : ℝ) / (ℓi j : ℝ) :=
        (Finset.prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin (J + 1) => primeGroup x (a i))
          (fun _ ℓi => ∏ j, (1 : ℝ) / (ℓi j : ℝ))).symm
    _ = ∏ i, (groupReciprocalSum x (a i)) ^ (J + 1) := by
        refine prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_univ_sum (fun _ : Fin (J + 1) => primeGroup x (a i))
          (fun _ (q : ℕ) => (1 : ℝ) / q)]
        simp [groupReciprocalSum]

/-- `∑_{p} ∏ᵢ 1/(pᵢ Vᵢ) ≤ 1` over label tuples. -/
lemma sum_last_weight_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∑ p ∈ Fintype.piFinset (fun i => primeGroup x (a i)),
      ∏ i, 1 / ((p i : ℝ) * groupReciprocalSum x (a i)) ≤ 1 := by
  rw [← Finset.prod_univ_sum (fun i => primeGroup x (a i))
    (fun i (q : ℕ) => 1 / ((q : ℝ) * groupReciprocalSum x (a i)))]
  have hV0 : ∀ i, 0 ≤ groupReciprocalSum x (a i) := fun i => sum_nonneg fun p _ => by positivity
  refine prod_le_one (fun i _ => sum_nonneg fun q _ => ?_) fun i _ => ?_
  · have := hV0 i; positivity
  · have hV : groupReciprocalSum x (a i) = ∑ q ∈ primeGroup x (a i), 1 / (q : ℝ) := rfl
    rw [show ∑ q ∈ primeGroup x (a i), 1 / ((q : ℝ) * groupReciprocalSum x (a i)) =
        (∑ q ∈ primeGroup x (a i), 1 / (q : ℝ)) / groupReciprocalSum x (a i) by
      rw [sum_div]; exact sum_congr rfl fun q _ => by rw [div_div], ← hV]
    exact div_self_le_one _

open Classical in
/-- **The harmonic list sum.** `σ ∏Vᵢ⁻¹ ∑_{ℓ, ℓ'} 1_{pads agree}/(listProd ℓ · lastProd ℓ') ≤ 1`. -/
lemma list_pair_sum_le (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) :
    stateNorm x a J * ((∏ i, (groupReciprocalSum x (a i))⁻¹) *
      ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
        (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
          (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0)) ≤ 1 := by
  have hinner : ∀ ℓ ∈ listCands x a J, (∏ i, (groupReciprocalSum x (a i))⁻¹) *
      ∑ ℓ' ∈ listCands x a J, (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
        (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) ≤ 1 / (listProd ℓ : ℝ) := by
    intro ℓ _
    set T := (listCands x a J).filter fun ℓ' : Fin K → Fin (J + 1) → ℕ =>
      ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc
    set last : (Fin K → Fin (J + 1) → ℕ) → (Fin K → ℕ) := fun ℓ' i => ℓ' i (Fin.last J)
    have hinj : Set.InjOn last ↑T := by
      intro ℓ₁ h₁ ℓ₂ h₂ heq
      have h₁' := (mem_filter.1 h₁).2
      have h₂' := (mem_filter.1 h₂).2
      funext i j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact congrFun heq i
      · rw [h₁' i j, h₂' i j]
    have hmaps : T.image last ⊆ Fintype.piFinset (fun i => primeGroup x (a i)) := by
      intro p hp
      obtain ⟨ℓ', h', rfl⟩ := mem_image.1 hp
      exact Fintype.mem_piFinset.2 fun i => mem_listCands_grp (mem_filter.1 h').1 i _
    have hw : ∀ ℓ' ∈ T, (∏ i, (groupReciprocalSum x (a i))⁻¹) * (1 / (lastProd ℓ' : ℝ)) =
        ∏ i, 1 / ((last ℓ' i : ℝ) * groupReciprocalSum x (a i)) := by
      intro ℓ' _
      unfold lastProd; push_cast
      rw [one_div, ← prod_inv_distrib, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [one_div, mul_inv, mul_comm]
    have hV0 : ∀ i, 0 ≤ groupReciprocalSum x (a i) := fun i => (hVpos i).le
    have hlp : (0 : ℝ) ≤ 1 / (listProd ℓ : ℝ) := by positivity
    calc (∏ i, (groupReciprocalSum x (a i))⁻¹) *
          ∑ ℓ' ∈ listCands x a J, (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
            (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0)
        = 1 / (listProd ℓ : ℝ) * ∑ ℓ' ∈ T,
            (∏ i, (groupReciprocalSum x (a i))⁻¹) * (1 / (lastProd ℓ' : ℝ)) := by
          rw [← sum_filter, mul_sum, mul_sum]
          refine sum_congr rfl fun ℓ' _ => ?_
          ring
      _ = 1 / (listProd ℓ : ℝ) * ∑ p ∈ T.image last,
            ∏ i, 1 / ((p i : ℝ) * groupReciprocalSum x (a i)) := by
          rw [sum_image hinj, sum_congr rfl hw]
      _ ≤ 1 / (listProd ℓ : ℝ) * ∑ p ∈ Fintype.piFinset (fun i => primeGroup x (a i)),
            ∏ i, 1 / ((p i : ℝ) * groupReciprocalSum x (a i)) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hmaps ?_) hlp
          intro p _ _
          refine prod_nonneg fun i _ => ?_
          have := hV0 i
          positivity
      _ ≤ 1 / (listProd ℓ : ℝ) * 1 := by gcongr; exact sum_last_weight_le x a
      _ = 1 / (listProd ℓ : ℝ) := mul_one _
  have hσ : stateNorm x a J * ∏ i, (groupReciprocalSum x (a i)) ^ (J + 1) = 1 := by
    unfold stateNorm
    rw [← prod_mul_distrib]
    refine prod_eq_one fun i _ => ?_
    rw [← mul_pow, inv_mul_cancel₀ (hVpos i).ne', one_pow]
  have hσ0 : 0 ≤ stateNorm x a J := prod_nonneg fun i _ => by have := hVpos i; positivity
  calc stateNorm x a J * ((∏ i, (groupReciprocalSum x (a i))⁻¹) *
        ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
          (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
            (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0))
      = stateNorm x a J * ∑ ℓ ∈ listCands x a J, ((∏ i, (groupReciprocalSum x (a i))⁻¹) *
          ∑ ℓ' ∈ listCands x a J,
          (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
            (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0)) := by rw [mul_sum]
    _ ≤ stateNorm x a J * ∑ ℓ ∈ listCands x a J, (1 : ℝ) / listProd ℓ := by
        gcongr with ℓ hℓ; exact hinner ℓ hℓ
    _ = 1 := by rw [sum_inv_listProd', hσ]

end Lists

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E: removing `G` and `S` from the pairing ([21] (4.56), first sentences)

`‖⟨f, STSf⟩_σ − ⟨f, GSTSGf⟩_σ‖ ≤ σ ∑_{t,t'} ‖T(t,t')‖ ‖f(t)‖ ‖f(t')‖ (b(t) + b(t'))`, `b = 1 − g`
the badness indicator: `GMG` differs from `M` only where an endpoint is bad, `|STS| ≤ S|T|S`
entrywise, and `‖f‖`, `b` are constant on slot orbits (goodness depends only on the unordered
lists, `isGoodRatio_congr`), so the averaging matrix `S` disappears. Then the state sums are
re-indexed by list pairs and position pairs. -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots ArtinPrimitiveRoots.L102D

section Algebra

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

open Classical in
/-- The badness indicator of an ambient state. -/
noncomputable def badA (x Y : ℝ) {K : ℕ} (a : Fin K → ℝ) {J : ℕ}
    (z : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) : ℝ :=
  if IsGoodRatio x Y a z.2 (rootRatio z.1.1 z.1.2) then 0 else 1

lemma badA_nonneg (Y : ℝ) (z : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) : 0 ≤ badA x Y a z := by
  unfold badA; split_ifs <;> norm_num

open Classical in
lemma pairing_sub_le (Y : ℝ) (α β : ℕ → ℂ)
    (M : Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ) (hσ : 0 ≤ stateNorm x a J) :
    ‖opPairing x a J U V α β M -
        opPairing x a J U V α β (goodProj x Y a J U V * M * goodProj x Y a J U V)‖ ≤
      stateNorm x a J * ∑ s, ∑ s', ‖M s s'‖ *
        (‖endpointVec x a J U V α β s‖ * ‖endpointVec x a J U V α β s'‖ *
          (badA x Y a s.1 + badA x Y a s'.1)) := by
  set f := endpointVec x a J U V α β
  set g : PhysState x a J U V → ℂ := fun s =>
    if IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2) then 1 else 0
  have hG : goodProj x Y a J U V = Matrix.diagonal g := rfl
  have hGMG : ∀ s s', (goodProj x Y a J U V * M * goodProj x Y a J U V) s s' =
      g s * M s s' * g s' := by
    intro s s'; rw [hG, Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold opPairing
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ]
  gcongr
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s' _ => ?_)
  rw [hGMG]
  have e : (starRingEnd ℂ) (f s) * M s s' * f s' -
      (starRingEnd ℂ) (f s) * (g s * M s s' * g s') * f s' =
      (starRingEnd ℂ) (f s) * M s s' * f s' * (1 - g s * g s') := by ring
  rw [e, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
  have hb : ‖1 - g s * g s'‖ ≤ badA x Y a s.1 + badA x Y a s'.1 := by
    simp only [g, badA]
    split_ifs <;> norm_num
  calc ‖f s‖ * ‖M s s'‖ * ‖f s'‖ * ‖1 - g s * g s'‖ ≤
        ‖f s‖ * ‖M s s'‖ * ‖f s'‖ * (badA x Y a s.1 + badA x Y a s'.1) := by gcongr
    _ = _ := by ring

lemma norm_mul3_apply_le {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (s s' : ι) :
    ‖(A * B * A) s s'‖ ≤ ∑ t, ∑ t', ‖A s t‖ * ‖B t t'‖ * ‖A t' s'‖ := by
  calc ‖(A * B * A) s s'‖ = ‖∑ t', (A * B) s t' * A t' s'‖ := by rw [Matrix.mul_apply]
    _ ≤ ∑ t', ‖(A * B) s t'‖ * ‖A t' s'‖ :=
        (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun t' _ => norm_mul _ _))
    _ ≤ ∑ t', (∑ t, ‖A s t‖ * ‖B t t'‖) * ‖A t' s'‖ := by
        gcongr with t'
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun t _ => norm_mul _ _))
    _ = ∑ t', ∑ t, ‖A s t‖ * ‖B t t'‖ * ‖A t' s'‖ := by simp only [sum_mul]
    _ = ∑ t, ∑ t', ‖A s t‖ * ‖B t t'‖ * ‖A t' s'‖ := sum_comm

/-- `S` disappears against orbit-invariant weights. -/
lemma sum_STS_le (T : Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ)
    (φ₁ ψ₁ φ₂ ψ₂ : PhysState x a J U V → ℝ)
    (h₁ : ∀ s, 0 ≤ φ₁ s) (h₂ : ∀ s, 0 ≤ ψ₁ s) (h₃ : ∀ s, 0 ≤ φ₂ s) (h₄ : ∀ s, 0 ≤ ψ₂ s)
    (i₁ : ∀ s t, slotSym x a J U V s t ≠ 0 → φ₁ s = φ₁ t)
    (i₂ : ∀ s t, slotSym x a J U V s t ≠ 0 → ψ₁ s = ψ₁ t)
    (i₃ : ∀ s t, slotSym x a J U V s t ≠ 0 → φ₂ s = φ₂ t)
    (i₄ : ∀ s t, slotSym x a J U V s t ≠ 0 → ψ₂ s = ψ₂ t) :
    ∑ s, ∑ s', ‖(slotSym x a J U V * T * slotSym x a J U V) s s'‖ *
        (φ₁ s * ψ₁ s' + φ₂ s * ψ₂ s') ≤
      ∑ t, ∑ t', ‖T t t'‖ * (φ₁ t * ψ₁ t' + φ₂ t * ψ₂ t') := by
  set S := slotSym x a J U V
  set w : PhysState x a J U V → PhysState x a J U V → ℝ := fun s s' =>
    φ₁ s * ψ₁ s' + φ₂ s * ψ₂ s'
  have hw : ∀ s s', 0 ≤ w s s' := fun s s' => by
    have := h₁ s; have := h₂ s'; have := h₃ s; have := h₄ s'; simp only [w]; positivity
  calc ∑ s, ∑ s', ‖(S * T * S) s s'‖ * w s s'
      ≤ ∑ s, ∑ s', (∑ t, ∑ t', ‖S s t‖ * ‖T t t'‖ * ‖S t' s'‖) * w s s' := by
        gcongr with s _ s' _
        · exact hw s s'
        · exact norm_mul3_apply_le S T s s'
    _ = ∑ s, ∑ s', ∑ t, ∑ t', ‖T t t'‖ * (‖S s t‖ * ‖S t' s'‖ * w s s') := by
        refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun t _ => ?_
        rw [sum_mul]
        exact sum_congr rfl fun t' _ => by ring
    _ = ∑ s, ∑ t, ∑ t', ∑ s', ‖T t t'‖ * (‖S s t‖ * ‖S t' s'‖ * w s s') := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun t _ => sum_comm
    _ = ∑ t, ∑ t', ∑ s, ∑ s', ‖T t t'‖ * (‖S s t‖ * ‖S t' s'‖ * w s s') := by
        rw [sum_comm]
        exact sum_congr rfl fun t _ => sum_comm
    _ = ∑ t, ∑ t', ‖T t t'‖ * (φ₁ t * ψ₁ t' + φ₂ t * ψ₂ t') := by
        refine sum_congr rfl fun t _ => sum_congr rfl fun t' _ => ?_
        have e : ∑ s, ∑ s', ‖T t t'‖ * (‖S s t‖ * ‖S t' s'‖ * w s s') =
            ‖T t t'‖ * ((∑ s, ‖S s t‖ * φ₁ s) * (∑ s', ‖S t' s'‖ * ψ₁ s') +
              (∑ s, ‖S s t‖ * φ₂ s) * (∑ s', ‖S t' s'‖ * ψ₂ s')) := by
          rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun s _ => ?_
          rw [← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun s' _ => ?_
          simp only [w]; ring
        rw [e, sum_norm_slotSym_mul_col φ₁ i₁, sum_norm_slotSym_mul_row ψ₁ i₂,
          sum_norm_slotSym_mul_col φ₂ i₃, sum_norm_slotSym_mul_row ψ₂ i₄]

lemma endpointVec_eq_of_slotSym (α β : ℕ → ℂ) {s t : PhysState x a J U V}
    (h : slotSym x a J U V s t ≠ 0) :
    endpointVec x a J U V α β s = endpointVec x a J U V α β t := by
  have h1 := (slotSym_ne_zero' h).1
  simp only [endpointVec, h1]

lemma badA_eq_of_slotSym (Y : ℝ) {s t : PhysState x a J U V} (h : slotSym x a J U V s t ≠ 0) :
    badA x Y a s.1 = badA x Y a t.1 := by
  obtain ⟨h1, h2⟩ := slotSym_ne_zero' h
  have hs := (mem_filter.1 s.2).2.1
  have ht := (mem_filter.1 t.2).2.1
  unfold badA
  rw [h1, isGoodRatio_congr hs ht h2]

/-- **Removing `G` and `S`.** -/
theorem pairing_STS_sub_le (A₀ Y : ℝ) (d₀ : ℕ) (α β : ℕ → ℂ) (hσ : 0 ≤ stateNorm x a J) :
    ‖opPairing x a J U V α β (slotSym x a J U V * rowOp x a A₀ Y J d₀ U V * slotSym x a J U V) -
        opPairing x a J U V α β (opA x a A₀ Y J d₀ U V)‖ ≤
      stateNorm x a J * ∑ t, ∑ t', ‖rowOp x a A₀ Y J d₀ U V t t'‖ *
        (‖endpointVec x a J U V α β t‖ * ‖endpointVec x a J U V α β t'‖ *
          (badA x Y a t.1 + badA x Y a t'.1)) := by
  set M := slotSym x a J U V * rowOp x a A₀ Y J d₀ U V * slotSym x a J U V
  have hA : opA x a A₀ Y J d₀ U V = goodProj x Y a J U V * M * goodProj x Y a J U V := by
    simp only [opA, M, Matrix.mul_assoc]
  rw [hA]
  refine (pairing_sub_le Y α β M hσ).trans (mul_le_mul_of_nonneg_left ?_ hσ)
  set F : PhysState x a J U V → ℝ := fun s => ‖endpointVec x a J U V α β s‖
  set b : PhysState x a J U V → ℝ := fun s => badA x Y a s.1
  have hF : ∀ s t, slotSym x a J U V s t ≠ 0 → F s = F t := fun s t h => by
    simp only [F, endpointVec_eq_of_slotSym α β h]
  have hb : ∀ s t, slotSym x a J U V s t ≠ 0 → b s = b t := fun s t h =>
    badA_eq_of_slotSym Y h
  have hFb : ∀ s t, slotSym x a J U V s t ≠ 0 → F s * b s = F t * b t := fun s t h => by
    rw [hF s t h, hb s t h]
  have key := sum_STS_le (rowOp x a A₀ Y J d₀ U V) (fun s => F s * b s) F F (fun s => F s * b s)
    (fun s => mul_nonneg (norm_nonneg _) (badA_nonneg Y _)) (fun s => norm_nonneg _)
    (fun s => norm_nonneg _) (fun s => mul_nonneg (norm_nonneg _) (badA_nonneg Y _))
    hFb hF hF hFb
  have e1 : ∑ s, ∑ s', ‖M s s'‖ * (‖endpointVec x a J U V α β s‖ *
      ‖endpointVec x a J U V α β s'‖ * (badA x Y a s.1 + badA x Y a s'.1)) =
      ∑ s, ∑ s', ‖M s s'‖ * (F s * b s * F s' + F s * (F s' * b s')) :=
    sum_congr rfl fun s _ => sum_congr rfl fun s' _ => by simp only [F, b]; ring
  have e2 : ∑ t, ∑ t', ‖rowOp x a A₀ Y J d₀ U V t t'‖ * (‖endpointVec x a J U V α β t‖ *
      ‖endpointVec x a J U V α β t'‖ * (badA x Y a t.1 + badA x Y a t'.1)) =
      ∑ t, ∑ t', ‖rowOp x a A₀ Y J d₀ U V t t'‖ * (F t * b t * F t' + F t * (F t' * b t')) :=
    sum_congr rfl fun s _ => sum_congr rfl fun s' _ => by simp only [F, b]; ring
  rw [e1, e2]
  exact key

end Algebra

/-! ## Re-indexing the state sums by list pairs and position pairs -/

section Reindex

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

/-- Validity of an ambient state: injective lists whose entries divide the first coordinate. -/
def ValidSt {K J : ℕ} (z : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) : Prop :=
  (∀ i, Function.Injective (z.2 i)) ∧ ∀ i j, z.2 i j ∣ z.1.1

lemma sum_subtype_pair {α : Type*} (A : Finset α) (F : α → α → ℝ) :
    ∑ t : {s // s ∈ A}, ∑ t' : {s // s ∈ A}, F t.1 t'.1 = ∑ w ∈ A ×ˢ A, F w.1 w.2 := by
  rw [sum_product, ← Finset.sum_coe_sort A]
  exact sum_congr rfl fun t _ => Finset.sum_coe_sort A (F t.1)

open Classical in
lemma sum_states_le (F : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ) →
      (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ) → ℝ) (hF : ∀ z z', 0 ≤ F z z') :
    ∑ t : PhysState x a J U V, ∑ t' : PhysState x a J U V, F t.1 t'.1 ≤
      ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J, ∑ PQ ∈ posBox U V ×ˢ posBox U V,
        if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then F (PQ.1, ℓ) (PQ.2, ℓ') else 0 := by
  have e1 := sum_subtype_pair (stateSet x a J U V) F
  set A := stateSet x a J U V
  rw [e1]
  set g : ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) × ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) →
      ((Fin K → Fin (J + 1) → ℕ) × (Fin K → Fin (J + 1) → ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) :=
    fun w => ((w.1.2, w.2.2), (w.1.1, w.2.1))
  set G : ((Fin K → Fin (J + 1) → ℕ) × (Fin K → Fin (J + 1) → ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → ℝ :=
    fun v => if ValidSt (v.2.1, v.1.1) ∧ ValidSt (v.2.2, v.1.2) then
      F (v.2.1, v.1.1) (v.2.2, v.1.2) else 0
  have hinj : Set.InjOn g ↑(A ×ˢ A) := by
    intro w _ w' _ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact Prod.ext (Prod.ext h3 h1) (Prod.ext h4 h2)
  have hval : ∀ z ∈ A, ValidSt z := fun z hz => (mem_filter.1 hz).2
  have e2 : ∑ w ∈ A ×ˢ A, F w.1 w.2 = ∑ v ∈ (A ×ˢ A).image g, G v := by
    rw [sum_image hinj]
    refine sum_congr rfl fun w hw => ?_
    obtain ⟨hw1, hw2⟩ := mem_product.1 hw
    simp only [G, g, Prod.mk.eta]
    rw [if_pos ⟨hval _ hw1, hval _ hw2⟩]
  rw [e2]
  have hsub : (A ×ˢ A).image g ⊆
      (listCands x a J ×ˢ listCands x a J) ×ˢ (posBox U V ×ˢ posBox U V) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hv
    obtain ⟨hw1, hw2⟩ := mem_product.1 hw
    have m1 := mem_product.1 (mem_filter.1 hw1).1
    have m2 := mem_product.1 (mem_filter.1 hw2).1
    exact mem_product.2 ⟨mem_product.2 ⟨m1.2, m2.2⟩, mem_product.2 ⟨m1.1, m2.1⟩⟩
  have hG0 : ∀ v, 0 ≤ G v := fun v => by simp only [G]; split_ifs; exacts [hF _ _, le_rfl]
  refine (sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => hG0 v).trans (le_of_eq ?_)
  rw [sum_product, sum_product]

end Reindex

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E: one pair of lists

For fixed source and target lists `ℓ, ℓ'` the bad part of the edge sum is at most
`∏Vᵢ⁻¹ (1 + 44 L^{3A₀}) Φ / (listProd ℓ · lastProd ℓ')`, by the core count at every determinant
value `t = det/D` with `|t| ≤ 5Y` (the raw value `b − a` among them). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots ArtinPrimitiveRoots.L102D

/-! ## Coprimality and squarefreeness of the edge modulus -/

lemma sqf_prod_of_inj {γ : Type*} [Fintype γ] (e : γ → ℕ) (hp : ∀ i, (e i).Prime)
    (hi : Function.Injective e) : Squarefree (∏ i, e i) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun i _ => Irreducible.squarefree (hp i)
  intro i _ j _ hij
  exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hp i) (hp j)).2 (hi.ne hij))

lemma coprime_sqf_of_inj {α β : Type*} [Fintype α] [Fintype β] (e₁ : α → ℕ) (e₂ : β → ℕ)
    (hp₁ : ∀ i, (e₁ i).Prime) (hp₂ : ∀ j, (e₂ j).Prime) (hi₁ : Function.Injective e₁)
    (hi₂ : Function.Injective e₂) (hd : ∀ i j, e₁ i ≠ e₂ j) :
    Nat.Coprime (∏ i, e₁ i) (∏ j, e₂ j) ∧ Squarefree ((∏ i, e₁ i) * ∏ j, e₂ j) := by
  have hc : Nat.Coprime (∏ i, e₁ i) (∏ j, e₂ j) :=
    Nat.Coprime.prod_left fun i _ => Nat.Coprime.prod_right fun j _ =>
      (Nat.coprime_primes (hp₁ i) (hp₂ j)).2 (hd i j)
  exact ⟨hc, Nat.squarefree_mul_iff.2 ⟨hc, sqf_prod_of_inj e₁ hp₁ hi₁, sqf_prod_of_inj e₂ hp₂ hi₂⟩⟩

/-! ## The ambient row kernel -/

open Classical in
/-- The body of `rowOp` on ambient pairs. -/
noncomputable def rowA (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ)
    (z z' : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) : ℂ :=
  if (∀ i (j : Fin J), z'.2 i j.castSucc = z.2 i j.castSucc) ∧
      (∀ i, z'.2 i (Fin.last J) ∉ Set.range (z.2 i)) ∧
      d₀ ≤ padProd z.2 ∧ padProd z.2 < 2 * d₀ then
    (((∏ i, (groupReciprocalSum x (a i))⁻¹) * ((d₀ : ℝ) / padProd z.2) *
        dyadicBump ((lastProd z.2 : ℝ) / Y) * dyadicBump ((lastProd z'.2 : ℝ) / Y) *
        (1 / 2 : ℝ) ^ (excessOmega x a J z.1.1 + excessOmega x a J z'.1.1) : ℝ) : ℂ) *
      minorKernel x A₀ Y (((z.1.1 : ℤ) * z'.1.2 - (z.1.2 : ℤ) * z'.1.1) / (padProd z.2 : ℤ))
        (lastProd z'.2) (lastProd z.2)
  else 0

/-! ## Global facts at one `x` -/

/-- The facts used at one `x` (all hold for large `x`). -/
structure Glob (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (A₀ Y U V c ε E η₁ Pm : ℝ) : Prop where
  hx0 : 0 < x
  hL1 : 1 ≤ log x
  hU : 0 < U
  hV : 0 < V
  hY1 : 1 ≤ Y
  hRC : RootCountAt x U V c
  hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))
  hPm1 : 1 ≤ Pm
  hPm : ∀ i, ∀ p ∈ primeGroup x (a i), (p : ℝ) ≤ Pm
  hE : E = Pm ^ (K * (J + 3))
  hε : 0 < ε
  hεE : E * ε ≤ exp (-(log x ^ (0.2 : ℝ)))
  hε10 : 10 * E ^ 3 * ε ≤ 1
  hEx : E ≤ exp (log x ^ (0.98 : ℝ))
  haL : ∀ i, a i ≤ 0.2
  hη : 0 ≤ η₁
  hGW : ∀ ℓ : Fin K → Fin (J + 1) → ℕ, (∀ i j, ℓ i j ∈ primeGroup x (a i)) →
    log x ^ (0.1 : ℝ) - 2 ≤ log Y →
    (volume ({r | ¬ IsGoodRatioW x Y a ℓ r} ∩ Set.Ioc 0 1)).toReal ≤ η₁
  hlast : ∀ ℓ ∈ listCands x a J, exp (log x ^ (0.1 : ℝ)) ≤ (lastProd ℓ : ℝ)
  hvolM : (volume (majorArcs x A₀ Y)).toReal ≤ 4 * log x ^ (3 * A₀) / Y
  hA₀ : 0 ≤ A₀

/-- `Φ = 1000 UV η₁ + 19 E³ UV x^{-c}/ε`. -/
noncomputable def PhiE (x U V c ε E η₁ : ℝ) : ℝ :=
  1000 * (U * V) * η₁ + 19 * E ^ 3 * (U * V * x ^ (-c)) / ε

section Bounds

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {A₀ Y U V c ε E η₁ Pm : ℝ}

lemma Glob.E_ge_one (G : Glob x a J A₀ Y U V c ε E η₁ Pm) : 1 ≤ E := by
  rw [G.hE]; exact one_le_pow₀ G.hPm1

lemma Glob.phi_nonneg (G : Glob x a J A₀ Y U V c ε E η₁ Pm) : 0 ≤ PhiE x U V c ε E η₁ := by
  have := G.hU; have := G.hV; have := G.hη; have := G.hε
  have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg G.hx0.le _
  have := G.E_ge_one
  unfold PhiE; positivity

lemma prod_cast_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℕ) {Pm : ℝ}
    (h : ∀ i ∈ s, (f i : ℝ) ≤ Pm) : ((∏ i ∈ s, f i : ℕ) : ℝ) ≤ Pm ^ s.card := by
  push_cast
  calc ∏ i ∈ s, (f i : ℝ) ≤ ∏ _i ∈ s, Pm := prod_le_prod (fun i _ => Nat.cast_nonneg _) h
    _ = Pm ^ s.card := prod_const _

lemma Glob.listProd_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) : (listProd ℓ : ℝ) ≤ Pm ^ (K * (J + 1)) := by
  unfold listProd
  have h1 : ((∏ i, ∏ j, ℓ i j : ℕ) : ℝ) ≤ ∏ _i : Fin K, Pm ^ (J + 1) := by
    push_cast
    refine prod_le_prod (fun i _ => prod_nonneg fun j _ => Nat.cast_nonneg _) fun i _ => ?_
    have := prod_cast_le_pow (univ : Finset (Fin (J + 1))) (ℓ i)
      (fun j _ => G.hPm i _ (mem_listCands_grp hℓ i j))
    push_cast at this; simpa using this
  rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm] at h1
  exact h1

lemma Glob.lastProd_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) : (lastProd ℓ : ℝ) ≤ Pm ^ K := by
  unfold lastProd
  have := prod_cast_le_pow (univ : Finset (Fin K)) (fun i => ℓ i (Fin.last J))
    (fun i _ => G.hPm i _ (mem_listCands_grp hℓ i _))
  simpa using this

lemma Glob.padProd_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) : (padProd ℓ : ℝ) ≤ Pm ^ (K * J) := by
  unfold padProd
  have h1 : ((∏ i, ∏ j : Fin J, ℓ i j.castSucc : ℕ) : ℝ) ≤ ∏ _i : Fin K, Pm ^ J := by
    push_cast
    refine prod_le_prod (fun i _ => prod_nonneg fun j _ => Nat.cast_nonneg _) fun i _ => ?_
    have := prod_cast_le_pow (univ : Finset (Fin J)) (fun j => ℓ i j.castSucc)
      (fun j _ => G.hPm i _ (mem_listCands_grp hℓ i _))
    push_cast at this; simpa using this
  rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm] at h1
  exact h1

lemma Glob.omitProd_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) (o : Fin K → Fin (J + 1)) :
    (omitProd ℓ o : ℝ) ≤ Pm ^ (K * (J + 1)) := by
  refine le_trans ?_ (G.listProd_le hℓ)
  have hpos : ∀ i j, 1 ≤ ℓ i j := fun i j =>
    (prime_of_mem_primeGroup (mem_listCands_grp hℓ i j)).one_lt.le
  have : omitProd ℓ o ≤ listProd ℓ := by
    unfold omitProd listProd
    exact prod_le_prod' fun i _ =>
      prod_le_prod_of_subset_of_one_le' (erase_subset _ _) fun j _ _ => hpos i j
  exact_mod_cast this

lemma Glob.tuple_prod_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm) (T : Fin K → ℕ)
    (h : ∀ i, T i = 1 ∨ T i ∈ primeGroup x (a i)) : ((∏ i, T i : ℕ) : ℝ) ≤ Pm ^ K := by
  have := prod_cast_le_pow (Pm := Pm) (univ : Finset (Fin K)) T fun i _ => by
    rcases h i with h1 | h1
    · rw [h1]; exact_mod_cast G.hPm1
    · exact G.hPm i _ h1
  simpa using this

/-- **Fattening for a list.** -/
lemma Glob.fat (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) (hYP : Y ≤ Pm ^ K) :
    ∀ r ∈ {r | ¬ IsGoodRatio x Y a ℓ r}, 0 ≤ r → r < 1 → ∀ r', |r' - r| ≤ ε →
      r' ∈ {r | ¬ IsGoodRatioW x Y a ℓ r} := by
  intro r hr _ _ r' hr'
  have hE1 := G.E_ge_one
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos G.hY1
  have hPmK : (1 : ℝ) ≤ Pm ^ K := one_le_pow₀ G.hPm1
  have hεE1 : E * ε ≤ 1 := G.hεE.trans (by
    rw [exp_le_one_iff, neg_nonpos]; exact Real.rpow_nonneg (by linarith [G.hL1]) _)
  have hε0 := G.hε.le
  have hPm0 : 0 ≤ Pm := by linarith [G.hPm1]
  refine not_goodW_of_not_good (ε := ε) ?_ ?_ hr' hr
  · intro o l hl1 hlY
    have homit := G.omitProd_le hℓ o
    have hl : (l : ℝ) * omitProd ℓ o ≤ Y ^ (0.2 : ℝ) * Pm ^ (K * (J + 1)) :=
      mul_le_mul hlY homit (Nat.cast_nonneg _) (by positivity)
    have h07 : 0 < Y ^ (0.7 : ℝ) := Real.rpow_pos_of_pos hY0 _
    have hYY : Y ^ (0.2 : ℝ) * Y ^ (0.7 : ℝ) ≤ Y := by
      rw [← Real.rpow_add hY0]
      calc Y ^ ((0.2 : ℝ) + 0.7) ≤ Y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le G.hY1 (by norm_num)
        _ = Y := Real.rpow_one Y
    have hPE : Pm ^ K * Pm ^ (K * (J + 1)) ≤ E := by
      rw [G.hE, ← pow_add]
      exact pow_le_pow_right₀ G.hPm1 (by nlinarith)
    have key : Y ^ (0.2 : ℝ) * Pm ^ (K * (J + 1)) * ε * Y ^ (0.7 : ℝ) ≤ 1 := by
      calc Y ^ (0.2 : ℝ) * Pm ^ (K * (J + 1)) * ε * Y ^ (0.7 : ℝ)
          = (Y ^ (0.2 : ℝ) * Y ^ (0.7 : ℝ)) * Pm ^ (K * (J + 1)) * ε := by ring
        _ ≤ Pm ^ K * Pm ^ (K * (J + 1)) * ε :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hYY.trans hYP)
              (pow_nonneg hPm0 _)) hε0
        _ ≤ E * ε := mul_le_mul_of_nonneg_right hPE hε0
        _ ≤ 1 := hεE1
    have hm : Y ^ (-0.7 : ℝ) = 1 / Y ^ (0.7 : ℝ) := by
      rw [Real.rpow_neg hY0.le, one_div]
    push_cast
    rw [hm, le_div_iff₀ h07]
    calc (l : ℝ) * omitProd ℓ o * ε * Y ^ (0.7 : ℝ)
        ≤ Y ^ (0.2 : ℝ) * Pm ^ (K * (J + 1)) * ε * Y ^ (0.7 : ℝ) := by gcongr
      _ ≤ 1 := key
  · intro I i₀ o o' Z Z' T hZ hZ' hT
    have hZb : ∀ Z ∈ zTuples x a I i₀, ((∏ i, Z i : ℕ) : ℝ) ≤ Pm ^ K := fun Z hZ =>
      G.tuple_prod_le Z fun i => by
        have := Fintype.mem_piFinset.1 hZ i
        split_ifs at this
        · exact Or.inr this
        · exact Or.inl (Finset.mem_singleton.1 this)
    have hTb : ((∏ i, T i : ℕ) : ℝ) ≤ Pm ^ K :=
      G.tuple_prod_le T fun i => by
        have := Fintype.mem_piFinset.1 hT i
        split_ifs at this
        · exact Or.inl (Finset.mem_singleton.1 this)
        · exact Or.inr this
    have hD1 : ((omitProd ℓ o * ∏ i, Z i : ℕ) : ℝ) ≤ Pm ^ (K * (J + 2)) := by
      push_cast
      calc (omitProd ℓ o : ℝ) * ∏ i, (Z i : ℝ) ≤ Pm ^ (K * (J + 1)) * Pm ^ K := by
            have := hZb Z hZ; push_cast at this
            exact mul_le_mul (G.omitProd_le hℓ o) this (prod_nonneg fun i _ => Nat.cast_nonneg _)
              (pow_nonneg hPm0 _)
        _ = Pm ^ (K * (J + 2)) := by rw [← pow_add]; ring_nf
    have hD2 : ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℝ) ≤ Pm ^ (K * (J + 2)) := by
      push_cast
      calc (omitProd ℓ o' : ℝ) * ∏ i, (Z' i : ℝ) ≤ Pm ^ (K * (J + 1)) * Pm ^ K := by
            have := hZb Z' hZ'; push_cast at this
            exact mul_le_mul (G.omitProd_le hℓ o') this (prod_nonneg fun i _ => Nat.cast_nonneg _)
              (pow_nonneg hPm0 _)
        _ = Pm ^ (K * (J + 2)) := by rw [← pow_add]; ring_nf
    have hdiff : |(((omitProd ℓ o * ∏ i, Z i : ℕ) : ℝ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℝ))|
        ≤ Pm ^ (K * (J + 2)) := by
      rw [abs_le]
      constructor <;> linarith [(Nat.cast_nonneg (omitProd ℓ o * ∏ i, Z i) : (0 : ℝ) ≤ _),
        (Nat.cast_nonneg (omitProd ℓ o' * ∏ i, Z' i) : (0 : ℝ) ≤ _)]
    have hN : |(((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
        ((∏ i, T i : ℕ) : ℤ) : ℤ) : ℝ)| ≤ E := by
      push_cast
      rw [abs_mul]
      have hT0 : |((∏ i, T i : ℕ) : ℝ)| ≤ Pm ^ K := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hTb
      push_cast at hdiff hT0
      calc |(omitProd ℓ o : ℝ) * ∏ i, (Z i : ℝ) - (omitProd ℓ o' : ℝ) * ∏ i, (Z' i : ℝ)| *
            |∏ i, (T i : ℝ)| ≤ Pm ^ (K * (J + 2)) * Pm ^ K :=
            mul_le_mul hdiff hT0 (abs_nonneg _) (pow_nonneg hPm0 _)
        _ = E := by rw [G.hE, ← pow_add]; ring_nf
    have hL : log x ^ a i₀ ≤ log x ^ (0.2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le G.hL1 (G.haL i₀)
    calc _ ≤ E * ε := mul_le_mul_of_nonneg_right hN hε0
      _ ≤ exp (-(log x ^ (0.2 : ℝ))) := G.hεE
      _ ≤ exp (-(log x ^ a i₀)) := exp_le_exp.2 (by linarith)
      _ ≤ 100 * exp (-(log x ^ a i₀)) := by linarith [exp_pos (-(log x ^ a i₀))]

open Classical in
/-- **The core count for one list** (the bad side `ℓ`, a set `B` of bad ratios for `ℓ`). -/
lemma Glob.core_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {A₁ A₂ : ℕ} (hA : Nat.Coprime A₁ A₂)
    (hS0 : 0 < A₁ * A₂) (hSq : Squarefree (A₁ * A₂)) (hSE : ((A₁ * A₂ : ℕ) : ℝ) ≤ E)
    (N₀ : ℤ) (hN : |(N₀ : ℝ)| ≤ 5 * E) {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) (hYP : Y ≤ Pm ^ K) (hYl : log x ^ (0.1 : ℝ) - 2 ≤ log Y)
    (B : Set ℝ) (hB : B ⊆ {r | ¬ IsGoodRatio x Y a ℓ r}) :
    ((((posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
        A₁ ∣ PQ.1.1 ∧ A₂ ∣ PQ.2.1 ∧ detPQ PQ.1 PQ.2 = N₀ ∧
        rootRatio PQ.1.1 PQ.1.2 ∈ B).card : ℕ) : ℝ) ≤
      PhiE x U V c ε E η₁ / ((A₁ * A₂ : ℕ) : ℝ) := by
  have hE1 := G.E_ge_one
  have hε := G.hε
  have hε2 : ε ≤ 1 / 2 := by
    have h3 : 1 ≤ E ^ 3 := one_le_pow₀ hE1
    nlinarith [G.hε10]
  have hNε : |(N₀ : ℝ)| * ε ≤ 1 := by
    have h3 : E ≤ E ^ 3 := by nlinarith [one_le_pow₀ hE1 (n := 2)]
    nlinarith [G.hε10]
  have hSx : ((A₁ * A₂ : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ)) := hSE.trans G.hEx
  have hfat : ∀ r ∈ B, 0 ≤ r → r < 1 → ∀ r', |r' - r| ≤ ε →
      r' ∈ {r | ¬ IsGoodRatioW x Y a ℓ r} := fun r hr h0 h1 =>
    G.fat hℓ hYP r (hB hr) h0 h1
  have h := core_count_bound G.hRC G.hx0 G.hU G.hV hA hS0 hSq hSx N₀ hε hε2 hNε
    B {r | ¬ IsGoodRatioW x Y a ℓ r} hfat
  have hvol := G.hGW ℓ (mem_listCands_grp hℓ) hYl
  refine h.trans ?_
  have hS : (0 : ℝ) < ((A₁ * A₂ : ℕ) : ℝ) := by exact_mod_cast hS0
  set S := ((A₁ * A₂ : ℕ) : ℝ)
  have hUV : 0 ≤ U * V := by have := G.hU; have := G.hV; positivity
  have hx : 0 ≤ x ^ (-c) := Real.rpow_nonneg G.hx0.le _
  have hS3 : S ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ hS.le hSE 3
  set Z := U * V * x ^ (-c)
  have hZ : 0 ≤ Z := by positivity
  have h1 : 1000 * (U * V) * (volume ({r | ¬ IsGoodRatioW x Y a ℓ r} ∩ Set.Ioc 0 1)).toReal / S ≤
      1000 * (U * V) * η₁ / S := by gcongr
  have h2 : 19 * S ^ 2 * Z / ε ≤ 19 * E ^ 3 * Z / ε / S := by
    rw [div_div, div_le_div_iff₀ hε (mul_pos hε hS)]
    have h19 : 0 ≤ 19 * Z * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS3 h19]
  calc _ ≤ 1000 * (U * V) * η₁ / S + 19 * E ^ 3 * Z / ε / S := add_le_add h1 h2
    _ = PhiE x U V c ε E η₁ / S := by unfold PhiE; ring

/-! ## Summing the minor kernel over determinant fibres -/

open Classical in
lemma sum_minorKernel_le (G : Glob x a J A₀ Y U V c ε E η₁ Pm)
    (X : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (D a' b : ℕ) (hab : |((b : ℝ) - a')| < 5 * Y) (Φ' : ℝ)
    (hΦ : 0 ≤ Φ') (hcount : ∀ t₀ : ℤ, |(t₀ : ℝ)| ≤ 5 * Y →
      ((X.filter fun PQ => detPQ PQ.1 PQ.2 / (D : ℤ) = t₀).card : ℝ) ≤ Φ') :
    ∑ PQ ∈ X, ‖minorKernel x A₀ Y (detPQ PQ.1 PQ.2 / (D : ℤ)) (a' : ℤ) (b : ℤ)‖ ≤
      (1 + 44 * log x ^ (3 * A₀)) * Φ' := by
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos G.hY1
  set vol := (volume (majorArcs x A₀ Y)).toReal
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  set w : ℤ → ℝ := fun t => (if t - (b : ℤ) + (a' : ℤ) = 0 then 1 else 0) +
    (if |(t : ℝ) / Y| < 5 then 1 else 0) * vol
  have hw0 : ∀ t, 0 ≤ w t := fun t => by simp only [w]; split_ifs <;> positivity
  set T := Finset.Icc (-⌊5 * Y⌋) ⌊5 * Y⌋
  have hmemT : ∀ t : ℤ, |(t : ℝ)| ≤ 5 * Y → t ∈ T := by
    intro t ht
    rw [abs_le] at ht
    refine Finset.mem_Icc.2 ⟨?_, Int.le_floor.2 (by linarith)⟩
    have : -t ≤ ⌊5 * Y⌋ := Int.le_floor.2 (by push_cast; linarith)
    omega
  have hwT : ∀ t, t ∉ T → w t = 0 := by
    intro t ht
    have h1 : ¬ (t - (b : ℤ) + (a' : ℤ) = 0) := by
      intro h
      apply ht
      apply hmemT
      have : (t : ℝ) = b - a' := by
        have : t = (b : ℤ) - a' := by linarith
        rw [this]; push_cast; ring
      rw [this]; exact hab.le
    have h2 : ¬ (|(t : ℝ) / Y| < 5) := by
      intro h
      apply ht
      apply hmemT
      rw [abs_div, abs_of_pos hY0, div_lt_iff₀ hY0] at h
      linarith
    simp only [w, if_neg h1, if_neg h2]; ring
  have hstep1 : ∀ PQ ∈ X, ‖minorKernel x A₀ Y (detPQ PQ.1 PQ.2 / (D : ℤ)) (a' : ℤ) (b : ℤ)‖ ≤
      ∑ t₀ ∈ T, if detPQ PQ.1 PQ.2 / (D : ℤ) = t₀ then w t₀ else 0 := by
    intro PQ _
    set t := detPQ PQ.1 PQ.2 / (D : ℤ)
    have h1 : ‖minorKernel x A₀ Y t (a' : ℤ) (b : ℤ)‖ ≤ w t := norm_minorKernel_le x A₀ Y t a' b
    refine h1.trans (le_of_eq ?_)
    rw [sum_ite_eq]
    by_cases hT : t ∈ T
    · rw [if_pos hT]
    · rw [if_neg hT, hwT t hT]
  have hfib : ∀ t₀ ∈ T, ∑ PQ ∈ X, (if detPQ PQ.1 PQ.2 / (D : ℤ) = t₀ then w t₀ else 0) =
      ((X.filter fun PQ => detPQ PQ.1 PQ.2 / (D : ℤ) = t₀).card : ℝ) * w t₀ := by
    intro t₀ _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hTcard : (T.card : ℝ) ≤ 10 * Y + 1 := by
    rw [Int.card_Icc]
    have h5 : (⌊5 * Y⌋ : ℝ) ≤ 5 * Y := Int.floor_le _
    have h0 : 0 ≤ ⌊5 * Y⌋ := Int.floor_nonneg.2 (by linarith)
    have : ((⌊5 * Y⌋ + 1 - -⌊5 * Y⌋).toNat : ℝ) = 2 * (⌊5 * Y⌋ : ℝ) + 1 := by
      rw [show ⌊5 * Y⌋ + 1 - -⌊5 * Y⌋ = 2 * ⌊5 * Y⌋ + 1 by ring]
      have : 0 ≤ 2 * ⌊5 * Y⌋ + 1 := by omega
      rw [← Int.cast_natCast, Int.toNat_of_nonneg this]; push_cast; ring
    rw [this]; linarith
  have hsumw : ∑ t₀ ∈ T, w t₀ ≤ 1 + 44 * log x ^ (3 * A₀) := by
    have e1 : ∑ t₀ ∈ T, w t₀ = ∑ t₀ ∈ T, (if t₀ = (b : ℤ) - a' then (1 : ℝ) else 0) +
        ∑ t₀ ∈ T, (if |(t₀ : ℝ) / Y| < 5 then 1 else 0) * vol := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun t₀ _ => ?_
      simp only [w]
      congr 1
      by_cases h : t₀ = (b : ℤ) - a'
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [e1, sum_ite_eq']
    have h1 : (if (b : ℤ) - a' ∈ T then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have h2 : ∑ t₀ ∈ T, (if |(t₀ : ℝ) / Y| < 5 then (1 : ℝ) else 0) * vol ≤ T.card * vol := by
      calc _ ≤ ∑ _t₀ ∈ T, vol := sum_le_sum fun t₀ _ => by
              split_ifs <;> simp [hvol0]
        _ = T.card * vol := by rw [sum_const, nsmul_eq_mul]
    have h3 : (T.card : ℝ) * vol ≤ 44 * log x ^ (3 * A₀) := by
      have hL3 : 0 ≤ log x ^ (3 * A₀) := Real.rpow_nonneg (by linarith [G.hL1]) _
      calc (T.card : ℝ) * vol ≤ (10 * Y + 1) * (4 * log x ^ (3 * A₀) / Y) :=
            mul_le_mul hTcard G.hvolM hvol0 (by linarith)
        _ = (40 + 4 / Y) * log x ^ (3 * A₀) := by field_simp; ring
        _ ≤ 44 * log x ^ (3 * A₀) := by
            gcongr
            have : 4 / Y ≤ 4 := by rw [div_le_iff₀ hY0]; linarith [G.hY1]
            linarith
    linarith
  calc ∑ PQ ∈ X, ‖minorKernel x A₀ Y (detPQ PQ.1 PQ.2 / (D : ℤ)) (a' : ℤ) (b : ℤ)‖
      ≤ ∑ PQ ∈ X, ∑ t₀ ∈ T, (if detPQ PQ.1 PQ.2 / (D : ℤ) = t₀ then w t₀ else 0) :=
        sum_le_sum hstep1
    _ = ∑ t₀ ∈ T, ∑ PQ ∈ X, (if detPQ PQ.1 PQ.2 / (D : ℤ) = t₀ then w t₀ else 0) := sum_comm
    _ = ∑ t₀ ∈ T, ((X.filter fun PQ => detPQ PQ.1 PQ.2 / (D : ℤ) = t₀).card : ℝ) * w t₀ :=
        sum_congr rfl hfib
    _ ≤ ∑ t₀ ∈ T, Φ' * w t₀ := by
        refine sum_le_sum fun t₀ ht₀ => mul_le_mul_of_nonneg_right ?_ (hw0 t₀)
        apply hcount
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht₀
        have h5 : (⌊5 * Y⌋ : ℝ) ≤ 5 * Y := Int.floor_le _
        rw [abs_le]
        constructor
        · have : (-⌊5 * Y⌋ : ℝ) ≤ t₀ := by exact_mod_cast h1
          linarith
        · have : (t₀ : ℝ) ≤ ⌊5 * Y⌋ := by exact_mod_cast h2
          linarith
    _ = Φ' * ∑ t₀ ∈ T, w t₀ := by rw [mul_sum]
    _ ≤ Φ' * (1 + 44 * log x ^ (3 * A₀)) := mul_le_mul_of_nonneg_left hsumw hΦ
    _ = (1 + 44 * log x ^ (3 * A₀)) * Φ' := by ring

/-! ## Edge facts -/

lemma pair_inj_of {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hℓ : ℓ ∈ listCands x a J) (hinj : ∀ i, Function.Injective (ℓ i)) :
    Function.Injective fun q : Fin K × Fin (J + 1) => ℓ q.1 q.2 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ heq
  simp only at heq
  by_cases hi : i = i'
  · subst hi; rw [hinj i heq]
  · have h1 := mem_listCands_grp hℓ i j
    have h2 : ℓ i j ∈ primeGroup x (a i') := by rw [heq]; exact mem_listCands_grp hℓ i' j'
    exact absurd h2 (Finset.disjoint_left.1 (hdisj i i' hi) h1)

lemma last_inj_of {ℓ : Fin K → Fin (J + 1) → ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hℓ : ℓ ∈ listCands x a J) : Function.Injective fun k : Fin K => ℓ k (Fin.last J) := by
  intro i i' heq
  by_contra hi
  simp only at heq
  exact Finset.disjoint_left.1 (hdisj i i' hi) (mem_listCands_grp hℓ i _)
    (heq ▸ mem_listCands_grp hℓ i' _)

lemma listProd_eq_prod_pairs (ℓ : Fin K → Fin (J + 1) → ℕ) :
    listProd ℓ = ∏ q : Fin K × Fin (J + 1), ℓ q.1 q.2 := by
  unfold listProd; rw [Fintype.prod_prod_type]

open Classical in
lemma norm_rowA_le {A₀' Y' : ℝ} {d₀ : ℕ} {z z' : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)}
    (hcond : (∀ i (j : Fin J), z'.2 i j.castSucc = z.2 i j.castSucc) ∧
      (∀ i, z'.2 i (Fin.last J) ∉ Set.range (z.2 i)) ∧
      d₀ ≤ padProd z.2 ∧ padProd z.2 < 2 * d₀) :
    ‖rowA x a A₀' Y' J d₀ z z'‖ ≤ (∏ i, (groupReciprocalSum x (a i))⁻¹) *
      ‖minorKernel x A₀' Y' (detPQ z.1 z'.1 / (padProd z.2 : ℤ)) (lastProd z'.2) (lastProd z.2)‖ := by
  unfold rowA
  rw [if_pos hcond, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hV : 0 ≤ ∏ i, (groupReciprocalSum x (a i))⁻¹ :=
    prod_nonneg fun i _ => inv_nonneg.2 (sum_nonneg fun p _ => by positivity)
  have hd : (d₀ : ℝ) / padProd z.2 ≤ 1 := by
    rcases Nat.eq_zero_or_pos (padProd z.2) with h | h
    · rw [h]; simp
    · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast hcond.2.2.1
  have hd0 : 0 ≤ (d₀ : ℝ) / padProd z.2 := by positivity
  have hb1 := abs_dyadicBump_le_one' ((lastProd z.2 : ℝ) / Y')
  have hb2 := abs_dyadicBump_le_one' ((lastProd z'.2 : ℝ) / Y')
  have hq : (1 / 2 : ℝ) ^ (excessOmega x a J z.1.1 + excessOmega x a J z'.1.1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (excessOmega x a J z.1.1 + excessOmega x a J z'.1.1) := by
    positivity
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hV, abs_of_nonneg hd0,
    abs_of_nonneg hq0]
  calc (∏ i, (groupReciprocalSum x (a i))⁻¹) * ((d₀ : ℝ) / padProd z.2) *
        |dyadicBump ((lastProd z.2 : ℝ) / Y')| * |dyadicBump ((lastProd z'.2 : ℝ) / Y')| *
        (1 / 2 : ℝ) ^ (excessOmega x a J z.1.1 + excessOmega x a J z'.1.1)
      ≤ (∏ i, (groupReciprocalSum x (a i))⁻¹) * 1 * 1 * 1 * 1 := by gcongr
    _ = _ := by ring

open Classical in
/-- The term bound: a valid bad pair contributes at most `∏Vᵢ⁻¹ ‖H_𝔪‖`. -/
lemma term_le (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    {A₀' Y' : ℝ} {d₀ : ℕ} {ℓ ℓ' : Fin K → Fin (J + 1) → ℕ} (hℓ : ℓ ∈ listCands x a J)
    (hℓ' : ℓ' ∈ listCands x a J)
    (hcond : (∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc) ∧
      (∀ i, ℓ' i (Fin.last J) ∉ Set.range (ℓ i)) ∧ d₀ ≤ padProd ℓ ∧ padProd ℓ < 2 * d₀)
    (bad : ℝ) (hb01 : bad = 0 ∨ bad = 1) (PQ : (ℕ × ℕ) × (ℕ × ℕ)) :
    (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
        ‖rowA x a A₀' Y' J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * bad else 0) ≤
      (∏ i, (groupReciprocalSum x (a i))⁻¹) *
        (if listProd ℓ ∣ PQ.1.1 ∧ listProd ℓ' ∣ PQ.2.1 ∧ bad = 1 then
          ‖minorKernel x A₀' Y' (detPQ PQ.1 PQ.2 / (padProd ℓ : ℤ)) (lastProd ℓ')
            (lastProd ℓ)‖ else 0) := by
  have hV : 0 ≤ ∏ i, (groupReciprocalSum x (a i))⁻¹ :=
    prod_nonneg fun i _ => inv_nonneg.2 (sum_nonneg fun p _ => by positivity)
  have hR : 0 ≤ (∏ i, (groupReciprocalSum x (a i))⁻¹) *
      (if listProd ℓ ∣ PQ.1.1 ∧ listProd ℓ' ∣ PQ.2.1 ∧ bad = 1 then
        ‖minorKernel x A₀' Y' (detPQ PQ.1 PQ.2 / (padProd ℓ : ℤ)) (lastProd ℓ')
          (lastProd ℓ)‖ else 0) := by
    refine mul_nonneg hV ?_; split_ifs <;> positivity
  by_cases hv : ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ')
  · rw [if_pos hv]
    have d1 : listProd ℓ ∣ PQ.1.1 := listProd_dvd_of hdisj hℓ hv.1.1 hv.1.2
    have d2 : listProd ℓ' ∣ PQ.2.1 := listProd_dvd_of hdisj hℓ' hv.2.1 hv.2.2
    rcases hb01 with h0 | h1
    · calc ‖rowA x a A₀' Y' J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * bad = 0 := by rw [h0, mul_zero]
        _ ≤ _ := hR
    · rw [if_pos ⟨d1, d2, h1⟩, h1, mul_one]
      exact norm_rowA_le (z := (PQ.1, ℓ)) (z' := (PQ.2, ℓ')) hcond
  · rw [if_neg hv]; exact hR

/-- The facts about a live edge (both cutoffs nonzero). -/
lemma Glob.edge_facts (G : Glob x a J A₀ Y U V c ε E η₁ Pm) {ℓ ℓ' : Fin K → Fin (J + 1) → ℕ}
    (hℓ : ℓ ∈ listCands x a J) (hℓ' : ℓ' ∈ listCands x a J)
    (hηb : dyadicBump ((lastProd ℓ : ℝ) / Y) ≠ 0) (hηa : dyadicBump ((lastProd ℓ' : ℝ) / Y) ≠ 0) :
    Y ≤ Pm ^ K ∧ log x ^ (0.1 : ℝ) - 2 ≤ log Y ∧
      |((lastProd ℓ : ℕ) : ℝ) - (lastProd ℓ' : ℕ)| < 5 * Y ∧
      (padProd ℓ : ℝ) * (5 * Y) ≤ 5 * E ∧
      ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ) ≤ E ∧ ((listProd ℓ' * lastProd ℓ : ℕ) : ℝ) ≤ E := by
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos G.hY1
  have hb := dyadicBump_ne_zero hηb
  have ha := dyadicBump_ne_zero hηa
  rw [lt_div_iff₀ hY0, div_lt_iff₀ hY0, one_mul] at hb ha
  have hPm0 : 0 ≤ Pm := by linarith [G.hPm1]
  have hYP : Y ≤ Pm ^ K := hb.1.le.trans (G.lastProd_le hℓ)
  refine ⟨hYP, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := G.hlast ℓ hℓ
    have hb0 : (0 : ℝ) < lastProd ℓ := lt_of_lt_of_le (exp_pos _) h1
    have h2 : log x ^ (0.1 : ℝ) ≤ log (lastProd ℓ : ℝ) := by
      rw [← log_exp (log x ^ (0.1 : ℝ))]; exact log_le_log (exp_pos _) h1
    have h3 : log (lastProd ℓ : ℝ) ≤ log (4 * Y) := log_le_log hb0 hb.2.le
    rw [log_mul (by norm_num) hY0.ne'] at h3
    have h4 : log (4 : ℝ) < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    linarith
  · rw [abs_lt]; constructor <;> linarith
  · have hD := G.padProd_le hℓ
    have : (padProd ℓ : ℝ) * Y ≤ Pm ^ (K * J) * Pm ^ K :=
      mul_le_mul hD hYP hY0.le (pow_nonneg hPm0 _)
    have hE : Pm ^ (K * J) * Pm ^ K ≤ E := by
      rw [G.hE, ← pow_add]; exact pow_le_pow_right₀ G.hPm1 (by nlinarith)
    nlinarith
  · push_cast
    calc (listProd ℓ : ℝ) * lastProd ℓ' ≤ Pm ^ (K * (J + 1)) * Pm ^ K :=
          mul_le_mul (G.listProd_le hℓ) (G.lastProd_le hℓ') (Nat.cast_nonneg _) (pow_nonneg hPm0 _)
      _ ≤ E := by rw [G.hE, ← pow_add]; exact pow_le_pow_right₀ G.hPm1 (by nlinarith)
  · push_cast
    calc (listProd ℓ' : ℝ) * lastProd ℓ ≤ Pm ^ (K * (J + 1)) * Pm ^ K :=
          mul_le_mul (G.listProd_le hℓ') (G.lastProd_le hℓ) (Nat.cast_nonneg _) (pow_nonneg hPm0 _)
      _ ≤ E := by rw [G.hE, ← pow_add]; exact pow_le_pow_right₀ G.hPm1 (by nlinarith)

lemma badA_eq_one {Y : ℝ} {z : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)} (h : badA x Y a z = 1) :
    rootRatio z.1.1 z.1.2 ∈ {r | ¬ IsGoodRatio x Y a z.2 r} := by
  unfold badA at h; split_ifs at h with hg
  · norm_num at h
  · exact hg

lemma badA_zero_or_one (Y : ℝ) (z : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) :
    badA x Y a z = 0 ∨ badA x Y a z = 1 := by
  unfold badA; split_ifs <;> simp

lemma padProd_eq_of {ℓ ℓ' : Fin K → Fin (J + 1) → ℕ}
    (h : ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc) : padProd ℓ' = padProd ℓ := by
  unfold padProd; exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => h i j

lemma detPQ_eq_mul {P Q : ℕ × ℕ} {D : ℕ} (hP : D ∣ P.1) (hQ : D ∣ Q.1) {t₀ : ℤ}
    (ht : detPQ P Q / (D : ℤ) = t₀) : detPQ P Q = D * t₀ := by
  have hdvd : (D : ℤ) ∣ detPQ P Q := by
    unfold detPQ
    exact dvd_sub (dvd_mul_of_dvd_left (by exact_mod_cast hP) _)
      (dvd_mul_of_dvd_right (by exact_mod_cast hQ) _)
  rw [← Int.mul_ediv_cancel' hdvd, ht]

open Classical in
/-- The vanishing of a dead edge. -/
lemma pair_dead {A₀' Y' : ℝ} {d₀ : ℕ} {ℓ ℓ' : Fin K → Fin (J + 1) → ℕ} (bad : ℝ)
    (hdead : ¬ (((∀ i, Function.Injective (ℓ i)) ∧ (∀ i, Function.Injective (ℓ' i))) ∧
      ((∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc) ∧
        (∀ i, ℓ' i (Fin.last J) ∉ Set.range (ℓ i)) ∧ d₀ ≤ padProd ℓ ∧ padProd ℓ < 2 * d₀) ∧
      dyadicBump ((lastProd ℓ : ℝ) / Y') ≠ 0 ∧ dyadicBump ((lastProd ℓ' : ℝ) / Y') ≠ 0))
    (PQ : (ℕ × ℕ) × (ℕ × ℕ)) :
    (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
        ‖rowA x a A₀' Y' J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * bad else 0) = 0 := by
  by_cases hv : ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ')
  · rw [if_pos hv]
    have : rowA x a A₀' Y' J d₀ (PQ.1, ℓ) (PQ.2, ℓ') = 0 := by
      dsimp only [rowA]
      split_ifs with hc
      · have hη : dyadicBump ((lastProd ℓ : ℝ) / Y') = 0 ∨
            dyadicBump ((lastProd ℓ' : ℝ) / Y') = 0 := by
          by_contra h
          push Not at h
          exact hdead ⟨⟨hv.1.1, hv.2.1⟩, hc, h.1, h.2⟩
        rcases hη with h | h <;> simp [h]
      · rfl
    rw [this, norm_zero, zero_mul]
  · rw [if_neg hv]

open Classical in
/-- **One pair of lists, bad source.** -/
lemma Glob.pair_src (G : Glob x a J A₀ Y U V c ε E η₁ Pm) (d₀ : ℕ)
    {ℓ ℓ' : Fin K → Fin (J + 1) → ℕ} (hℓ : ℓ ∈ listCands x a J) (hℓ' : ℓ' ∈ listCands x a J) :
    ∑ PQ ∈ posBox U V ×ˢ posBox U V,
      (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
        ‖rowA x a A₀ Y J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * badA x Y a (PQ.1, ℓ) else 0) ≤
      (∏ i, (groupReciprocalSum x (a i))⁻¹) *
        ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
          (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) *
        ((1 + 44 * log x ^ (3 * A₀)) * PhiE x U V c ε E η₁)) := by
  have hV : 0 ≤ ∏ i, (groupReciprocalSum x (a i))⁻¹ :=
    prod_nonneg fun i _ => inv_nonneg.2 (sum_nonneg fun p _ => by positivity)
  have hL3 : 0 ≤ log x ^ (3 * A₀) := Real.rpow_nonneg (by linarith [G.hL1]) _
  have hΦ := G.phi_nonneg
  have hR0 : 0 ≤ (∏ i, (groupReciprocalSum x (a i))⁻¹) *
        ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
          (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) *
        ((1 + 44 * log x ^ (3 * A₀)) * PhiE x U V c ε E η₁)) := by
    refine mul_nonneg hV (mul_nonneg ?_ (by positivity))
    split_ifs <;> positivity
  by_cases hmain : ((∀ i, Function.Injective (ℓ i)) ∧ (∀ i, Function.Injective (ℓ' i))) ∧
      ((∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc) ∧
        (∀ i, ℓ' i (Fin.last J) ∉ Set.range (ℓ i)) ∧ d₀ ≤ padProd ℓ ∧ padProd ℓ < 2 * d₀) ∧
      dyadicBump ((lastProd ℓ : ℝ) / Y) ≠ 0 ∧ dyadicBump ((lastProd ℓ' : ℝ) / Y) ≠ 0
  swap
  · exact le_trans (le_of_eq (sum_eq_zero fun PQ _ => pair_dead _ hmain PQ)) hR0
  obtain ⟨⟨hinj, hinj'⟩, hcond, hηb, hηa⟩ := hmain
  obtain ⟨hYP, hYl, hab, hDE, hSE, -⟩ := G.edge_facts hℓ hℓ' hηb hηa
  -- the modulus
  have hd : ∀ (q : Fin K × Fin (J + 1)) (k : Fin K), ℓ q.1 q.2 ≠ ℓ' k (Fin.last J) := by
    intro q k h
    by_cases hk : q.1 = k
    · subst hk; exact hcond.2.1 q.1 ⟨q.2, h⟩
    · exact Finset.disjoint_left.1 (G.hdisj q.1 k hk) (mem_listCands_grp hℓ q.1 q.2)
        (h ▸ mem_listCands_grp hℓ' k _)
  obtain ⟨hcop, hsq⟩ := coprime_sqf_of_inj (fun q : Fin K × Fin (J + 1) => ℓ q.1 q.2)
    (fun k => ℓ' k (Fin.last J))
    (fun q => prime_of_mem_primeGroup (mem_listCands_grp hℓ q.1 q.2))
    (fun k => prime_of_mem_primeGroup (mem_listCands_grp hℓ' k _))
    (pair_inj_of G.hdisj hℓ hinj) (last_inj_of G.hdisj hℓ') hd
  rw [← listProd_eq_prod_pairs] at hcop hsq
  have hcop' : Nat.Coprime (listProd ℓ) (lastProd ℓ') := hcop
  have hsq' : Squarefree (listProd ℓ * lastProd ℓ') := hsq
  have hS0 : 0 < listProd ℓ * lastProd ℓ' := Nat.mul_pos (listProd_pos hℓ) (lastProd_pos hℓ')
  have hS : (0 : ℝ) < ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ) := by exact_mod_cast hS0
  -- step 1
  set X := (posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
    listProd ℓ ∣ PQ.1.1 ∧ listProd ℓ' ∣ PQ.2.1 ∧ badA x Y a (PQ.1, ℓ) = 1
  have hstep1 : ∑ PQ ∈ posBox U V ×ˢ posBox U V,
      (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
        ‖rowA x a A₀ Y J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * badA x Y a (PQ.1, ℓ) else 0) ≤
      (∏ i, (groupReciprocalSum x (a i))⁻¹) * ∑ PQ ∈ X,
        ‖minorKernel x A₀ Y (detPQ PQ.1 PQ.2 / (padProd ℓ : ℤ)) (lastProd ℓ') (lastProd ℓ)‖ := by
    rw [sum_filter, mul_sum]
    exact sum_le_sum fun PQ _ =>
      term_le G.hdisj hℓ hℓ' hcond _ (badA_zero_or_one Y (PQ.1, ℓ)) PQ
  -- step 2
  have hcount : ∀ t₀ : ℤ, |(t₀ : ℝ)| ≤ 5 * Y →
      ((X.filter fun PQ => detPQ PQ.1 PQ.2 / (padProd ℓ : ℤ) = t₀).card : ℝ) ≤
        PhiE x U V c ε E η₁ / ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ) := by
    intro t₀ ht₀
    have hN : |(((padProd ℓ : ℤ) * t₀ : ℤ) : ℝ)| ≤ 5 * E := by
      push_cast
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_mul_of_nonneg_left ht₀ (Nat.cast_nonneg _)).trans hDE
    obtain ⟨Bs, hBs⟩ : ∃ Bs : Set ℝ, Bs = {r | ¬ IsGoodRatio x Y a ℓ r} := ⟨_, rfl⟩
    refine le_trans ?_ (G.core_le hcop' hS0 hsq' hSE ((padProd ℓ : ℤ) * t₀) hN hℓ hYP hYl
      Bs hBs.le)
    refine Nat.cast_le.2 (card_le_card fun PQ hPQ => ?_)
    obtain ⟨hX, ht⟩ := mem_filter.1 hPQ
    obtain ⟨hpp, d1, d2, hbad⟩ := mem_filter.1 hX
    have hDP : padProd ℓ ∣ PQ.1.1 := (Dvd.intro _ (listProd_eq_pad_mul_last ℓ).symm).trans d1
    have hDQ : padProd ℓ ∣ PQ.2.1 := by
      rw [← padProd_eq_of hcond.1]
      exact (Dvd.intro _ (listProd_eq_pad_mul_last ℓ').symm).trans d2
    have h3 : lastProd ℓ' ∣ PQ.2.1 :=
      (Dvd.intro_left _ (listProd_eq_pad_mul_last ℓ').symm).trans d2
    have h4 : detPQ PQ.1 PQ.2 = (padProd ℓ : ℤ) * t₀ := detPQ_eq_mul hDP hDQ ht
    have h5 : rootRatio PQ.1.1 PQ.1.2 ∈ Bs := by
      rw [hBs]; have := badA_eq_one hbad; simpa using this
    exact mem_filter.2 ⟨hpp, d1, h3, h4, h5⟩
  have hstep2 := sum_minorKernel_le G X (padProd ℓ) (lastProd ℓ') (lastProd ℓ) hab
    (PhiE x U V c ε E η₁ / ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ)) (by positivity) hcount
  refine hstep1.trans ((mul_le_mul_of_nonneg_left hstep2 hV).trans (le_of_eq ?_))
  rw [if_pos hcond.1]
  push_cast
  ring

open Classical in
/-- **One pair of lists, bad target.** -/
lemma Glob.pair_tgt (G : Glob x a J A₀ Y U V c ε E η₁ Pm) (d₀ : ℕ)
    {ℓ ℓ' : Fin K → Fin (J + 1) → ℕ} (hℓ : ℓ ∈ listCands x a J) (hℓ' : ℓ' ∈ listCands x a J) :
    ∑ PQ ∈ posBox U V ×ˢ posBox U V,
      (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
        ‖rowA x a A₀ Y J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * badA x Y a (PQ.2, ℓ') else 0) ≤
      (∏ i, (groupReciprocalSum x (a i))⁻¹) *
        ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
          (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) *
        ((1 + 44 * log x ^ (3 * A₀)) * PhiE x U V c ε E η₁)) := by
  have hV : 0 ≤ ∏ i, (groupReciprocalSum x (a i))⁻¹ :=
    prod_nonneg fun i _ => inv_nonneg.2 (sum_nonneg fun p _ => by positivity)
  have hL3 : 0 ≤ log x ^ (3 * A₀) := Real.rpow_nonneg (by linarith [G.hL1]) _
  have hΦ := G.phi_nonneg
  have hR0 : 0 ≤ (∏ i, (groupReciprocalSum x (a i))⁻¹) *
        ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
          (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) *
        ((1 + 44 * log x ^ (3 * A₀)) * PhiE x U V c ε E η₁)) := by
    refine mul_nonneg hV (mul_nonneg ?_ (by positivity))
    split_ifs <;> positivity
  by_cases hmain : ((∀ i, Function.Injective (ℓ i)) ∧ (∀ i, Function.Injective (ℓ' i))) ∧
      ((∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc) ∧
        (∀ i, ℓ' i (Fin.last J) ∉ Set.range (ℓ i)) ∧ d₀ ≤ padProd ℓ ∧ padProd ℓ < 2 * d₀) ∧
      dyadicBump ((lastProd ℓ : ℝ) / Y) ≠ 0 ∧ dyadicBump ((lastProd ℓ' : ℝ) / Y) ≠ 0
  swap
  · exact le_trans (le_of_eq (sum_eq_zero fun PQ _ => pair_dead _ hmain PQ)) hR0
  obtain ⟨⟨hinj, hinj'⟩, hcond, hηb, hηa⟩ := hmain
  obtain ⟨hYPb, hYl, hab, hDE, hSE, hSE'⟩ := G.edge_facts hℓ hℓ' hηb hηa
  have hYP : Y ≤ Pm ^ K := by
    have ha := dyadicBump_ne_zero hηa
    have hY0 : 0 < Y := lt_of_lt_of_le one_pos G.hY1
    rw [lt_div_iff₀ hY0, one_mul] at ha
    exact ha.1.le.trans (G.lastProd_le hℓ')
  -- the modulus: entries of `ℓ'` against the last labels of `ℓ`
  have hd : ∀ (q : Fin K × Fin (J + 1)) (k : Fin K), ℓ' q.1 q.2 ≠ ℓ k (Fin.last J) := by
    intro q k h
    by_cases hk : q.1 = k
    · subst hk
      rcases Fin.eq_castSucc_or_eq_last q.2 with ⟨j, hj⟩ | hj
      · rw [hj, hcond.1 q.1 j] at h
        exact Fin.castSucc_ne_last j (hinj q.1 h)
      · rw [hj] at h; exact hcond.2.1 q.1 ⟨Fin.last J, h.symm⟩
    · exact Finset.disjoint_left.1 (G.hdisj q.1 k hk) (mem_listCands_grp hℓ' q.1 q.2)
        (h ▸ mem_listCands_grp hℓ k _)
  obtain ⟨hcop, hsq⟩ := coprime_sqf_of_inj (fun q : Fin K × Fin (J + 1) => ℓ' q.1 q.2)
    (fun k => ℓ k (Fin.last J))
    (fun q => prime_of_mem_primeGroup (mem_listCands_grp hℓ' q.1 q.2))
    (fun k => prime_of_mem_primeGroup (mem_listCands_grp hℓ k _))
    (pair_inj_of G.hdisj hℓ' hinj') (last_inj_of G.hdisj hℓ) hd
  rw [← listProd_eq_prod_pairs] at hcop hsq
  have hcop' : Nat.Coprime (listProd ℓ') (lastProd ℓ) := hcop
  have hsq' : Squarefree (listProd ℓ' * lastProd ℓ) := hsq
  have hS0 : 0 < listProd ℓ' * lastProd ℓ := Nat.mul_pos (listProd_pos hℓ') (lastProd_pos hℓ)
  have hSS : listProd ℓ' * lastProd ℓ = listProd ℓ * lastProd ℓ' := by
    rw [listProd_eq_pad_mul_last ℓ', listProd_eq_pad_mul_last ℓ, padProd_eq_of hcond.1]; ring
  have hS : (0 : ℝ) < ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ) := by rw [← hSS]; exact_mod_cast hS0
  -- step 1
  set X := (posBox U V ×ˢ posBox U V).filter fun PQ : (ℕ × ℕ) × (ℕ × ℕ) =>
    listProd ℓ ∣ PQ.1.1 ∧ listProd ℓ' ∣ PQ.2.1 ∧ badA x Y a (PQ.2, ℓ') = 1
  have hstep1 : ∑ PQ ∈ posBox U V ×ˢ posBox U V,
      (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
        ‖rowA x a A₀ Y J d₀ (PQ.1, ℓ) (PQ.2, ℓ')‖ * badA x Y a (PQ.2, ℓ') else 0) ≤
      (∏ i, (groupReciprocalSum x (a i))⁻¹) * ∑ PQ ∈ X,
        ‖minorKernel x A₀ Y (detPQ PQ.1 PQ.2 / (padProd ℓ : ℤ)) (lastProd ℓ') (lastProd ℓ)‖ := by
    rw [sum_filter, mul_sum]
    exact sum_le_sum fun PQ _ =>
      term_le G.hdisj hℓ hℓ' hcond _ (badA_zero_or_one Y (PQ.2, ℓ')) PQ
  -- step 2: swap `P` and `Q`
  have hcount : ∀ t₀ : ℤ, |(t₀ : ℝ)| ≤ 5 * Y →
      ((X.filter fun PQ => detPQ PQ.1 PQ.2 / (padProd ℓ : ℤ) = t₀).card : ℝ) ≤
        PhiE x U V c ε E η₁ / ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ) := by
    intro t₀ ht₀
    have hN : |((-((padProd ℓ : ℤ) * t₀) : ℤ) : ℝ)| ≤ 5 * E := by
      push_cast
      rw [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_mul_of_nonneg_left ht₀ (Nat.cast_nonneg _)).trans hDE
    obtain ⟨Bs, hBs⟩ : ∃ Bs : Set ℝ, Bs = {r | ¬ IsGoodRatio x Y a ℓ' r} := ⟨_, rfl⟩
    have hc := G.core_le hcop' hS0 hsq' hSE' (-((padProd ℓ : ℤ) * t₀)) hN hℓ' hYP hYl
      Bs hBs.le
    rw [hSS] at hc
    refine le_trans ?_ hc
    refine Nat.cast_le.2 (card_le_card_of_injOn (fun PQ => (PQ.2, PQ.1)) ?_ ?_)
    · intro PQ hPQ
      obtain ⟨hX, ht⟩ := mem_filter.1 (mem_coe.1 hPQ)
      obtain ⟨hpp, d1, d2, hbad⟩ := mem_filter.1 hX
      obtain ⟨hp1, hp2⟩ := mem_product.1 hpp
      have hDP : padProd ℓ ∣ PQ.1.1 := (Dvd.intro _ (listProd_eq_pad_mul_last ℓ).symm).trans d1
      have hDQ : padProd ℓ ∣ PQ.2.1 := by
        rw [← padProd_eq_of hcond.1]
        exact (Dvd.intro _ (listProd_eq_pad_mul_last ℓ').symm).trans d2
      have hdet := detPQ_eq_mul hDP hDQ ht
      have h3 : lastProd ℓ ∣ PQ.1.1 :=
        (Dvd.intro_left _ (listProd_eq_pad_mul_last ℓ).symm).trans d1
      have h4 : detPQ PQ.2 PQ.1 = -((padProd ℓ : ℤ) * t₀) := by
        unfold detPQ at hdet ⊢; linarith
      have h5 : rootRatio PQ.2.1 PQ.2.2 ∈ Bs := by
        rw [hBs]; have := badA_eq_one hbad; simpa using this
      exact mem_coe.2 (mem_filter.2 ⟨mem_product.2 ⟨hp2, hp1⟩, d2, h3, h4, h5⟩)
    · intro PQ _ PQ' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
  have hstep2 := sum_minorKernel_le G X (padProd ℓ) (lastProd ℓ') (lastProd ℓ) hab
    (PhiE x U V c ε E η₁ / ((listProd ℓ * lastProd ℓ' : ℕ) : ℝ)) (by positivity) hcount
  refine hstep1.trans ((mul_le_mul_of_nonneg_left hstep2 hV).trans (le_of_eq ?_))
  rw [if_pos hcond.1]
  push_cast
  ring

end Bounds

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E: D8a, removing goodness ([21] §4.9, (4.56)–(4.57))

`goodness_removal : GoodnessRemovalStmt δ C c₁ c₂` (for `δ > 0`), with constant `c = 1`.
Lemma 3.3 enters through K's `rootResidues` (`L102K_Final`); Lemma 3.2 through the fattened
`goodness_measureW` (`L102E_Fat`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots ArtinPrimitiveRoots.L102D

/-- For large `x` every group is nonempty (Bertrand), so every `Vᵢ > 0`
(D's `eventually_groupReciprocalSum_pos`). -/
lemma eventually_groupReciprocalSum_pos' {K : ℕ} (a : Fin K → ℝ) (hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i, 0 < groupReciprocalSum x (a i) := by
  refine Filter.eventually_all.2 fun i => ?_
  have hy : Filter.Tendsto (fun x : ℝ => log x ^ a i) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (hpos i)).comp tendsto_log_atTop
  filter_upwards [hy.eventually_ge_atTop 2] with x hx
  set y := exp (log x ^ a i)
  have hy3 : 3 ≤ y := by
    have : exp 2 ≤ y := exp_le_exp.2 hx
    linarith [Real.exp_one_gt_d9, Real.add_one_le_exp (1 : ℝ), show exp 2 = exp 1 * exp 1 by
      rw [← exp_add]; norm_num, show (2.7182818283 : ℝ) * 2.7182818283 ≥ 3 by norm_num,
      mul_le_mul (le_of_lt Real.exp_one_gt_d9) (le_of_lt Real.exp_one_gt_d9) (by norm_num)
        (exp_pos 1).le]
  set n := ⌈y⌉₊
  have hn0 : n ≠ 0 := by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have hmem : p ∈ primeGroup x (a i) := by
    unfold primeGroup
    refine mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_)), hp, ?_⟩
    · have h1 : (n : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2
      have h3 : exp (2 * log x ^ a i) = y * y := by rw [← exp_add]; ring_nf
      rw [h3]; nlinarith
    · have : (n : ℝ) < p := by exact_mod_cast hnp
      linarith [Nat.le_ceil y]
  have : 0 < (1 : ℝ) / p := by have := hp.pos; positivity
  exact lt_of_lt_of_le this (single_le_sum (f := fun q : ℕ => (1 : ℝ) / q)
    (fun q _ => by positivity) hmem)

/-! ## Numerics -/

lemma numeric_ev (K : ℕ) (C A₀ A c : ℝ) (hc : 0 < c) (hA₀ : 0 ≤ A₀) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ J : ℕ, (J : ℝ) ≤ L ^ (0.01 : ℝ) →
      2 * (L ^ C * L ^ C) ^ 2 * (1 + 44 * L ^ (3 * A₀)) *
        (1000 * exp (-(L ^ (0.1 : ℝ)) / 4) +
          190 * exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L)) ≤ L ^ (-A) := by
  set p := 4 * C + 3 * A₀ + A
  have hK1 : (0 : ℝ) < 48 * K + 1 := by positivity
  have e1 := eventually_log_le_rpow (a := 0.1) (by norm_num) p (log 180000) (ε := 1 / 4)
    (by norm_num)
  have e2 := eventually_log_le_rpow (a := 1) one_pos p (log 34200) (ε := c / 2) (by positivity)
  have e3 := eventually_rpow_le_rpow (b := 0.21) (c := 1) (by norm_num)
    (ε := c / (2 * (48 * K + 1))) (by positivity)
  filter_upwards [e1, e2, e3, Filter.eventually_ge_atTop 1] with L h1 h2 h3 hL J hJ
  have hL0 : 0 < L := by linarith
  rw [Real.rpow_one] at h2 h3
  -- the powers of `L`
  have hpow : (L ^ C * L ^ C) ^ 2 = L ^ (4 * C) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
  have h3A : 1 ≤ L ^ (3 * A₀) := Real.one_le_rpow hL (by linarith)
  have h44 : 1 + 44 * L ^ (3 * A₀) ≤ 45 * L ^ (3 * A₀) := by linarith
  have h001 : 1 ≤ L ^ (0.01 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have h02 : L ^ (0.2 : ℝ) ≤ L ^ (0.21 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h021 : L ^ (0.01 : ℝ) * L ^ (0.2 : ℝ) = L ^ (0.21 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hQ : (12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) ≤ (48 * K + 1) * L ^ (0.21 : ℝ) := by
    have hJ3 : (J : ℝ) + 3 ≤ 4 * L ^ (0.01 : ℝ) := by linarith
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h0 : 0 ≤ L ^ (0.2 : ℝ) := by positivity
    calc (12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ)
        ≤ (12 * K * (4 * L ^ (0.01 : ℝ)) + 1) * L ^ (0.2 : ℝ) := by gcongr
      _ = 48 * K * (L ^ (0.01 : ℝ) * L ^ (0.2 : ℝ)) + L ^ (0.2 : ℝ) := by ring
      _ ≤ 48 * K * L ^ (0.21 : ℝ) + L ^ (0.21 : ℝ) := by rw [h021]; linarith
      _ = (48 * K + 1) * L ^ (0.21 : ℝ) := by ring
  -- the two exponentials
  have hLp : L ^ (4 * C) * L ^ (3 * A₀) * L ^ A = exp (p * log L) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, Real.rpow_def_of_pos hL0]
    congr 1; simp only [p]; ring
  have t1 : 90 * exp (p * log L) * (1000 * exp (-(L ^ (0.1 : ℝ)) / 4)) ≤ 1 / 2 := by
    have : 90 * exp (p * log L) * (1000 * exp (-(L ^ (0.1 : ℝ)) / 4)) =
        exp (log 90000 + p * log L + -(L ^ (0.1 : ℝ)) / 4) := by
      rw [exp_add, exp_add, exp_log (by norm_num)]; ring
    rw [this]
    have hl : log 90000 + p * log L + -(L ^ (0.1 : ℝ)) / 4 ≤ -log 2 := by
      have : log (180000 : ℝ) = log 90000 + log 2 := by
        rw [← log_mul (by norm_num) (by norm_num)]; norm_num
      linarith
    calc exp (log 90000 + p * log L + -(L ^ (0.1 : ℝ)) / 4) ≤ exp (-log 2) := exp_le_exp.2 hl
      _ = 1 / 2 := by rw [exp_neg, exp_log (by norm_num), one_div]
  have t2 : 90 * exp (p * log L) * (190 * exp ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L)) ≤
      1 / 2 := by
    have : 90 * exp (p * log L) * (190 * exp ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L)) =
        exp (log 17100 + p * log L + ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L)) := by
      rw [exp_add, exp_add, exp_log (by norm_num)]; ring
    rw [this]
    have h3' : (48 * K + 1) * L ^ (0.21 : ℝ) ≤ c / 2 * L := by
      have := mul_le_mul_of_nonneg_left h3 hK1.le
      calc (48 * K + 1) * L ^ (0.21 : ℝ) ≤ (48 * K + 1) * (c / (2 * (48 * K + 1)) * L) := this
        _ = c / 2 * L := by field_simp
    have hl : log 17100 + p * log L + (48 * K + 1) * L ^ (0.21 : ℝ) - c * L ≤ -log 2 := by
      have : log (34200 : ℝ) = log 17100 + log 2 := by
        rw [← log_mul (by norm_num) (by norm_num)]; norm_num
      linarith
    calc exp (log 17100 + p * log L + ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L)) ≤ exp (-log 2) :=
          exp_le_exp.2 (by linarith)
      _ = 1 / 2 := by rw [exp_neg, exp_log (by norm_num), one_div]
  -- assemble
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hneg : L ^ (-A) = 1 / L ^ A := by rw [Real.rpow_neg hL0.le, one_div]
  rw [hneg, le_div_iff₀ hLA, hpow]
  have hE2 : exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L) ≤
      exp ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L) := exp_le_exp.2 (by linarith)
  have hP0 : 0 ≤ L ^ (4 * C) := by positivity
  have hA0' : 0 ≤ L ^ (3 * A₀) := by positivity
  calc 2 * L ^ (4 * C) * (1 + 44 * L ^ (3 * A₀)) *
        (1000 * exp (-(L ^ (0.1 : ℝ)) / 4) +
          190 * exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L)) * L ^ A
      ≤ 2 * L ^ (4 * C) * (45 * L ^ (3 * A₀)) *
        (1000 * exp (-(L ^ (0.1 : ℝ)) / 4) +
          190 * exp ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L)) * L ^ A := by gcongr
    _ = 90 * (L ^ (4 * C) * L ^ (3 * A₀) * L ^ A) * (1000 * exp (-(L ^ (0.1 : ℝ)) / 4)) +
        90 * (L ^ (4 * C) * L ^ (3 * A₀) * L ^ A) *
          (190 * exp ((48 * K + 1) * L ^ (0.21 : ℝ) - c * L)) := by ring
    _ ≤ 1 / 2 + 1 / 2 := by rw [hLp]; exact add_le_add t1 t2
    _ = 1 := by norm_num

/-! ## The endpoint vector -/

lemma norm_endpointVec_le {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ} {α β : ℕ → ℂ}
    {B : ℝ} (hα : ∀ m, ‖α m‖ ≤ B) (hβ : ∀ n, ‖β n‖ ≤ B) (s : PhysState x a J U V) :
    ‖endpointVec x a J U V α β s‖ ≤ B * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hα 0)
  unfold endpointVec
  split_ifs
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hα _) (hβ _) (norm_nonneg _) hB
  · simp; positivity

/-! ## D8a -/

open Classical in
/-- **D8a** ([21] §4.9, (4.56)–(4.57)): removing the goodness projections from the pairing costs
`O(U V L^{-A})` for every `A`; here with constant `1`. -/
theorem goodness_removal (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) : GoodnessRemovalStmt δ C c₁ c₂ := by
  intro A₀ hA₀ K hK a ha hab A hA
  have ha1 : ∀ i, (0.1 : ℝ) < a i := fun i => (hab i).1
  have ha2 : ∀ i, a i ≤ 0.2 := fun i => (hab i).2.le
  have hapos : ∀ i, 0 < a i := fun i => (by norm_num : (0 : ℝ) < 0.1).trans (ha1 i)
  obtain ⟨c, hc, x₁, hx₁⟩ := rootCountAt_of hδ
  obtain ⟨x₂, hx₂⟩ := goodness_measureW a ha ha1
  -- the eventual conditions on `L = log x`
  have hLev : ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧ L ^ (0.01 : ℝ) + 1 ≤ L ∧
      8 * K * L ^ (0.21 : ℝ) ≤ L ^ (0.98 : ℝ) ∧
      ∀ J : ℕ, (J : ℝ) ≤ L ^ (0.01 : ℝ) →
        2 * (L ^ C * L ^ C) ^ 2 * (1 + 44 * L ^ (3 * A₀)) *
          (1000 * exp (-(L ^ (0.1 : ℝ)) / 4) +
            190 * exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L)) ≤ L ^ (-A) := by
    have e1 := eventually_rpow_le_rpow (b := 0.01) (c := 1) (by norm_num) (ε := 1 / 2)
      (by norm_num)
    have e2 := eventually_rpow_le_rpow (b := 0.21) (c := 0.98) (by norm_num)
      (ε := 1 / (8 * K + 1)) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop 2, e1, e2,
      numeric_ev K C A₀ A c hc hA₀.le] with L hL h1 h2 h4
    refine ⟨by linarith, ?_, ?_, h4⟩
    · rw [Real.rpow_one] at h1; linarith
    · have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have h0 : 0 ≤ L ^ (0.21 : ℝ) := by positivity
      have h98 : 0 ≤ L ^ (0.98 : ℝ) := by positivity
      calc 8 * K * L ^ (0.21 : ℝ) ≤ (8 * K + 1) * L ^ (0.21 : ℝ) := by nlinarith
        _ ≤ (8 * K + 1) * (1 / (8 * K + 1) * L ^ (0.98 : ℝ)) := by gcongr
        _ = L ^ (0.98 : ℝ) := by field_simp
  have hev := (Real.tendsto_log_atTop.eventually hLev).and
    ((eventually_disjoint_groups' a ha).and (eventually_groupReciprocalSum_pos' a hapos))
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1 hev
  refine ⟨1, max (max x₁ x₂) (max x₃ 1),
    fun x Hm Hn hx hm hn _ _ α β _ _ hαb hβb Y hY k => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxone : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  obtain ⟨⟨hL1, hJL, hEL, hnum⟩, hdisj, hVpos⟩ := hx₃ x hx3
  set L := log x with hLdef
  set J := padCount x
  have hJ : (J : ℝ) ≤ L ^ (0.01 : ℝ) := Nat.floor_le (by positivity)
  have hJ1 : ((J + 1 : ℕ) : ℝ) ≤ L := by push_cast; linarith
  set U := 2 ^ k * Y * Hm
  set V := Hn
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hHm : 0 < Hm := lt_of_lt_of_le hxδ hm
  have hHn : 0 < Hn := lt_of_lt_of_le hxδ hn
  have h2kY : 1 ≤ 2 ^ k * Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hY
  have hU : 0 < U := by positivity
  have hUx : x ^ δ ≤ U := hm.trans (by
    calc Hm = 1 * Hm := (one_mul _).symm
      _ ≤ 2 ^ k * Y * Hm := by gcongr)
  set Pm := exp (2 * L ^ (0.2 : ℝ))
  set E := Pm ^ (K * (J + 3))
  set ε := exp (-(L ^ (0.2 : ℝ))) / (10 * E ^ 3)
  set η₁ := exp (-(L ^ (0.1 : ℝ)) / 4)
  have hPm1 : 1 ≤ Pm := one_le_exp (by positivity)
  have hE1 : 1 ≤ E := one_le_pow₀ hPm1
  have hE0 : 0 < E := by linarith
  have hY0 : 0 < Y := by linarith
  -- the global facts
  have G : Glob x a J A₀ Y U V c ε E η₁ Pm := by
    refine ⟨hx0, hL1, hU, hHn, hY, hx₁ x hx1 U V hUx hn, hdisj, hPm1, ?_, rfl, by positivity,
      ?_, ?_, ?_, ha2, by positivity, ?_, ?_, ?_, hA₀.le⟩
    · intro i p hp
      refine (le_of_mem_primeGroup' hp).2.trans (exp_le_exp.2 ?_)
      have := Real.rpow_le_rpow_of_exponent_le hL1 (ha2 i)
      linarith
    · have : E * ε = exp (-(L ^ (0.2 : ℝ))) / (10 * E ^ 2) := by
        simp only [ε]; field_simp
      rw [this, div_le_iff₀ (by positivity)]
      have hE2 : 1 ≤ E ^ 2 := one_le_pow₀ hE1
      have : 1 ≤ 10 * E ^ 2 := by linarith only [hE2]
      exact le_mul_of_one_le_right (exp_pos _).le this
    · have : 10 * E ^ 3 * ε = exp (-(L ^ (0.2 : ℝ))) := by simp only [ε]; field_simp
      rw [this, exp_le_one_iff, neg_nonpos]; positivity
    · simp only [E, Pm]
      rw [← exp_nat_mul]
      apply exp_le_exp.2
      have h0 : 0 ≤ L ^ (0.2 : ℝ) := by positivity
      have hJ3 : ((K * (J + 3) : ℕ) : ℝ) ≤ 4 * K * L ^ (0.01 : ℝ) := by
        push_cast
        have h001 : 1 ≤ L ^ (0.01 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        calc (K : ℝ) * ((J : ℝ) + 3) ≤ K * (4 * L ^ (0.01 : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith only [hJ, h001]) hK0
          _ = 4 * K * L ^ (0.01 : ℝ) := by ring
      have h021 : L ^ (0.01 : ℝ) * L ^ (0.2 : ℝ) = L ^ (0.21 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]; norm_num
      calc ((K * (J + 3) : ℕ) : ℝ) * (2 * L ^ (0.2 : ℝ))
          ≤ 4 * K * L ^ (0.01 : ℝ) * (2 * L ^ (0.2 : ℝ)) := by gcongr
        _ = 8 * K * (L ^ (0.01 : ℝ) * L ^ (0.2 : ℝ)) := by ring
        _ = 8 * K * L ^ (0.21 : ℝ) := by rw [h021]
        _ ≤ L ^ (0.98 : ℝ) := hEL
    · intro ℓ hℓ hYl
      have h := hx₂ x hx2 (J + 1) hJ1 Y hY0 hYl ℓ hℓ
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal (exp_pos _).le] at this
    · intro ℓ hℓ
      have hK0 : 0 < K := hK
      set i₀ : Fin K := ⟨0, hK0⟩
      have hge : ∀ i ∈ (univ : Finset (Fin K)), 1 ≤ ℓ i (Fin.last J) := fun i _ =>
        (prime_of_mem_primeGroup (mem_listCands_grp hℓ i _)).one_lt.le
      have h1 : ℓ i₀ (Fin.last J) ≤ lastProd ℓ :=
        Finset.single_le_prod' (f := fun i => ℓ i (Fin.last J)) hge (mem_univ i₀)
      have h2 := (le_of_mem_primeGroup' (mem_listCands_grp hℓ i₀ (Fin.last J))).1
      have h3 : exp (L ^ (0.1 : ℝ)) ≤ exp (L ^ a i₀) :=
        exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (ha1 i₀).le)
      calc exp (L ^ (0.1 : ℝ)) ≤ exp (L ^ a i₀) := h3
        _ ≤ ℓ i₀ (Fin.last J) := h2
        _ ≤ lastProd ℓ := by exact_mod_cast h1
    · have h := volume_majorArcs_le' x A₀ Y hL1 hA₀.le hY0
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- the chain
  have hσ0 : 0 ≤ stateNorm x a J := prod_nonneg fun i _ => by have := hVpos i; positivity
  have hdiff := pairing_STS_sub_le (U := U) (V := V) A₀ Y (2 ^ k) α β hσ0
  set B2 := log x ^ C * log x ^ C
  have hB2 : 0 ≤ B2 := by positivity
  have hf : ∀ s : PhysState x a J U V, ‖endpointVec x a J U V α β s‖ ≤ B2 :=
    norm_endpointVec_le hαb hβb
  set T := rowOp x a A₀ Y J (2 ^ k) U V
  set Ψ₀ := (1 + 44 * log x ^ (3 * A₀)) * PhiE x U V c ε E η₁
  have hΨ0 : 0 ≤ Ψ₀ := by
    have := G.phi_nonneg
    have : 0 ≤ log x ^ (3 * A₀) := by positivity
    positivity
  -- one bad side at a time
  have hside : ∀ side : Bool,
      stateNorm x a J * ∑ t : PhysState x a J U V, ∑ t' : PhysState x a J U V,
        ‖T t t'‖ * (if side then badA x Y a t.1 else badA x Y a t'.1) ≤ Ψ₀ := by
    intro side
    have hF0 : ∀ z z' : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ),
        0 ≤ ‖rowA x a A₀ Y J (2 ^ k) z z'‖ * (if side then badA x Y a z else badA x Y a z') :=
      fun z z' => mul_nonneg (norm_nonneg _) (by split_ifs <;> exact badA_nonneg Y _)
    have hs := sum_states_le (x := x) (a := a) (J := J) (U := U) (V := V)
      (fun z z' => ‖rowA x a A₀ Y J (2 ^ k) z z'‖ *
        (if side then badA x Y a z else badA x Y a z')) hF0
    have hpair : ∀ ℓ ∈ listCands x a J, ∀ ℓ' ∈ listCands x a J,
        ∑ PQ ∈ posBox U V ×ˢ posBox U V,
          (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
            ‖rowA x a A₀ Y J (2 ^ k) (PQ.1, ℓ) (PQ.2, ℓ')‖ *
              (if side then badA x Y a (PQ.1, ℓ) else badA x Y a (PQ.2, ℓ')) else 0) ≤
          (∏ i, (groupReciprocalSum x (a i))⁻¹) *
            ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
              (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) * Ψ₀) := by
      intro ℓ hℓ ℓ' hℓ'
      cases side
      · simpa using G.pair_tgt (2 ^ k) hℓ hℓ'
      · simpa using G.pair_src (2 ^ k) hℓ hℓ'
    have hlist := list_pair_sum_le (x := x) (a := a) (J := J) hVpos
    calc stateNorm x a J * ∑ t : PhysState x a J U V, ∑ t' : PhysState x a J U V,
          ‖T t t'‖ * (if side then badA x Y a t.1 else badA x Y a t'.1)
        ≤ stateNorm x a J * ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
            ∑ PQ ∈ posBox U V ×ˢ posBox U V,
              (if ValidSt (PQ.1, ℓ) ∧ ValidSt (PQ.2, ℓ') then
                ‖rowA x a A₀ Y J (2 ^ k) (PQ.1, ℓ) (PQ.2, ℓ')‖ *
                  (if side then badA x Y a (PQ.1, ℓ) else badA x Y a (PQ.2, ℓ')) else 0) :=
          mul_le_mul_of_nonneg_left hs hσ0
      _ ≤ stateNorm x a J * ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
            (∏ i, (groupReciprocalSum x (a i))⁻¹) *
              ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
                (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) * Ψ₀) := by
          gcongr with ℓ hℓ ℓ' hℓ'
          exact hpair ℓ hℓ ℓ' hℓ'
      _ = Ψ₀ * (stateNorm x a J * ((∏ i, (groupReciprocalSum x (a i))⁻¹) *
            ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
              (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
                (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0))) := by
          have e : ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
              (∏ i, (groupReciprocalSum x (a i))⁻¹) *
                ((if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
                  (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) * Ψ₀) =
              (Ψ₀ * ∏ i, (groupReciprocalSum x (a i))⁻¹) *
                ∑ ℓ ∈ listCands x a J, ∑ ℓ' ∈ listCands x a J,
                  (if ∀ i (j : Fin J), ℓ' i j.castSucc = ℓ i j.castSucc then
                    (1 : ℝ) / ((listProd ℓ : ℝ) * (lastProd ℓ' : ℝ)) else 0) := by
            rw [mul_sum]
            refine sum_congr rfl fun ℓ _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun ℓ' _ => by ring
          rw [e]; ring
      _ ≤ Ψ₀ * 1 := mul_le_mul_of_nonneg_left hlist hΨ0
      _ = Ψ₀ := mul_one _
  have hsrc := hside true
  have htgt := hside false
  simp only [if_true, Bool.false_eq_true, if_false] at hsrc htgt
  -- combine
  have hmain : ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
      B2 * B2 * (2 * Ψ₀) := by
    refine hdiff.trans ?_
    calc stateNorm x a J * ∑ t, ∑ t', ‖T t t'‖ * (‖endpointVec x a J U V α β t‖ *
            ‖endpointVec x a J U V α β t'‖ * (badA x Y a t.1 + badA x Y a t'.1))
        ≤ stateNorm x a J * ∑ t, ∑ t', ‖T t t'‖ * (B2 * B2 * (badA x Y a t.1 + badA x Y a t'.1)) := by
          gcongr with t _ t' _
          · exact add_nonneg (badA_nonneg Y _) (badA_nonneg Y _)
          · exact hf t
          · exact hf t'
      _ = B2 * B2 * (stateNorm x a J * ∑ t, ∑ t', ‖T t t'‖ * badA x Y a t.1 +
            stateNorm x a J * ∑ t, ∑ t', ‖T t t'‖ * badA x Y a t'.1) := by
          have e : ∀ t t' : PhysState x a J U V,
              ‖T t t'‖ * (B2 * B2 * (badA x Y a t.1 + badA x Y a t'.1)) =
                B2 * B2 * (‖T t t'‖ * badA x Y a t.1) + B2 * B2 * (‖T t t'‖ * badA x Y a t'.1) :=
            fun t t' => by ring
          simp only [e, sum_add_distrib, ← mul_sum]
          ring
      _ ≤ B2 * B2 * (Ψ₀ + Ψ₀) := by gcongr
      _ = B2 * B2 * (2 * Ψ₀) := by ring
  refine hmain.trans ?_
  -- numerics
  have hnum' := hnum J hJ
  have hxc : x ^ (-c) = exp (-(c * L)) := by
    rw [Real.rpow_def_of_pos hx0, ← hLdef]; congr 1; ring
  have hEε : 19 * E ^ 3 * (U * V * x ^ (-c)) / ε =
      U * V * (190 * exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L)) := by
    have hE6 : E ^ 6 = exp (12 * K * (J + 3) * L ^ (0.2 : ℝ)) := by
      simp only [E, Pm]
      rw [← pow_mul, ← exp_nat_mul]; push_cast; ring_nf
    simp only [ε]
    rw [hxc]
    have hex : exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L) =
        exp (12 * K * (J + 3) * L ^ (0.2 : ℝ)) * exp (L ^ (0.2 : ℝ)) * exp (-(c * L)) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [hex, ← hE6, exp_neg (L ^ (0.2 : ℝ))]
    have hE0' : E ≠ 0 := hE0.ne'
    have hx0' : exp (L ^ (0.2 : ℝ)) ≠ 0 := (exp_pos _).ne'
    field_simp
    ring
  have hUV : 0 ≤ U * V := by positivity
  have hfin : B2 * B2 * (2 * Ψ₀) = U * V * (2 * (L ^ C * L ^ C) ^ 2 * (1 + 44 * L ^ (3 * A₀)) *
      (1000 * exp (-(L ^ (0.1 : ℝ)) / 4) +
        190 * exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L))) := by
    simp only [Ψ₀, PhiE, B2]
    rw [hEε]
    ring
  rw [hfin]
  calc U * V * (2 * (L ^ C * L ^ C) ^ 2 * (1 + 44 * L ^ (3 * A₀)) *
        (1000 * exp (-(L ^ (0.1 : ℝ)) / 4) +
          190 * exp ((12 * K * (J + 3) + 1) * L ^ (0.2 : ℝ) - c * L)))
      ≤ U * V * L ^ (-A) := mul_le_mul_of_nonneg_left hnum' hUV
    _ = 1 * (2 ^ k * Y * Hm * Hn * log x ^ (-A)) := by simp only [U, V]; ring

end ArtinPrimitiveRoots.L102E
end

section
/-! Check module: `chk_norm_dyadPairingSTS_sub_dyadPairingA_le`, the published statement `norm_dyadPairingSTS_sub_dyadPairingA_le` verbatim, proved from the
development and the cuts `abs_card_specialLinearGroup_box_sub_le`. -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) :
    ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ A : ℝ, 0 < A →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
            ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
              c * (2 ^ k * Y * Hm * Hn * log x ^ (-A)) :=
  L102E.goodness_removal δ C c₁ c₂ hδ
end
