-- Prove2me | Definitions.Def_ProductBrown
-- name    : ProductBrown
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:40.853985+00:00
-- url     : https://prove2.me/theorems/72c3db61-59aa-4577-9e2a-2d2e4c3be3fc
-- statement:
--   This block builds a concrete operator on an infinite product space and defines a claim that its Brown measure is a point mass at zero. First come finite-dimensional polynomial lemmas: if two complex polynomials both have nonzero coefficient at degree K, their product has a nonzero coefficient at some degree n ≤ 2K. This yields a compactness-based uniform bound: for coefficient vectors of length 2K+1 with all entries of norm ≤ D and K-th entry of norm ≥ δ > 0, some low-degree coefficient of the product has norm at least a positive ε depending only on K, D, δ. Next, the block defines a recursive sequence of stage data, indexed by s. A stage state records a cutoff K ≥ 1, G ≥ 1, a dimension count d, B ≥ 0 and a previous L ≥ 1; it starts at K=100, G=1, d=0, B=0, L=1. A stage choice supplies ε > 0, L, Gnext and a block length m ≥ 100 satisfying the polynomial lower bound at threshold 1/(s+1), a decay inequality, a growth bound on m (including m ≥ 2^(s+1), m ≥ 4G, m ≥ K), budget inequalities involving κ_s = 1/(100(s+1)), and a gap condition on the next cutoff ⌈m^(3m/4)⌉. Such choices always exist, one is selected, and it defines the next state and a log-weight C = max(L, K²). The coordinate set consists of pairs (s, j) with j < m_s, and the weight of a coordinate is its stage's C, which is nonnegative. SourceAngles θ requires every angle θ(s,j) to lie between 1/(m_s K_s) and 2/(m_s K_s). For angles θ and weights c, the block defines a floor-and-fractional-part action of integer k on [0,1)-valued sequences, and the cocycle exp(−Σ c_i ⌊x_i + kθ_i⌋). It is positive, measurable, and at most 1 for k = 1 on the unit cube when θ and c are nonnegative. On the product of the infinite unit-interval product measure with counting measure on ℤ, this gives a diagonal multiplication operator of norm at most 1 on L²; composing it with the shift of the integer coordinate (n to n−1), which preserves the measure, gives the source operator. The vacuum is the constant function 1 on the cube at integer coordinate 0, a unit vector, and the vacuum functional is T ↦ ⟨vacuum, T vacuum⟩. The Fuglede–Kadison determinant of T is defined as the infimum over n of exp of the real part of the trace of log(max(e^(−n), |T|)), computed by continuous functional calculus. A measure μ on ℂ is a Brown measure of T if it is a compactly supported probability measure whose exp-log potential, the infimum over n of exp ∫ log(max(e^(−n), |z−w|)) dμ(w), equals the determinant of T − z for every complex z. ProductBrownClaim is a defined proposition, not an established theorem: for every angle sequence satisfying SourceAngles, the Dirac mass at 0 is a Brown measure of the source operator with the vacuum functional and these weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProductBrown.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProductBrown.lean; bytes 16..32738
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.34 name and implicit-function convention, proved using Lean 4.33 Mathlib.
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)]
    {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf

namespace OAI

section
noncomputable section
open Polynomial
namespace FiniteFactor

theorem product_has_low_nonzero_coeff (K : ℕ) (p q : ℂ[X])
    (hp : p.coeff K ≠ 0) (hq : q.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (p * q).coeff n ≠ 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  refine ⟨(p * q).natTrailingDegree, ?_,
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hp0 hq0)⟩
  rw [Polynomial.natTrailingDegree_mul hp0 hq0]
  have ha := Polynomial.natTrailingDegree_le_of_ne_zero hp
  have hb := Polynomial.natTrailingDegree_le_of_ne_zero hq
  omega

abbrev Coefficients (K : ℕ) := Fin (2 * K + 1) → ℂ

noncomputable def coefficientPolynomial {K : ℕ} (a : Coefficients K) : ℂ[X] :=
  ∑ i : Fin (2 * K + 1), Polynomial.monomial i.val (a i)

theorem coefficientPolynomial_coeff {K : ℕ} (a : Coefficients K)
    (i : Fin (2 * K + 1)) : (coefficientPolynomial a).coeff i.val = a i := by
  classical
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

noncomputable def productCoefficient {K : ℕ} (a b : Coefficients K) (n : ℕ) : ℂ :=
  ∑ i : Fin (2 * K + 1), ∑ j : Fin (2 * K + 1),
    if i.val + j.val = n then a i * b j else 0

theorem productCoefficient_eq {K : ℕ} (a b : Coefficients K) (n : ℕ) :
    productCoefficient a b n =
      (coefficientPolynomial a * coefficientPolynomial b).coeff n := by
  classical
  simp only [productCoefficient, coefficientPolynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  exact Finset.sum_comm

theorem continuous_productCoefficient (K n : ℕ) :
    Continuous (fun ab : Coefficients K × Coefficients K =>
      productCoefficient ab.1 ab.2 n) := by
  classical
  unfold productCoefficient
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

noncomputable def lowCoefficients {K : ℕ} (ab : Coefficients K × Coefficients K) :
    Coefficients K := fun n => productCoefficient ab.1 ab.2 n.val

theorem continuous_lowCoefficients (K : ℕ) : Continuous (@lowCoefficients K) :=
  continuous_pi fun n => continuous_productCoefficient K n.val

theorem lowCoefficients_ne_zero {K : ℕ} (ab : Coefficients K × Coefficients K)
    (ha : ab.1 ⟨K, by omega⟩ ≠ 0) (hb : ab.2 ⟨K, by omega⟩ ≠ 0) :
    lowCoefficients ab ≠ 0 := by
  have ha' : (coefficientPolynomial ab.1).coeff K ≠ 0 := by
    simpa using (coefficientPolynomial_coeff ab.1 ⟨K, by omega⟩).trans_ne ha
  have hb' : (coefficientPolynomial ab.2).coeff K ≠ 0 := by
    simpa using (coefficientPolynomial_coeff ab.2 ⟨K, by omega⟩).trans_ne hb
  obtain ⟨n, hn, hne⟩ := product_has_low_nonzero_coeff K _ _ ha' hb'
  intro h
  have hz := congrFun h ⟨n, by omega⟩
  exact hne (by simpa [lowCoefficients, productCoefficient_eq] using hz)

def admissibleCoefficients (K : ℕ) (D δ : ℝ) : Set (Coefficients K) :=
  {a | ∀ i, ‖a i‖ ≤ D} ∩ {a | δ ≤ ‖a ⟨K, by omega⟩‖}

theorem isCompact_admissibleCoefficients (K : ℕ) (D δ : ℝ) :
    IsCompact (admissibleCoefficients K D δ) := by
  have hc : IsCompact {a : Coefficients K | ∀ i, ‖a i‖ ≤ D} := by
    simpa [Set.pi, Metric.mem_closedBall, dist_zero_right] using
      (isCompact_pi_infinite fun _ : Fin (2 * K + 1) =>
        isCompact_closedBall (0 : ℂ) D)
  exact hc.inter_right (isClosed_le continuous_const (continuous_apply (⟨K, by omega⟩ : Fin (2 * K + 1))).norm)

theorem uniform_product_coefficient_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a ⟨K, by omega⟩‖ → δ ≤ ‖b ⟨K, by omega⟩‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖productCoefficient a b n.val‖ := by
  classical
  let S := (admissibleCoefficients K D δ).prod (admissibleCoefficients K D δ)
  have hc : IsCompact S := (isCompact_admissibleCoefficients K D δ).prod
    (isCompact_admissibleCoefficients K D δ)
  by_cases hs : S.Nonempty
  · obtain ⟨ab, hab, hmin⟩ := hc.exists_isMinOn hs
      (continuous_lowCoefficients K).norm.continuousOn
    have hpos : 0 < ‖lowCoefficients ab‖ := by
      apply norm_pos_iff.mpr
      apply lowCoefficients_ne_zero
      · exact norm_pos_iff.mp (hδ.trans_le hab.1.2)
      · exact norm_pos_iff.mp (hδ.trans_le hab.2.2)
    refine ⟨‖lowCoefficients ab‖, hpos, ?_⟩
    intro a b ha hb ha0 hb0
    have hm : ‖lowCoefficients ab‖ ≤ ‖lowCoefficients (a, b)‖ :=
      hmin ⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩
    by_contra hn
    push Not at hn
    have hlt : ‖lowCoefficients (a, b)‖ < ‖lowCoefficients ab‖ :=
      (pi_norm_lt_iff hpos).mpr hn
    exact (not_lt_of_ge hm) hlt
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a b ha hb ha0 hb0
    exact False.elim (hs ⟨(a, b), ⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩⟩)

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace FiniteFactor

def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  simp [unitIntervalMeasure, Real.volume_Ico]

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace FiniteFactor

def sourceKappa (s : ℕ) : ℝ := 1 / (100*((s : ℝ)+1))

end FiniteFactor
end
end

section
noncomputable section
open Filter Finset
open scoped Topology
namespace FiniteFactor

def sourceNextCutoff (m : ℕ) : ℕ := Nat.ceil ((m : ℝ)^((3/4 : ℝ)*(m : ℝ)))

theorem sourceNextCutoff_large (m : ℕ) (hm : 100 ≤ m) : 2*m < sourceNextCutoff m := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ)^2 ≤ (m : ℝ)^((3/4 : ℝ)*(m : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hh := hp.trans (Nat.le_ceil _)
  have hh2 : (2 : ℝ)*m < (sourceNextCutoff m : ℝ) := by
    change (m : ℝ)^2 ≤ (sourceNextCutoff m : ℝ) at hh
    nlinarith
  exact_mod_cast hh2

theorem exists_source_block_length (R κ L G : ℝ) (hκ : 0 < κ) (hG : 0 < G) :
    ∃ m : ℕ, R ≤ (m : ℝ) ∧ 100 ≤ m ∧ κ*(m : ℝ)^(1/40 : ℝ) ≥ L ∧
      G*(sourceNextCutoff m : ℝ) < (m : ℝ)^((4/5 : ℝ)*(m : ℝ)) := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ)^(1/40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨m, hmR, hm100, hmG, hmκ⟩ :=
    ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)).and
      ((eventually_ge_atTop (100 : ℕ)).and
        ((tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2*G))).and
          (ht.eventually (eventually_ge_atTop (L/κ)))))).exists
  refine ⟨m, hmR, hm100, (div_le_iff₀ hκ).mp hmκ |>.trans_eq (mul_comm _ _), ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  let A : ℝ := (m : ℝ)^((3/4 : ℝ)*(m : ℝ))
  have hApos : 0 < A := Real.rpow_pos_of_pos hm0 _
  have hA1 : 1 ≤ A := Real.one_le_rpow hm1 (by positivity)
  have hceil : (sourceNextCutoff m : ℝ) ≤ 2*A := by
    have hh := Nat.ceil_lt_add_one hApos.le
    change (Nat.ceil A : ℝ) ≤ 2*A
    linarith
  calc
    G*(sourceNextCutoff m : ℝ) ≤ G*(2*A) := mul_le_mul_of_nonneg_left hceil hG.le
    _ < (m : ℝ)*A := by nlinarith
    _ = (m : ℝ)^((3/4 : ℝ)*(m : ℝ)+1) := by rw [Real.rpow_add hm0, Real.rpow_one]; ring
    _ ≤ (m : ℝ)^((4/5 : ℝ)*(m : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by
        have hh : (100 : ℝ) ≤ m := by exact_mod_cast hm100
        linarith)

structure SourceStageState where
  K : ℕ
  G : ℝ
  d : ℕ
  B : ℝ
  previousL : ℝ
  K_ge : 1 ≤ K
  G_ge : 1 ≤ G
  B_nonneg : 0 ≤ B
  previousL_ge : 1 ≤ previousL

def SourceStageState.D (a : SourceStageState) : ℝ := Real.exp (((a.K : ℝ)+1)*a.B)

structure SourceStageChoice (s : ℕ) (a : SourceStageState) where
  ε : ℝ
  L : ℝ
  Gnext : ℝ
  m : ℕ
  ε_pos : 0 < ε
  polynomial : ∀ u v : Coefficients a.K,
    (∀ i, ‖u i‖ ≤ a.D) → (∀ i, ‖v i‖ ≤ a.D) →
    1/((s : ℝ)+1) ≤ ‖u ⟨a.K, by omega⟩‖ → 1/((s : ℝ)+1) ≤ ‖v ⟨a.K, by omega⟩‖ →
    ∃ n : Fin (2*a.K+1), ε ≤ ‖productCoefficient u v n.val‖
  L_ge : a.previousL ≤ L
  decay : ((2*a.K : ℕ)+1 : ℝ)*3*Real.exp (-L/10000) ≤ ε/((s : ℝ)+1)
  Gnext_ge : 1 ≤ Gnext
  next_budget : sourceKappa (s+1) * Real.sqrt Gnext ≥ L
  m_ge_K : a.K ≤ m
  m_ge_pow : 2^(s+1) ≤ m
  m_ge_G : 4*a.G ≤ (m : ℝ)
  m_ge_100 : 100 ≤ m
  previous_size : (a.d : ℝ) ≤ (m : ℝ)/100
  current_budget : sourceKappa s * (m : ℝ)^(1/40 : ℝ) ≥ L
  next_gap : Gnext*(sourceNextCutoff m : ℝ) < (m : ℝ)^((4/5 : ℝ)*(m : ℝ))

theorem exists_sourceStageChoice (s : ℕ) (a : SourceStageState) :
    Nonempty (SourceStageChoice s a) := by
  have hs : 0 < (s : ℝ)+1 := by positivity
  have hk (j : ℕ) : 0 < sourceKappa j := by unfold sourceKappa; positivity
  obtain ⟨ε, hε, hp⟩ := uniform_product_coefficient_bound a.K a.D (1/((s : ℝ)+1)) (by positivity)
  let target : ℝ := (ε/((s : ℝ)+1))/(((2*a.K : ℕ)+1 : ℝ)*3)
  have ht : 0 < target := by dsimp [target]; positivity
  obtain ⟨t, htL, htt⟩ := ((eventually_ge_atTop (a.previousL/10000)).and
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds ht))).exists
  let L : ℝ := 10000*t
  have hL : a.previousL ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith [a.previousL_ge]) hL
  let G : ℝ := (1+L/sourceKappa (s+1))^2
  have hG : 1 ≤ G := by dsimp [G]; nlinarith [div_pos hLpos (hk (s+1))]
  have hbudget : L ≤ sourceKappa (s+1)*Real.sqrt G := by
    rw [show Real.sqrt G = 1+L/sourceKappa (s+1) by
      dsimp [G]; rw [Real.sqrt_sq (by linarith [div_pos hLpos (hk (s+1))])]]
    rw [mul_add, mul_one, mul_div_cancel₀ _ (hk (s+1)).ne']
    linarith [hk (s+1)]
  let R : ℝ := max (a.K : ℝ) (max ((2^(s+1) : ℕ) : ℝ) (max (4*a.G) (100*(a.d : ℝ))))
  obtain ⟨m, hmR, hm100, hmκ, hmgap⟩ := exists_source_block_length R (sourceKappa s) L G (hk s) (by linarith)
  have hmK : (a.K : ℝ) ≤ m := (le_max_left _ _).trans hmR
  have hm2 : (((2^(s+1) : ℕ)) : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hmR)
  have hmG : 4*a.G ≤ (m : ℝ) := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hmR))
  have hmd : 100*(a.d : ℝ) ≤ m := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hmR))
  refine ⟨⟨ε, L, G, m, hε, hp, hL, ?_, hG, hbudget,
    by exact_mod_cast hmK, by exact_mod_cast hm2, hmG, hm100, by linarith, hmκ, hmgap⟩⟩
  have hden : 0 < (((2*a.K : ℕ)+1 : ℝ)*3) := by positivity
  have htt' := (lt_div_iff₀ hden).mp htt
  have he : -L/10000 = -t := by dsimp [L]; ring
  rw [he]
  nlinarith

def selectedSourceStage (s : ℕ) (a : SourceStageState) : SourceStageChoice s a :=
  Classical.choice (exists_sourceStageChoice s a)

def SourceStageChoice.C {s : ℕ} {a : SourceStageState} (b : SourceStageChoice s a) : ℝ :=
  max b.L ((a.K : ℝ)^2)

def SourceStageChoice.next {s : ℕ} {a : SourceStageState} (b : SourceStageChoice s a) : SourceStageState where
  K := sourceNextCutoff b.m
  G := b.Gnext
  d := a.d+b.m
  B := a.B+b.C*(b.m : ℝ)
  previousL := b.L
  K_ge := by have := sourceNextCutoff_large b.m b.m_ge_100; omega
  G_ge := b.Gnext_ge
  B_nonneg := add_nonneg a.B_nonneg (mul_nonneg (le_max_of_le_right (sq_nonneg _)) (Nat.cast_nonneg _))
  previousL_ge := a.previousL_ge.trans b.L_ge

def sourceStageState : ℕ → SourceStageState
  | 0 => ⟨100, 1, 0, 0, 1, by norm_num, le_rfl, le_rfl, le_rfl⟩
  | s+1 => (selectedSourceStage s (sourceStageState s)).next

def sourceStage (s : ℕ) : SourceStageChoice s (sourceStageState s) :=
  selectedSourceStage s (sourceStageState s)

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FiniteFactor

def coordinateFloor {ι : Type*} (θ : ι → ℝ) (k : ℤ) (x : ι → ℝ) (i : ι) : ℤ :=
  Int.floor (x i + (k : ℝ)*θ i)

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FiniteFactor

def coordinateRotate {ι : Type*} (θ : ι → ℝ) (k : ℤ) (x : ι → ℝ) (i : ι) : ℝ :=
  Int.fract (x i + (k : ℝ)*θ i)

def sourceLog {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) : ℝ :=
  ∑' i, c i * (coordinateFloor θ k x i : ℝ)

def sourceCocycle {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) : ℝ :=
  Real.exp (-sourceLog θ c k x)

theorem sourceCocycle_pos {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) :
    0 < sourceCocycle θ c k x := Real.exp_pos _

theorem sourceCocycle_measurable {ι : Type*} [Countable ι]
    (θ c : ι → ℝ) (k : ℤ) :
    @Measurable (ι → ℝ) ℝ
      (@MeasurableSpace.pi ι (fun _ => ℝ) (fun _ => Real.measurableSpace))
      Real.measurableSpace (sourceCocycle θ c k) := by
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hm0 : Measurable (fun x : ι → ℝ => x i + (k : ℝ)*θ i) :=
    (measurable_pi_apply i).add measurable_const
  have hm := Int.measurable_floor.comp hm0
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hm)

theorem sourceWeight_le_one {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) : sourceCocycle θ c 1 x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  unfold coordinateFloor
  exact_mod_cast Int.floor_nonneg.mpr (show 0 ≤ x i + (1 : ℤ)*θ i by simpa using add_nonneg (hx i).1 (hθ i))

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FiniteFactor

abbrev sourceMeasure (ι : Type*) : Measure ((ι → ℝ) × ℤ) :=
  (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)).prod Measure.count

abbrev SourceHilbert (ι : Type*) : Type _ := Lp ℂ 2 (sourceMeasure ι)

def sourceDiagonal {ι : Type*} (θ c : ι → ℝ) (z : (ι → ℝ) × ℤ) : ℂ :=
  sourceCocycle θ c 1 (coordinateRotate θ z.2 z.1)

theorem sourceDiagonal_measurable {ι : Type*} [Countable ι] (θ c : ι → ℝ) :
    Measurable (sourceDiagonal θ c) := by
  apply Complex.measurable_ofReal.comp
  apply (sourceCocycle_measurable θ c 1).comp
  apply Measurable.of_eval
  intro i
  unfold coordinateRotate
  fun_prop

theorem sourceDiagonal_norm_le {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (z : (ι → ℝ) × ℤ) :
    ‖sourceDiagonal θ c z‖ ≤ 1 := by
  rw [sourceDiagonal, Complex.norm_real, Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
  apply sourceWeight_le_one θ c hθ hc
  intro i
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem sourceDiagonal_memLp {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    MemLp (sourceDiagonal θ c) ∞ (sourceMeasure ι) :=
  memLp_top_of_bound (sourceDiagonal_measurable θ c).aestronglyMeasurable 1
    (Eventually.of_forall (sourceDiagonal_norm_le θ c hθ hc))

def sourceMultiplication {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (sourceMeasure ι) ∞ 2 2
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c))

def sourceShiftIndex {ι : Type*} (z : (ι → ℝ) × ℤ) : (ι → ℝ) × ℤ := (z.1, z.2-1)

theorem sourceShiftIndex_preserving (ι : Type*) :
    MeasurePreserving (sourceShiftIndex (ι := ι)) (sourceMeasure ι) (sourceMeasure ι) := by
  have hm : Measurable (fun k : ℤ => k-1) := measurable_of_countable _
  have hi : Function.Injective (fun k : ℤ => k-1) := by intro a b h; dsimp at h; omega
  have hs : Function.Surjective (fun k : ℤ => k-1) := by intro k; exact ⟨k+1, by dsimp; omega⟩
  have hp : MeasurePreserving (fun k : ℤ => k-1) Measure.count Measure.count := by
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← hi.encard_image, Set.image_preimage_eq S hs]
  exact (MeasurePreserving.id _).prod hp

def sourceShift (ι : Type*) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (Lp.compMeasurePreservingₗᵢ ℂ sourceShiftIndex (sourceShiftIndex_preserving ι)).toContinuousLinearMap

def sourceOperator {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (sourceShift ι).comp (sourceMultiplication θ c hθ hc)

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter Finset
open scoped Topology ENNReal
namespace FiniteFactor
namespace CouplingParameters

abbrev BlockCoordinate (m : ℕ → ℕ) := Σ s : ℕ, Fin (m s)

end CouplingParameters
end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter Finset
open scoped Topology ENNReal
namespace FiniteFactor

def sourceBlockSize (s : ℕ) : ℕ := (sourceStage s).m
abbrev SourceCoordinate := CouplingParameters.BlockCoordinate sourceBlockSize

def sourceLogWeight (i : SourceCoordinate) : ℝ := (sourceStage i.1).C

def SourceAngles (θ : SourceCoordinate → ℝ) : Prop :=
  let realGroup : GroupWithZero ℝ :=
    (@DivisionRing.toDivisionSemiring ℝ Real.instField.toDivisionRing).toGroupWithZero
  let realOrder : LE ℝ := @Preorder.toLE ℝ Real.partialOrder.toPreorder
  ∀ i : SourceCoordinate,
    let block : ℝ := @Nat.cast ℝ Real.instNatCast (sourceBlockSize i.1)
    let cutoff : ℝ := @Nat.cast ℝ Real.instNatCast (sourceStageState i.1).K
    let denominator : ℝ := @Mul.mul ℝ Real.instMul block cutoff
    let lower : ℝ :=
      @Div.div ℝ realGroup.toDiv (@One.one ℝ Real.instOne) denominator
    let upper : ℝ :=
      @Div.div ℝ realGroup.toDiv (@Nat.cast ℝ Real.instNatCast 2) denominator
    @LE.le ℝ realOrder lower (θ i) ∧ @LE.le ℝ realOrder (θ i) upper

theorem sourceBlockSize_pos (s : ℕ) : (0 : ℝ) < sourceBlockSize s := by
  exact_mod_cast (show 0 < (sourceStage s).m by have := (sourceStage s).m_ge_100; omega)

theorem sourceCutoff_pos (s : ℕ) : (0 : ℝ) < (sourceStageState s).K := by
  exact_mod_cast (show 0 < (sourceStageState s).K by have := (sourceStageState s).K_ge; omega)

theorem SourceAngles.nonneg {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (i : SourceCoordinate) :
    @LE.le ℝ (@Preorder.toLE ℝ Real.partialOrder.toPreorder)
      (@Zero.zero ℝ Real.instZero) (θ i) :=
  let realGroup : GroupWithZero ℝ :=
    (@DivisionRing.toDivisionSemiring ℝ Real.instField.toDivisionRing).toGroupWithZero
  let realOrder : Preorder ℝ := Real.partialOrder.toPreorder
  let realStrict : @PosMulStrictMono ℝ Real.instMul Real.instZero realOrder :=
    @IsStrictOrderedRing.toPosMulStrictMono ℝ Real.semiring Real.partialOrder
      Real.instIsStrictOrderedRing
  let realReflect : @PosMulReflectLT ℝ Real.instMul Real.instZero realOrder :=
    @PosMulMono.toPosMulReflectLT ℝ Real.instMul Real.instZero Real.linearOrder
      (@IsOrderedRing.toPosMulMono ℝ Real.semiring Real.partialOrder
        Real.instIsOrderedRing)
  let block : ℝ := @Nat.cast ℝ Real.instNatCast (sourceBlockSize i.1)
  let cutoff : ℝ := @Nat.cast ℝ Real.instNatCast (sourceStageState i.1).K
  let denominator : ℝ := @Mul.mul ℝ Real.instMul block cutoff
  let lower : ℝ :=
    @Div.div ℝ realGroup.toDiv (@One.one ℝ Real.instOne) denominator
  let upper : ℝ :=
    @Div.div ℝ realGroup.toDiv (@Nat.cast ℝ Real.instNatCast 2) denominator
  let zeroReal : ℝ := @Zero.zero ℝ Real.instZero
  @le_trans ℝ realOrder zeroReal lower (θ i)
    (@le_of_lt ℝ realOrder zeroReal lower
      ((@one_div_pos ℝ realGroup Real.partialOrder realReflect denominator).mpr
        (@mul_pos ℝ realGroup.toMulZeroClass (a := block) (b := cutoff)
          realOrder realStrict (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))))
    (@And.left
      (@LE.le ℝ realOrder.toLE lower (θ i))
      (@LE.le ℝ realOrder.toLE (θ i) upper)
      (hθ i))

theorem sourceLogWeight_nonneg (i : SourceCoordinate) : 0 ≤ sourceLogWeight i :=
  le_max_of_le_right (sq_nonneg _)

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FiniteFactor

def sourceVacuum : SourceHilbert SourceCoordinate :=
  @indicatorConstLp ((SourceCoordinate → ℝ) × ℤ) ℂ
    (@Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
      (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
        (fun _ => Real.measurableSpace)) Int.instMeasurableSpace)
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    (Set.univ ×ˢ {(0 : ℤ)})
    (@Nat.cast ENNReal
      (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
      (Nat.succ (Nat.succ Nat.zero)))
    (MeasurableSet.univ.prod (measurableSet_singleton (0 : ℤ)))
    (letI : IsProbabilityMeasure unitIntervalMeasure :=
       ⟨(Measure.restrict_apply_univ
           (μ := (volume : Measure ℝ)) (Set.Ico (0 : ℝ) 1)).trans
         ((Real.volume_Ico (a := 0) (b := 1)).trans
           ((congrArg ENNReal.ofReal (sub_zero (1 : ℝ))).trans
             ENNReal.ofReal_one))⟩
     let base : Measure (SourceCoordinate → ℝ) :=
       Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)
     let mass_one :=
       (Measure.prod_prod (μ := base) (ν := (Measure.count : Measure ℤ))
         Set.univ {(0 : ℤ)}).trans
         ((congrArg₂ (fun left right : ℝ≥0∞ => left * right)
           (measure_univ (μ := base))
           (Measure.count_singleton (0 : ℤ))).trans (one_mul (1 : ℝ≥0∞)))
     fun mass_top => ENNReal.one_ne_top (mass_one.symm.trans mass_top)) (1 : ℂ)

theorem sourceVacuum_norm : ‖sourceVacuum‖ = 1 := by
  rw [sourceVacuum,norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def,sourceMeasure,Measure.prod_prod]

section

local notation "vacuumMeasurable" =>
  @Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
    (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
      (fun _ => Real.measurableSpace)) Int.instMeasurableSpace
local notation "vacuumSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring
local notation "vacuumIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ vacuumSemiring)
local notation "vacuumHilbertGroup" =>
  @MeasureTheory.Lp.instNormedAddCommGroup
    ((SourceCoordinate → ℝ) × ℤ) ℂ vacuumMeasurable
    (@Nat.cast ENNReal
      (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
      (Nat.succ (Nat.succ Nat.zero)))
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    fact_one_le_two_ennreal
local notation "vacuumHilbertInner" =>
  @MeasureTheory.L2.innerProductSpace
    ((SourceCoordinate → ℝ) × ℤ) ℂ ℂ Complex.instRCLike
    vacuumMeasurable (sourceMeasure SourceCoordinate)
    Complex.instNormedAddCommGroup (@RCLike.innerProductSpace ℂ Complex.instRCLike)
local notation "vacuumHilbertTopology" =>
  @UniformSpace.toTopologicalSpace (SourceHilbert SourceCoordinate)
    (@PseudoMetricSpace.toUniformSpace (SourceHilbert SourceCoordinate)
      (@MetricSpace.toPseudoMetricSpace (SourceHilbert SourceCoordinate)
        (@NormedAddCommGroup.toMetricSpace (SourceHilbert SourceCoordinate) vacuumHilbertGroup)))
local notation "vacuumHilbertAddition" =>
  @AddCommGroup.toAddCommMonoid (SourceHilbert SourceCoordinate)
    (@NormedAddCommGroup.toAddCommGroup (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
local notation "vacuumHilbertModule" =>
  @NormedSpace.toModule ℂ (SourceHilbert SourceCoordinate)
    (@DenselyNormedField.toNormedField ℂ
      (@RCLike.toDenselyNormedField ℂ Complex.instRCLike))
    (@NormedAddCommGroup.toSeminormedAddCommGroup
      (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
    (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
      vacuumHilbertInner)

abbrev sourceVacuumFunctional
    (operator : @ContinuousLinearMap ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
      (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
      (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
      vacuumHilbertModule vacuumHilbertModule) : ℂ :=
  @inner ℂ (SourceHilbert SourceCoordinate)
    (@InnerProductSpace.toInner ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
      vacuumHilbertInner) sourceVacuum
    (@AddHom.toFun (SourceHilbert SourceCoordinate) (SourceHilbert SourceCoordinate)
      (vacuumHilbertAddition).toAdd (vacuumHilbertAddition).toAdd
      (@LinearMap.toAddHom ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
        (SourceHilbert SourceCoordinate) (SourceHilbert SourceCoordinate)
        vacuumHilbertAddition vacuumHilbertAddition vacuumHilbertModule vacuumHilbertModule
        (@ContinuousLinearMap.toLinearMap ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
          (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
          (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
          vacuumHilbertModule vacuumHilbertModule operator)) sourceVacuum)

end

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal CStarAlgebra
namespace FiniteFactor

local instance : IsometricContinuousFunctionalCalculus ℝ
    (SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
instance productHilbertNontrivial : Nontrivial (SourceHilbert SourceCoordinate) := by
  have hv : sourceVacuum≠0 := by
    intro hz
    have h := sourceVacuum_norm
    rw [hz,norm_zero] at h
    norm_num at h
  exact ⟨⟨sourceVacuum,0,hv⟩⟩

end FiniteFactor
end
end

section
noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace FiniteFactor

local notation "productMeasurable" =>
  @Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
    (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
      (fun _ => Real.measurableSpace)) Int.instMeasurableSpace
local notation "productSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring
local notation "productIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ productSemiring)
local notation "productExponent" =>
  @Nat.cast ENNReal
    (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
    (Nat.succ (Nat.succ Nat.zero))
local notation "productHilbertGroup" =>
  @MeasureTheory.Lp.instNormedAddCommGroup
    ((SourceCoordinate → ℝ) × ℤ) ℂ productMeasurable
    productExponent
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    fact_one_le_two_ennreal
local notation "productHilbertInner" =>
  @MeasureTheory.L2.innerProductSpace
    ((SourceCoordinate → ℝ) × ℤ) ℂ ℂ Complex.instRCLike
    productMeasurable (sourceMeasure SourceCoordinate)
    Complex.instNormedAddCommGroup (@RCLike.innerProductSpace ℂ Complex.instRCLike)
local notation "productHilbertTopology" =>
  @UniformSpace.toTopologicalSpace (SourceHilbert SourceCoordinate)
    (@PseudoMetricSpace.toUniformSpace (SourceHilbert SourceCoordinate)
      (@MetricSpace.toPseudoMetricSpace (SourceHilbert SourceCoordinate)
        (@NormedAddCommGroup.toMetricSpace (SourceHilbert SourceCoordinate) productHilbertGroup)))
local notation "productHilbertAddition" =>
  @AddCommGroup.toAddCommMonoid (SourceHilbert SourceCoordinate)
    (@NormedAddCommGroup.toAddCommGroup (SourceHilbert SourceCoordinate) productHilbertGroup)
local notation "productHilbertModule" =>
  @NormedSpace.toModule ℂ (SourceHilbert SourceCoordinate)
    (@DenselyNormedField.toNormedField ℂ
      (@RCLike.toDenselyNormedField ℂ Complex.instRCLike))
    (@NormedAddCommGroup.toSeminormedAddCommGroup
      (SourceHilbert SourceCoordinate) productHilbertGroup)
    (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) productHilbertGroup)
      productHilbertInner)

abbrev ProductOp :=
  @ContinuousLinearMap ℂ ℂ productSemiring productSemiring productIdentity
    (SourceHilbert SourceCoordinate) productHilbertTopology productHilbertAddition
    (SourceHilbert SourceCoordinate) productHilbertTopology productHilbertAddition
    productHilbertModule productHilbertModule

section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal

local instance : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

def logarithmCutoff (n : ℕ) : C(ℝ,ℝ) where
  toFun t := Real.log (max (Real.exp (-(n:ℝ))) t)
  continuous_toFun := (continuous_const.max continuous_id).log
    (fun _=>ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))


def FugledeKadisonDeterminant (τ : ProductOp → ℂ) (T : ProductOp) : ℝ≥0∞ :=
  let determinant := fun (Hilbert : Type) [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℂ Hilbert] [CompleteSpace Hilbert] [Nontrivial Hilbert]
    (trace : (Hilbert →L[ℂ] Hilbert) → ℂ) (operator : Hilbert →L[ℂ] Hilbert) =>
      letI : Module ℝ (Hilbert →L[ℂ] Hilbert) := Module.complexToReal _
      letI : IsometricContinuousFunctionalCalculus ℝ (Hilbert →L[ℂ] Hilbert)
          IsSelfAdjoint := IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
      ⨅ n : ℕ, ENNReal.ofReal
        (Real.exp ((trace (cfc (logarithmCutoff n) (CFC.abs operator))).re))
  let domain := (SourceCoordinate → ℝ) × ℤ
  let measurable : MeasurableSpace domain := productMeasurable
  let exponent : ℝ≥0∞ := productExponent
  let measure : @Measure domain measurable := sourceMeasure SourceCoordinate
  let complete := @MeasureTheory.Lp.instCompleteSpace domain measurable exponent measure ℂ
    Complex.instNormedAddCommGroup Complex.instCompleteSpace fact_one_le_two_ennreal
  @determinant (SourceHilbert SourceCoordinate) productHilbertGroup productHilbertInner
    complete productHilbertNontrivial τ T

end

section
open MeasureTheory Filter
open scoped ENNReal Topology

def expLogPotential (μ : Measure ℂ) (z : ℂ) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (Real.exp (∫ w,logarithmCutoff n ‖z-w‖ ∂μ))

def IsBrownMeasure (τ : ProductOp → ℂ) (T : ProductOp) (μ : Measure ℂ) : Prop :=
  let translate := fun (Hilbert : Type) [NormedAddCommGroup Hilbert]
    [NormedSpace ℂ Hilbert] (operator : Hilbert →L[ℂ] Hilbert) (scalar : ℂ) =>
      operator - algebraMap ℂ (Hilbert →L[ℂ] Hilbert) scalar
  IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
  ∀ z : ℂ, FugledeKadisonDeterminant τ
    (@translate (SourceHilbert SourceCoordinate) productHilbertGroup
      (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup
          (SourceHilbert SourceCoordinate) productHilbertGroup)
        productHilbertInner) T z) = expLogPotential μ z

def ProductBrownClaim : Prop :=
  ∀ (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ),
    IsBrownMeasure sourceVacuumFunctional
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg) (Measure.dirac 0)

end

end FiniteFactor
end
end

namespace FiniteFactor



end FiniteFactor
end OAI


