-- Prove2me | Definitions.Def_OAIE3v2B034
-- name    : OAIE3v2B034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:28.785674+00:00
-- url     : https://prove2.me/theorems/6ef5d05d-63de-48cd-bef4-90d6edb54881
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 35 of 311
-- statement:
--   Definitions bundle 35 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/BooleanCanonicalLogBudget.lean`, `Dynamics/JointExceptionalGainBudget.lean`, `Dynamics/PreparedJointPhysicalScalarBudget.lean`, `Estimates/CanonicalCubeMinorThreshold.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/FiniteFiberVolumeBound.lean`, `Estimates/ModularVectorCoefficientDecomposition.lean`, `Estimates/SeparatedInterpolationBound.lean`, `Estimates/SeparatedRealSamples.lean`, `Estimates/SublevelThresholdBalance.lean`, `Estimates/SymmetricCubeVolume.lean`, `Estimates/SymmetricScalarSublevel.lean`, `Geometry/CenteredFiniteEventSupport.lean`, `Geometry/JointExceptionalSpatialWidthBudget.lean`, `Geometry/OperatorCoordinateBound.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Lattices/AllocatedPhysicalIntegerRankLaw.lean`, `Lattices/LatticeMeasurableRepresentative.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Linear/SpatialMatrixCutoffBudget.lean`, `Polynomial/BooleanPolynomialLogBudget.lean`, `Polynomial/EmbeddedMatrixDeterminantPolynomial.lean`, `Polynomial/PolynomialAnalyticDerivative.lean`, `Polynomial/PolynomialCoordinateSlice.lean`, `Polynomial/PolynomialDilation.lean`, `Polynomial/PolynomialValueCoefficient.lean`, `Polynomial/PreparedUniformDegreeProductiveSource.lean`, `Polynomial/PreparedUniformDegreeTolerance.lean`, `Polynomial/UnivariatePolynomialSublevel.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/SymmetricCubeMeasure.lean`, `Sampling/AllocatedExternalCandidateActualShearForecastScore.lean`, `Sampling/PreparedCenteredShortForecastGoodInterface.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem disjoint_cells_card_mul_le {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (μ : Measure X) (C : Ω → Set X) (A : Set X) (v : ℝ)
    (hdis : Pairwise (fun a b => Disjoint (C a) (C b))) (hm : ∀ ω, MeasurableSet (C ω))
    (hfin : ∀ ω, μ (C ω) ≠ ⊤) (hv : ∀ ω, μ.real (C ω) = v)
    (hsub : ∀ ω, C ω ⊆ A) (hA : μ A ≠ ⊤) :
    (Fintype.card Ω : ℝ) * v ≤ μ.real A := by
  have heq : μ.real (⋃ ω, C ω) = (Fintype.card Ω : ℝ) * v := by
    rw [measureReal_iUnion_fintype hdis hm hfin]
    simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← heq]
  exact measureReal_mono (Set.iUnion_subset hsub) hA

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_basis {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : (I → ℝ) →L[ℝ] E)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, ‖A (Pi.single i 1)‖ ≤ M) :
    ‖A‖ ≤ Fintype.card I * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hsum : A x = ∑ i, (x i) • A (Pi.single i 1) := by
    calc
      A x = A (∑ i, Pi.single i (x i)) :=
        congrArg A (LinearMap.sum_single_apply (fun _ : I => ℝ) x).symm
      _ = ∑ i, A (Pi.single i (x i)) := map_sum A _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hs : Pi.single i (x i) = (x i) • (Pi.single i (1 : ℝ) : I → ℝ) := by
          rw [← Pi.single_smul]
          simp
        rw [hs, map_smul]
  rw [hsum]
  calc
    _ ≤ ∑ i, ‖(x i) • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, ‖x‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hA i) (norm_nonneg _) (norm_nonneg x)
    _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialAnalyticDerivative
namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem mvPolynomial_hasDerivAt_update {ι : Type*} [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (j : ι) (a : ι → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update a j t) p)
      (MvPolynomial.eval a (MvPolynomial.pderiv j p)) (a j) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simpa only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero] using hasDerivAt_const (a j) r
  | add p q hp hq =>
    have h := HasDerivAt.add hp hq
    simp only [map_add]
    exact h
  | mul_X p i hp =>
    by_cases hi : i = j
    · subst i
      have h := hp.mul (hasDerivAt_id (a j))
      simp only [id_eq, Function.update_eq_self, mul_one] at h
      simp only [map_mul, MvPolynomial.eval_X, Function.update_self, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_self, map_add, mul_one]
      exact h
    · have h := hp.mul (hasDerivAt_const (a j) (a i))
      simp only [Function.update_eq_self, mul_zero, add_zero] at h
      simp only [map_mul, MvPolynomial.eval_X, Function.update_of_ne hi, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_of_ne hi, mul_zero,
        add_zero]
      exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SublevelThresholdBalance
namespace OAI

section

namespace Erdos3

theorem sublevel_threshold_balance (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧
      (τ / c) ^ (((n * d : ℕ) : ℝ)⁻¹) =
        (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) ∧
      (u / τ) ^ ((d : ℝ)⁻¹) =
        (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let x : ℝ := u / c
  let a : ℝ := (n : ℝ) / (n + 1)
  have hx : 0 < x := div_pos hu hc
  let τ : ℝ := c * x ^ a
  have hτ : 0 < τ := mul_pos hc (Real.rpow_pos_of_pos hx _)
  have hratio : τ / c = x ^ a := by dsimp [τ]; field_simp
  have hexp : a * (((n * d : ℕ) : ℝ)⁻¹) = ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
    dsimp [a]
    push_cast
    field_simp
  have hexp' : (1 - a) * (d : ℝ)⁻¹ = ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
    dsimp [a]
    push_cast
    field_simp
    ring
  have hquot : u / τ = x ^ (1 - a) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    dsimp [τ, x]
    field_simp
  refine ⟨τ, hτ, ?_, ?_⟩
  · rw [hratio, ← Real.rpow_mul hx.le, hexp]
  · rw [hquot, ← Real.rpow_mul hx.le, hexp']

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberVolumeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem integral_indicator_fiber (ν : Measure B) (s : Set (A × B)) (hs : MeasurableSet s) (x : A) :
    (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) = ν.real {y | (x, y) ∈ s} := by
  have ht : MeasurableSet {y | (x, y) ∈ s} := hs.preimage (measurable_const.prodMk measurable_id)
  have heq : (fun y => s.indicator (fun _ => (1 : ℝ)) (x, y)) =
      {y | (x, y) ∈ s}.indicator (fun _ => (1 : ℝ)) := by
    funext y
    rfl
  rw [heq]
  exact integral_indicator_one ht

theorem product_measureReal_eq_integral_fiber
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set (A × B)) (hs : MeasurableSet s) :
    (μ.prod ν).real s = ∫ x, ν.real {y | (x, y) ∈ s} ∂μ := by
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) = _
  rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator hs)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_indicator_fiber ν s hs x

theorem product_probability_le_bad_set_add
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (bad : Set A) (hbad : MeasurableSet bad)
    {b : ℝ} (hb : 0 ≤ b) (hgood : ∀ x, x ∉ bad → ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real bad + b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).indicator hs
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, bad.indicator (fun _ => (1 : ℝ)) x + b ∂μ := by
      apply integral_mono hi.integral_prod_left
        (((integrable_const (1 : ℝ)).indicator hbad).add (integrable_const b))
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤
        bad.indicator (fun _ => (1 : ℝ)) x + b
      rw [integral_indicator_fiber ν s hs x]
      by_cases hx : x ∈ bad
      · rw [Set.indicator_of_mem hx]
        have hle : ν.real {y | (x, y) ∈ s} ≤ 1 := by
          have h := measureReal_mono (μ := ν) (Set.subset_univ {y | (x, y) ∈ s})
          simp only [probReal_univ] at h
          exact h
        linarith
      · rw [Set.indicator_of_notMem hx, zero_add]
        exact hgood x hx
    _ = _ := by
      rw [integral_add ((integrable_const (1 : ℝ)).indicator hbad) (integrable_const b),
        integral_indicator_const (1 : ℝ) hbad, integral_const]
      simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedInterpolationBound
namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem coeff_X_sub_C_mul_abs_le (p : ℝ[X]) {M y : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n, |p.coeff n| ≤ M) (hy : |y| ≤ 1) (n : ℕ) :
    |((X - C y) * p).coeff n| ≤ 2 * M := by
  cases n with
  | zero =>
    simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_mul, abs_neg,
      abs_mul]
    calc
      |y| * |p.coeff 0| ≤ 1 * M := mul_le_mul hy (hp 0) (abs_nonneg _) zero_le_one
      _ ≤ 2 * M := by linarith
  | succ n =>
    rw [coeff_X_sub_C_mul]
    calc
      |p.coeff n - y * p.coeff (n + 1)| ≤ |p.coeff n| + |y * p.coeff (n + 1)| := abs_sub _ _
      _ = |p.coeff n| + |y| * |p.coeff (n + 1)| := by rw [abs_mul]
      _ ≤ M + 1 * M := add_le_add (hp n) (mul_le_mul hy (hp (n + 1)) (abs_nonneg _) zero_le_one)
      _ = 2 * M := by ring

theorem coeff_prod_X_sub_C_abs_le {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, |v i| ≤ 1) (n : ℕ) :
    |(∏ i ∈ s, (X - C (v i))).coeff n| ≤ (2 : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    have hp (k : ℕ) : |(∏ j ∈ s, (X - C (v j))).coeff k| ≤ (2 : ℝ) ^ s.card := by
      exact ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)) k
    simpa only [mul_comm] using coeff_X_sub_C_mul_abs_le (∏ j ∈ s, (X - C (v j)))
      (by positivity : 0 ≤ (2 : ℝ) ^ s.card) hp (hv i (Finset.mem_insert_self i s)) n

theorem lagrange_basis_coeff_abs_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (i : ι) {r : ℝ} (hr : 0 < r)
    (hv : ∀ j ∈ s, |v j| ≤ 1)
    (hsep : ∀ j ∈ s.erase i, r ≤ |v i - v j|) (n : ℕ) :
    |(Lagrange.basis s v i).coeff n| ≤ (2 / r) ^ (s.erase i).card := by
  have heq : Lagrange.basis s v i =
      C (∏ j ∈ s.erase i, (v i - v j)⁻¹) * ∏ j ∈ s.erase i, (X - C (v j)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, map_prod]
  have hprod : (∏ j ∈ s.erase i, |(v i - v j)⁻¹|) ≤ (r⁻¹) ^ (s.erase i).card := by
    apply (Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j hj => ?_)).trans_eq
      (Finset.prod_const _)
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hr (hsep j hj)
  rw [heq, coeff_C_mul, abs_mul, Finset.abs_prod]
  calc
    _ ≤ (r⁻¹) ^ (s.erase i).card * (2 : ℝ) ^ (s.erase i).card :=
      mul_le_mul hprod (coeff_prod_X_sub_C_abs_le (s.erase i) v
        (fun j hj => hv j (Finset.mem_of_mem_erase hj)) n) (abs_nonneg _) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem polynomial_coeff_le_of_separated_samples (p : ℝ[X]) (t : Finset ℝ)
    {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (hdeg : p.degree < t.card)
    (ht : ∀ x ∈ t, |x| ≤ 1) (hval : ∀ x ∈ t, |p.eval x| ≤ u)
    (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r ≤ |x - y|) (n : ℕ) :
    |p.coeff n| ≤ (t.card : ℝ) * u * (2 / r) ^ (t.card - 1) := by
  classical
  have heq : p = Lagrange.interpolate t id (fun x => p.eval x) :=
    Lagrange.eq_interpolate (fun _ _ _ _ h => h) hdeg
  have hterm (x : ℝ) (hx : x ∈ t) :
      |(C (p.eval x) * Lagrange.basis t id x).coeff n| ≤ u * (2 / r) ^ (t.card - 1) := by
    rw [coeff_C_mul, abs_mul]
    apply mul_le_mul (hval x hx) _ (abs_nonneg _) hu
    have h := lagrange_basis_coeff_abs_le t id x hr ht
      (fun y hy => hsep x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm) n
    simpa only [Finset.card_erase_of_mem hx] using h
  calc
    |p.coeff n| = |(∑ x ∈ t, C (p.eval x) * Lagrange.basis t id x).coeff n| :=
      congrArg (fun q : ℝ[X] => |q.coeff n|) heq
    _ = |∑ x ∈ t, (C (p.eval x) * Lagrange.basis t id x).coeff n| := by rw [finsetSum_coeff]
    _ ≤ ∑ x ∈ t, |(C (p.eval x) * Lagrange.basis t id x).coeff n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ t, u * (2 / r) ^ (t.card - 1) := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedRealSamples
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem real_interval_cover_measure_le (t : Finset ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (⋃ y ∈ t, Set.Ioo (y - r) (y + r)) ≤ 2 * (t.card : ℝ) * r := by
  apply (measureReal_biUnion_finset_le t (fun y => Set.Ioo (y - r) (y + r))).trans
  have hlen (y : ℝ) : volume.real (Set.Ioo (y - r) (y + r)) = 2 * r := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  simp only [hlen, Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_rfl

theorem exists_separated_real_samples (s : Set ℝ) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (hlarge : 2 * (n : ℝ) * r < volume.real s) :
    ∃ t : Finset ℝ, t.card = n ∧ (↑t : Set ℝ) ⊆ s ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    have hsmall : 2 * (n : ℝ) * r < volume.real s := by
      push_cast at hlarge
      nlinarith
    obtain ⟨t, hcard, hts, hsep⟩ := ih hsmall
    let cover := ⋃ y ∈ t, Set.Ioo (y - r) (y + r)
    have hfinite : volume cover ≠ ⊤ := by
      apply measure_biUnion_ne_top t.finite_toSet
      intro y _
      simp only [Real.volume_Ioo, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
    have hnot : ¬s ⊆ cover := by
      intro hsub
      have h := (measureReal_mono hsub hfinite).trans (real_interval_cover_measure_le t hr.le)
      rw [hcard] at h
      linarith
    obtain ⟨x, hxs, hxc⟩ := Set.not_subset.mp hnot
    have hfar (y : ℝ) (hy : y ∈ t) : r ≤ |x - y| := by
      by_contra! h
      have hxy := abs_lt.mp h
      apply hxc
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, ⟨by linarith, by linarith⟩⟩⟩
    have hxt : x ∉ t := by
      intro hx
      have h := hfar x hx
      simp only [sub_self, abs_zero] at h
      linarith
    refine ⟨insert x t, by rw [Finset.card_insert_of_notMem hxt, hcard], ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxs
      · exact hts hy
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | hat
      · subst a
        rcases Finset.mem_insert.mp hb with rfl | hbt
        · exact False.elim (hab rfl)
        · exact hfar b hbt
      · rcases Finset.mem_insert.mp hb with hbx | hbt
        · subst b
          simpa only [abs_sub_comm] using hfar a hat
        · exact hsep a hat b hbt hab

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UnivariatePolynomialSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped BigOperators

def unitPolynomialSublevel (p : ℝ[X]) (u : ℝ) : Set ℝ :=
  {x | |x| ≤ 1 ∧ |p.eval x| ≤ u}

theorem unitPolynomialSublevel_power_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    |p.coeff k| * (volume.real (unitPolynomialSublevel p u)) ^ d ≤
      (d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d * u := by
  let mass := volume.real (unitPolynomialSublevel p u)
  change |p.coeff k| * mass ^ d ≤ _
  have hmass0 : 0 ≤ mass := measureReal_nonneg
  by_cases hz : mass = 0
  · rw [hz, zero_pow (Nat.ne_of_gt hd), mul_zero]
    positivity
  have hmass : 0 < mass := lt_of_le_of_ne hmass0 (Ne.symm hz)
  let r := mass / (4 * (d + 1 : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * (d + 1 : ℝ) * r = mass / 2 := by
    dsimp [r]
    field_simp
    ring
  have hlarge : 2 * ((d + 1 : ℕ) : ℝ) * r < volume.real (unitPolynomialSublevel p u) := by
    push_cast
    rw [hscale]
    change mass / 2 < mass
    linarith
  obtain ⟨t, htcard, hts, htsep⟩ := exists_separated_real_samples (unitPolynomialSublevel p u) hr (d + 1) hlarge
  have hdegree : p.degree < t.card := by
    rw [htcard]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hcoeff := polynomial_coeff_le_of_separated_samples p t hr hu hdegree
    (fun x hx => (hts hx).1) (fun x hx => (hts hx).2) htsep k
  rw [htcard, Nat.add_sub_cancel] at hcoeff
  push_cast at hcoeff
  have hcancel : (2 / r) * mass = 8 * (d + 1 : ℝ) := by
    dsimp [r]
    field_simp
    ring
  calc
    |p.coeff k| * mass ^ d ≤ ((d + 1 : ℝ) * u * (2 / r) ^ d) * mass ^ d :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hmass0 d)
    _ = (d + 1 : ℝ) * u * ((2 / r) * mass) ^ d := by rw [mul_pow]; ring
    _ = _ := by rw [hcancel]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricScalarSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped ENNReal

noncomputable def symmetricScalarMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance symmetricScalarMeasure_probability : IsProbabilityMeasure symmetricScalarMeasure := by
  constructor
  norm_num [symmetricScalarMeasure, Measure.smul_apply, ENNReal.smul_def, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem symmetricScalarMeasure_sublevel (p : ℝ[X]) (u : ℝ) :
    symmetricScalarMeasure.real {x | |p.eval x| ≤ u} =
      (1 / 2 : ℝ) * volume.real (unitPolynomialSublevel p u) := by
  have hs : MeasurableSet {x | |p.eval x| ≤ u} := (isClosed_le p.continuous.abs continuous_const).measurableSet
  have heq : {x | |p.eval x| ≤ u} ∩ Set.Icc (-1 : ℝ) 1 = unitPolynomialSublevel p u := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, unitPolynomialSublevel, abs_le]
    tauto
  rw [symmetricScalarMeasure, measureReal_ennreal_smul_apply, measureReal_restrict_apply hs, heq]
  norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinateSlice
namespace OAI

section

namespace Erdos3

noncomputable def polynomialCoordinateSlice {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) : Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ n p).map (MvPolynomial.eval x)

theorem polynomialCoordinateSlice_eval {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (y : ℝ) :
    (polynomialCoordinateSlice p x).eval y = MvPolynomial.eval (Fin.cons y x) p :=
  (MvPolynomial.eval_eq_eval_mv_eval' x y p).symm

theorem polynomialCoordinateSlice_coeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (k : ℕ) :
    (polynomialCoordinateSlice p x).coeff k =
      MvPolynomial.eval x ((MvPolynomial.finSuccEquiv ℝ n p).coeff k) := by
  simp only [polynomialCoordinateSlice, Polynomial.coeff_map]

theorem polynomialCoordinateSlice_degree_le {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : p.degreeOf 0 ≤ d) (x : Fin n → ℝ) :
    (polynomialCoordinateSlice p x).natDegree ≤ d := by
  apply (Polynomial.natDegree_map_le).trans
  exact (MvPolynomial.natDegree_finSuccEquiv p).le.trans hp

theorem polynomialCoordinateSlice_coefficient_degrees {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : ∀ j, p.degreeOf j ≤ d) (k : ℕ) (j : Fin n) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).degreeOf j ≤ d :=
  (MvPolynomial.degreeOf_coeff_finSuccEquiv p j k).trans (hp j.succ)

theorem polynomialCoordinateSlice_selected_coefficient {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (m : Fin (n + 1) →₀ ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff (m 0)).coeff m.tail =
      p.coeff m := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]

theorem polynomialCoordinateSlice_measurable_eval {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => (polynomialCoordinateSlice p z.1).eval z.2) := by
  have hcons : Continuous (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  have h := (p.continuous_eval.comp hcons).measurable
  simp only [Function.comp_def] at h
  simpa only [polynomialCoordinateSlice_eval] using h

theorem polynomialCoordinateSlice_measurable_coeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (k : ℕ) :
    Measurable (fun x => (polynomialCoordinateSlice p x).coeff k) := by
  simpa only [polynomialCoordinateSlice_coeff] using
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).continuous_eval.measurable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SymmetricCubeMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def symmetricCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => symmetricScalarMeasure)

instance symmetricCubeMeasure_probability (n : ℕ) : IsProbabilityMeasure (symmetricCubeMeasure n) := by
  unfold symmetricCubeMeasure
  infer_instance

theorem symmetricCubeMeasure_zero : symmetricCubeMeasure 0 = Measure.dirac 0 :=
  Measure.pi_of_empty _ _

theorem symmetricCubeMeasure_cons (n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ))
      ((symmetricCubeMeasure n).prod symmetricScalarMeasure) (symmetricCubeMeasure (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e (symmetricCubeMeasure (n + 1))
      (symmetricScalarMeasure.prod (symmetricCubeMeasure n)) :=
    measurePreserving_piFinSuccAbove (fun _ => symmetricScalarMeasure) 0
  have h := (MeasurePreserving.symm e he).comp
    (Measure.measurePreserving_swap (μ := symmetricCubeMeasure n) (ν := symmetricScalarMeasure))
  convert h using 1
  funext z
  simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  change Fin.cons z.2 z.1 = @Fin.insertNth n (fun _ => ℝ) 0 z.2 z.1
  exact (Fin.insertNth_zero' _ _).symm

theorem symmetricCubeMeasure_sublevel_succ {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (u : ℝ) :
    (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} =
      ((symmetricCubeMeasure n).prod symmetricScalarMeasure).real
        {z | |(polynomialCoordinateSlice p z.1).eval z.2| ≤ u} := by
  have hs : MeasurableSet {x | |MvPolynomial.eval x p| ≤ u} :=
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet
  have h := (symmetricCubeMeasure_cons n).measureReal_preimage hs.nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, polynomialCoordinateSlice_eval] using h.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricCubeVolume
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal BigOperators

def symmetricUnitBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)

theorem symmetricUnitBox_mem (n : ℕ) (x : Fin n → ℝ) :
    x ∈ symmetricUnitBox n ↔ ∀ i, |x i| ≤ 1 := by
  simp only [symmetricUnitBox, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc, abs_le]

theorem symmetricCubeMeasure_eq_smul_restrict (n : ℕ) :
    symmetricCubeMeasure n = (1 / 2 : ℝ≥0∞) ^ n • volume.restrict (symmetricUnitBox n) := by
  unfold symmetricCubeMeasure
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  change (1 / 2 : ℝ≥0∞) ^ n * volume ((Set.pi Set.univ s) ∩
    (Set.pi Set.univ fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) = _
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [symmetricScalarMeasure, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem symmetricUnitBox_volume_inter (n : ℕ) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    volume.real (symmetricUnitBox n ∩ s) = (2 : ℝ) ^ n * (symmetricCubeMeasure n).real s := by
  rw [symmetricCubeMeasure_eq_smul_restrict, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs, ENNReal.toReal_pow]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [← mul_assoc, ← mul_pow]
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]
  rw [Set.inter_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def dilateMvPolynomial {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial m
    (p.coeff m * ∏ i ∈ m.support, R ^ m i)

theorem dilateMvPolynomial_coeff {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    (dilateMvPolynomial R p).coeff m =
      p.coeff m * ∏ i ∈ m.support, R ^ m i := by
  classical
  rw [dilateMvPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem dilateMvPolynomial_support_subset {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) :
    (dilateMvPolynomial R p).support ⊆ p.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, dilateMvPolynomial_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)

theorem dilateMvPolynomial_degree_le {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ)
    (i : ι) {d : ℕ} (hp : p.degreeOf i ≤ d) : (dilateMvPolynomial R p).degreeOf i ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff] at hp ⊢
  exact fun m hm => hp m (dilateMvPolynomial_support_subset R p hm)

theorem dilateMvPolynomial_eval {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (dilateMvPolynomial R p) = MvPolynomial.eval (R • x) p := by
  classical
  rw [dilateMvPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem dilateMvPolynomial_coeff_abs_le {ι : Type*} {R : ℝ} (hR : 1 ≤ R)
    (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    |p.coeff m| ≤ |(dilateMvPolynomial R p).coeff m| := by
  have hw : 1 ≤ ∏ i ∈ m.support, R ^ m i := by
    calc
      1 = ∏ _i ∈ m.support, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ m.support, R ^ m i := Finset.prod_le_prod (fun _ _ => zero_le_one)
        (fun index _ => one_le_pow₀ hR)
  rw [dilateMvPolynomial_coeff, abs_mul, abs_of_nonneg (zero_le_one.trans hw)]
  exact le_mul_of_one_le_right (abs_nonneg _) hw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialValueCoefficient
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_support_card_le {N d : ℕ}
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ i, p.degreeOf i ≤ d) :
    p.support.card ≤ (d + 1) ^ N := by
  classical
  let f : p.support → (Fin N → Fin (d + 1)) := fun m i =>
    ⟨m.val i, Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp (hp i)) m.val m.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hab i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

section

namespace Erdos3

open MeasureTheory

def unitMvPolynomialSublevel {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) : Set (Fin N → ℝ) :=
  symmetricUnitBox N ∩ {x | |MvPolynomial.eval x p| ≤ u}

theorem unitMvPolynomialSublevel_volume_ne_top {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) :
    volume (unitMvPolynomialSublevel p u) ≠ ⊤ := by
  have hbox : volume (symmetricUnitBox N) ≠ ⊤ := by
    rw [symmetricUnitBox, volume_pi_pi]
    exact ENNReal.prod_ne_top (fun _ _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact measure_ne_top_of_subset Set.inter_subset_left hbox

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Matrix

noncomputable def affinePairScale (H L : ℝ) : Fin 2 → ℝ := ![H, H / L]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def cubeMinorVariableCount (O α : Type*) [Fintype O] [Fintype α] (h : ℕ) : ℕ :=
  Fintype.card O * (h * (Fintype.card α + 1))

def cubeMinorDegree (O : Type*) [Fintype O] (h : ℕ) : ℕ :=
  max 1 (Fintype.card O * (h - 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
namespace OAI

section

namespace Erdos3

def productMinorEntryLog (q h : ℕ) (P : ℝ) : ℝ := P+h+(h : ℝ)*q

end Erdos3

end

section

namespace Erdos3

def cubeMinorConstantLog (j q h N d : ℕ) : ℝ :=
  (j : ℝ)*h*((q : ℝ)+1)^2+3*N+(d+1 : ℝ)+d*(8+(d+1 : ℝ))

def cubeMinorScaleLog (j N d : ℕ) (P : ℝ) : ℝ := (N : ℝ)*d+j*P

def cubeMinorThresholdLog (m j q h N d : ℕ) (P E : ℝ) : ℝ :=
  cubeMinorScaleLog j N d P+2+(N*d : ℕ)*(cubeMinorConstantLog j q h N d+m+E+2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def canonicalBooleanMinorLog (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) (P E : ℝ) : ℝ :=
  cubeMinorThresholdLog 1 (Fintype.card O) (Fintype.card α) h
    (cubeMinorVariableCount O α h) (cubeMinorDegree O h) P E

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialLogBudget
namespace OAI

section

namespace Erdos3

def booleanJetMassLog (q h : ℕ) (P : ℝ) : ℝ := q+P+(h : ℝ)*q

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

def scalarNativeDimension (s : ℕ) : ℕ := (s + 1) * (s + 3)

theorem scalarNativeDimension_capacity {r s : ℕ} (hrs : r ≤ s) :
    (r + 1) * (r + 3) ≤ scalarNativeDimension s := by
  exact Nat.mul_le_mul (Nat.add_le_add_right hrs 1) (Nat.add_le_add_right hrs 3)

theorem scalarNativeDimension_selection_bound {r s : ℕ} (hrs : r ≤ s) :
    r + 1 ≤ scalarNativeDimension s := by
  exact (Nat.le_mul_of_pos_right (r + 1) (by omega : 0 < r + 3)).trans
    (scalarNativeDimension_capacity hrs)

def scalarNativeSelection {r s : ℕ} (hrs : r ≤ s) :
    Fin (r + 1) ↪ Fin (scalarNativeDimension s) where
  toFun a := ⟨a.val, a.isLt.trans_le (scalarNativeDimension_selection_bound hrs)⟩
  inj' := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin (scalarNativeDimension s) => z.val) hab)

@[simp] theorem scalarNativeSelection_val {r s : ℕ} (hrs : r ≤ s) (a : Fin (r + 1)) :
    (scalarNativeSelection hrs a).val = a.val := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open scoped NNReal

def spatialMovementEnvelope {A : Type*} [Semiring A] (p l : A) : A := p + l + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixCutoffBudget
namespace OAI

section

namespace Erdos3

theorem nat_mul_factorial_le_exp_square (n : ℕ) :
    ((n * n.factorial : ℕ) : ℝ) ≤ Real.exp (((n : ℝ) + 1) ^ 2) := by
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    have h := Real.add_one_le_exp (n : ℝ)
    linarith
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hp : (n : ℝ) ^ n ≤ Real.exp ((n : ℝ) * n) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn n
  calc
    _ = (n : ℝ) * n.factorial := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp ((n : ℝ) * n) :=
      mul_le_mul hn (hf.trans hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) + (n : ℝ) * n) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem determinantCutoff_lip_le_exp (n : ℕ) {κ K : ℝ}
    (hκ : 0 < κ) (hK : κ⁻¹ ≤ Real.exp K) :
    (2 / κ) * ((n * n.factorial : ℕ) : ℝ) ≤
      Real.exp (K + ((n : ℝ) + 1) ^ 2 + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc
    _ = (2 * κ⁻¹) * ((n * n.factorial : ℕ) : ℝ) := by rw [div_eq_mul_inv]
    _ ≤ (Real.exp 1 * Real.exp K) * Real.exp (((n : ℝ) + 1) ^ 2) := by
      gcongr
      exact nat_mul_factorial_le_exp_square n
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointExceptionalGainBudget
namespace OAI

section

namespace Erdos3

theorem jointExceptional_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 8
  norm_num [← Real.exp_nat_mul] at hp ⊢
  exact hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedJointPhysicalScalarBudget
namespace OAI

section

namespace Erdos3

def jointPhysicalBaseLog (Pwidth E V : ℝ) : ℝ := 8 * Pwidth + V + 2 * E + 134

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularVectorCoefficientDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {A B I R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [CommRing R]

noncomputable def designatedVectorComponent (S : B → A → Finset I)
    (Q : B → MvPolynomial I R) (c : B → A → R) (b : B) : MvPolynomial I R :=
  Q b + ∑ a, c b a • ∏ i ∈ S b a, X i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredFiniteEventSupport
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C)

theorem centeredFinite_event_measurableSet (event : Set (C × Ω))
    (hevent : ∀ x, MeasurableSet {c | (c,x) ∈ event}) : MeasurableSet event := by
  have hm : Measurable (fun z : C × Ω => if z ∈ event then (1 : ℝ) else 0) :=
    measurable_from_prod_countable_left
      (fun x => measurable_const.ite (hevent x) measurable_const)
  have he : event = (fun z : C × Ω => if z ∈ event then (1 : ℝ) else 0) ⁻¹' {1} := by
    ext z
    by_cases hz : z ∈ event <;> simp [hz]
  rw [he]
  exact hm (measurableSet_singleton 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JointExceptionalSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem jointExceptionalSpatialSize_polynomial {P : ℝ} (hP : 0 ≤ P) :
    10*P+128 ≤ (P+4)^4 := by
  nlinarith only [hP, pow_nonneg hP 2, pow_nonneg hP 3, pow_nonneg hP 4]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem finite_nat_sup_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℕ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x => s.sup (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sup_insert]
    exact (hf i (Finset.mem_insert_self _ _)).sup
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMeasurableRepresentative
namespace OAI

section

open MeasureTheory Module

namespace Erdos3

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem exists_measurable_representative_zspan (b : Basis I ℝ E) :
    ∃ r : E ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup → E,
      Measurable r ∧ ∀ x,
        QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup (r x) = x := by
  let e : E ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup ≃
      ZSpan.fundamentalDomain b := ZSpan.quotientEquiv b
  have hsymm (x : ZSpan.fundamentalDomain b) :
      e.symm x = QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup (x : E) := by
    exact ZSpan.quotientEquiv.symm_apply b x
  have hcont : Continuous (fun x : E =>
      (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup) x) :=
    QuotientAddGroup.continuous_mk
  have hinj : Set.InjOn
      (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup)
      (ZSpan.fundamentalDomain b) := by
    intro x hx y hy hxy
    have he : e.symm ⟨x, hx⟩ = e.symm ⟨y, hy⟩ := by
      simpa only [hsymm] using hxy
    exact congrArg Subtype.val (e.symm.injective he)
  have hfun : (e.symm : ZSpan.fundamentalDomain b → _) =
      (ZSpan.fundamentalDomain b).domRestrict
        (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup) :=
    funext hsymm
  have hem : MeasurableEmbedding (e.symm : ZSpan.fundamentalDomain b → _) := by
    rw [hfun]
    exact hcont.continuousOn.measurableEmbedding (ZSpan.fundamentalDomain_measurableSet b) hinj
  have he : Measurable e := hem.measurable_comp_iff.mp (by simpa using measurable_id)
  refine ⟨fun x => (e x : E), measurable_subtype_coe.comp he, ?_⟩
  intro x
  simpa only [hsymm] using e.symm_apply_apply x

theorem lattice_exists_measurable_representative (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ) :
    ∃ r : E ⧸ Λ.toAddSubgroup → E,
      Measurable r ∧ ∀ x, QuotientAddGroup.mk' Λ.toAddSubgroup (r x) = x := by
  have hspan : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ Λ : I → E)) = Λ :=
    b.ofZLatticeBasis_span ℝ Λ
  rw [← hspan]
  exact exists_measurable_representative_zspan (b.ofZLatticeBasis ℝ Λ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

noncomputable def canonicalAffineMinorLog (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) (P E F : ℝ) : ℝ :=
  canonicalBooleanMinorLog O α h P E +
    (cubeMinorVariableCount O α h * cubeMinorDegree O h : ℕ) *
      (cubeMinorVariableCount O α h : ℝ) * F

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeTolerance
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def preparedUniformDegreeTolerance (t : ι → ℝ) (Qσ : ℝ) : ℝ :=
  min (∏ i, t i) (Real.exp (-Qσ))

noncomputable def preparedUniformDegreeScaleLog (pRadius : ℝ) (Ptail : ι → ℝ)
    (Qσ : ℝ) : ℝ :=
  pRadius + ∑ i, Ptail i + Qσ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface
namespace OAI

section

namespace Erdos3

def preparedForecastGoodCertificateBudget (baseB₀ Pchart Pwidth g V : ℝ) : ℝ :=
  1 + baseB₀ + Pchart + jointPhysicalBaseLog Pwidth (g + 8) V

def preparedForecastGoodAnalyticBudget (Asp : ℕ) (baseB₀ Pchart Pwidth g V : ℝ) : ℝ :=
  preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V + Pwidth +
    (Pchart + Asp) ^ Asp + g + 9

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

def preparedUniformDegreeProductiveCertificateBudget
    (M nX : ℕ) (pRadius Pscale Pseed Qw Elog Vlog : ℝ) : ℝ :=
  1 + (M : ℝ) + (nX : ℝ) + pRadius + Pscale + Pseed + Qw + Elog + Vlog

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal TensorProduct Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {R σ : Fin m → ℝ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

def actualForecastDataModelRequired (budget Pnative massLog u p : ℝ) : ℝ :=
  u + 2 * p + max (max budget (3 * Pnative + 3))
    (2 * u + 4 * p + max 0 massLog + 20) + 32

end Erdos3.VectorPolynomial

end

end OAI
end


