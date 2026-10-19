-- Prove2me | Definitions.Def_OAIE3v2B065
-- name    : OAIE3v2B065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:15:03.874661+00:00
-- url     : https://prove2.me/theorems/4e1ba0bb-2305-4025-8e14-84023c49e2fc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 66 of 311
-- statement:
--   Definitions bundle 66 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B015`, `OAIE3v2B018`, `OAIE3v2B026`, `OAIE3v2B028`, `OAIE3v2B030`, `OAIE3v2B031`, `OAIE3v2B032`, `OAIE3v2B033`, `OAIE3v2B034` of this split.
--
--   Modules: `Dynamics/JointExceptionalGainBudget.lean`, `Dynamics/PatchTopNetBudget.lean`, `Estimates/AllocatedIdealPhysicalCover.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/NormalizedDeterminantCutoff.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/RowRestrictedDeckSiteMask.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/SymmetricCubeSublevel.lean`, `Estimates/SymmetricScalarSublevel.lean`, `Geometry/AllocatedInactiveSupportBudget.lean`, `Geometry/AllocatedProductChartRadius.lean`, `Geometry/BoxChartCutoff.lean`, `Geometry/FiniteRowChartRadiusBudget.lean`, `Geometry/NormalizedSpatialAmplitudeShift.lean`, `Geometry/SmoothSpatialCostBudget.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Geometry/SpatialTwoBlockEquiv.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedPhysicalIntegerRankLaw.lean`, `Lattices/CoverBasisResidues.lean`, `Lattices/IntegerBooleanSiteReconstruction.lean`, `Lattices/UniformResidueSmallPeriod.lean`, `Linear/AllocatedKernelPrimitiveBudget.lean`, `Linear/SmoothMatrixBlockBudget.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/EmbeddedMatrixDeterminantPolynomial.lean`, `Polynomial/PolynomialAnalyticDerivative.lean`, `Polynomial/PolynomialDeterminantDerivativeBound.lean`, `Polynomial/PolynomialSublevelThresholdBudget.lean`, `Polynomial/PolynomialThresholdBudget.lean`, `Polynomial/PolynomialValueCoefficient.lean`, `Polynomial/ShiftedSmoothPolynomialSublevel.lean`, `Polynomial/UnivariatePolynomialSublevel.lean`, `Probability/PMFPointMassMixture.lean`, `Probability/SymmetricCubeMeasure.lean`, `Sampling/CanonicalSamplerTuple.lean`, `Sampling/PatchKernelGridBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B026
import Definitions.Def_OAIE3v2B028
import Definitions.Def_OAIE3v2B030
import Definitions.Def_OAIE3v2B031
import Definitions.Def_OAIE3v2B032
import Definitions.Def_OAIE3v2B033
import Definitions.Def_OAIE3v2B034

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxChartCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem coordinateBoxCutoff_range {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (r : ℝ) (v : ι → ℝ) :
    0 ≤ coordinateBoxCutoff χ r v ∧ coordinateBoxCutoff χ r v ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (hχ _).1),
    Finset.prod_le_one (fun index _ => (hχ _).1) (fun index _ => (hχ _).2)⟩

theorem coordinateBoxCutoff_eq_one {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, |x| ≤ 1 / 2 → χ x = 1) {r : ℝ} (hr : 0 < r)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ r / 2) : coordinateBoxCutoff χ r v = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply hχ
  rw [abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  linarith [hv i]

theorem coordinateBoxCutoff_eq_zero {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 3 / 4 ≤ |x| → χ x = 0) {r : ℝ} (hr : 0 < r)
    (v : ι → ℝ) (hv : ∃ i, 3 * r / 4 ≤ |v i|) : coordinateBoxCutoff χ r v = 0 := by
  classical
  obtain ⟨i, hi⟩ := hv
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply hχ
  rw [abs_div, abs_of_pos hr]
  apply (le_div_iff₀ hr).mpr
  linarith

theorem contDiff_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (r : ℝ) : ContDiff ℝ ∞ (coordinateBoxCutoff (ι := ι) χ r) := by
  unfold coordinateBoxCutoff
  apply contDiff_prod
  intro i _
  exact hχ.comp ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.div_const r)

theorem hasCompactSupport_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 3 / 4 ≤ |x| → χ x = 0) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (coordinateBoxCutoff (ι := ι) χ r) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ι → ℝ) (3 * r / 4))
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * r / 4)).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hv (coordinateBoxCutoff_eq_zero χ hχ hr v ⟨i, hi.le⟩)

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

theorem mvPolynomial_fderiv_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (a : ι → ℝ) (j : ι) :
    fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a (Pi.single j 1) =
      MvPolynomial.eval a (MvPolynomial.pderiv j p) := by
  have hupdate : HasDerivAt (fun t => Function.update a j t) (Pi.single j 1) (a j) := by
    apply hasDerivAt_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self, Pi.single_eq_same]
      exact hasDerivAt_id (a j)
    · simpa [Function.update_of_ne hi, Pi.single_eq_of_ne hi] using hasDerivAt_const (a j) (a i)
  have hp := (mvPolynomial_contDiff_eval p).differentiable (by norm_num)
  have hf : HasFDerivAt (fun x : ι → ℝ => MvPolynomial.eval x p)
      (fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a) (Function.update a j (a j)) := by
    rw [Function.update_eq_self]
    exact (hp a).hasFDerivAt
  have h := hf.comp_hasDerivAt (a j) hupdate
  simp only [Function.comp_def] at h
  exact h.unique (mvPolynomial_hasDerivAt_update p j a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_pderiv_eval_abs_le {I O : Type*} [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) (a : I → ℝ) (j : I) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hM : ∀ row col, |MvPolynomial.eval a (M row col)| ≤ L)
    (hd : ∀ row col, |MvPolynomial.eval a (MvPolynomial.pderiv j (M row col))| ≤ D) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j M.det)| ≤
      (Fintype.card O).factorial * (Fintype.card O * D * L ^ Fintype.card O) := by
  classical
  rw [Matrix.det_apply', map_sum, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm O, |MvPolynomial.eval a (MvPolynomial.pderiv j
        (((Equiv.Perm.sign σ : ℤ) : MvPolynomial I ℝ) * ∏ i, M (σ i) i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm O, Fintype.card O * D * L ^ Fintype.card O := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial I ℝ)) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
      rw [hsign, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, abs_mul,
        ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul]
      simpa only [Finset.card_univ] using mvPolynomial_prod_pderiv_eval_abs_le_of_bound
        Finset.univ (fun i => M (σ i) i) j a hL hD
        (fun i _ => hM (σ i) i) (fun i _ => hd (σ i) i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem polynomial_det_fderiv_norm_le {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) (a : I → ℝ) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hM : ∀ row col, |MvPolynomial.eval a (M row col)| ≤ L)
    (hd : ∀ row col j, |MvPolynomial.eval a (MvPolynomial.pderiv j (M row col))| ≤ D) :
    ‖fderiv ℝ (fun x => (M.map (MvPolynomial.eval x)).det) a‖ ≤
      Fintype.card I * ((Fintype.card O).factorial *
        (Fintype.card O * D * L ^ Fintype.card O)) := by
  rw [polynomial_det_eval_function]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  apply clm_norm_le_card_mul_of_basis _ (by positivity)
  intro j
  rw [mvPolynomial_fderiv_coordinate, Real.norm_eq_abs]
  exact polynomial_det_pderiv_eval_abs_le M a j hL hD hM (fun row col => hd row col j)

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

theorem unitPolynomialSublevel_rpow_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (k : ℕ) (hk : c ≤ |p.coeff k|) :
    volume.real (unitPolynomialSublevel p u) ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  unfold univariateSublevelConstant
  rw [← Real.mul_rpow (by positivity : 0 ≤ (d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d)
    (div_nonneg hu hc.le)]
  apply (Real.le_rpow_inv_iff_of_pos measureReal_nonneg (by positivity)
    (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  rw [Real.rpow_natCast, ← mul_div_assoc]
  apply (le_div_iff₀ hc).mpr
  calc
    (volume.real (unitPolynomialSublevel p u)) ^ d * c ≤
        |p.coeff k| * (volume.real (unitPolynomialSublevel p u)) ^ d := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hk (pow_nonneg measureReal_nonneg d)
    _ ≤ _ := unitPolynomialSublevel_power_bound p hd hdeg hu k

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

theorem symmetricScalarMeasure_sublevel_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (k : ℕ) (hk : c ≤ |p.coeff k|) :
    symmetricScalarMeasure.real {x | |p.eval x| ≤ u} ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  rw [symmetricScalarMeasure_sublevel]
  apply le_trans _ (unitPolynomialSublevel_rpow_bound p hd hdeg hu hc k hk)
  nlinarith [measureReal_nonneg (μ := volume) (s := unitPolynomialSublevel p u)]

theorem polynomial_family_sublevel_step {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (p : T → ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree ≤ d)
    (hval : Measurable (fun z : T × ℝ => (p z.1).eval z.2))
    (k : ℕ) (hcoeff : Measurable (fun x => (p x).coeff k))
    {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 < τ) :
    (μ.prod symmetricScalarMeasure).real {z | |(p z.1).eval z.2| ≤ u} ≤
      μ.real {x | |(p x).coeff k| ≤ τ} +
        univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) := by
  apply product_probability_le_bad_set_add μ symmetricScalarMeasure _
    (measurableSet_le (continuous_abs.measurable.comp hval) measurable_const) _
    (measurableSet_le (continuous_abs.measurable.comp hcoeff) measurable_const)
    (mul_nonneg (univariateSublevelConstant_pos d).le (Real.rpow_nonneg (div_nonneg hu hτ.le) _))
  intro x hx
  have hk : τ ≤ |(p x).coeff k| := (lt_of_not_ge hx).le
  exact symmetricScalarMeasure_sublevel_bound (p x) hd (hdeg x) hu hτ k hk

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

theorem symmetricCubeMeasure_sublevel_step {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hd : 0 < d) (hp : p.degreeOf 0 ≤ d)
    (k : ℕ) {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 < τ) :
    (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} ≤
      (symmetricCubeMeasure n).real
        {x | |MvPolynomial.eval x ((MvPolynomial.finSuccEquiv ℝ n p).coeff k)| ≤ τ} +
      univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) := by
  rw [symmetricCubeMeasure_sublevel_succ]
  have h := polynomial_family_sublevel_step (symmetricCubeMeasure n) (polynomialCoordinateSlice p)
    hd (polynomialCoordinateSlice_degree_le p hp) (polynomialCoordinateSlice_measurable_eval p)
    k (polynomialCoordinateSlice_measurable_coeff p k) hu hτ
  simpa only [polynomialCoordinateSlice_coeff] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricCubeSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem symmetricCubeMeasure_sublevel_one
    (p : MvPolynomial (Fin 1) ℝ) {d : ℕ} (hd : 0 < d) (hp : p.degreeOf 0 ≤ d)
    {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c) (m : Fin 1 →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    (symmetricCubeMeasure 1).real {x | |MvPolynomial.eval x p| ≤ u} ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  have htail : m.tail = 0 := Subsingleton.elim _ _
  have hcoeff : (polynomialCoordinateSlice p (0 : Fin 0 → ℝ)).coeff (m 0) =
      p.coeff m := by
    rw [polynomialCoordinateSlice_coeff, MvPolynomial.eval_zero]
    have h := polynomialCoordinateSlice_selected_coefficient p m
    rw [htail] at h
    exact h
  have hs : MeasurableSet {z : (Fin 0 → ℝ) × ℝ | |(polynomialCoordinateSlice p z.1).eval z.2| ≤ u} :=
    measurableSet_le (continuous_abs.measurable.comp (polynomialCoordinateSlice_measurable_eval p))
      measurable_const
  rw [symmetricCubeMeasure_sublevel_succ, product_measureReal_eq_integral_fiber _ _ _ hs,
    symmetricCubeMeasure_zero, integral_dirac]
  exact symmetricScalarMeasure_sublevel_bound _ hd (polynomialCoordinateSlice_degree_le p hp 0)
    hu hc (m 0) (by simpa only [hcoeff] using hm)

theorem symmetricCube_polynomial_sublevel_bound (d : ℕ) (hd : 0 < d) :
    ∀ (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ),
      (∀ j, p.degreeOf j ≤ d) → ∀ {u c : ℝ}, 0 < u → 0 < c →
      ∀ m : Fin (n + 1) →₀ ℕ, c ≤ |p.coeff m| →
      (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} ≤
        ((n + 1 : ℝ) * univariateSublevelConstant d) *
          (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
  intro n
  induction n with
  | zero =>
    intro p hp u c hu hc m hm
    simpa only [Nat.zero_add, Nat.one_mul, Nat.cast_zero, zero_add, one_mul] using
      symmetricCubeMeasure_sublevel_one p hd (hp 0) hu.le hc m hm
  | succ n ih =>
    intro p hp u c hu hc m hm
    obtain ⟨τ, hτ, hfirst, hsecond⟩ := sublevel_threshold_balance (n + 1) d (by omega) hd hu hc
    let q := (MvPolynomial.finSuccEquiv ℝ (n + 1) p).coeff (m 0)
    have hq : ∀ j, q.degreeOf j ≤ d := polynomialCoordinateSlice_coefficient_degrees p hp (m 0)
    have hqc : c ≤ |q.coeff m.tail| := by
      simpa only [q, polynomialCoordinateSlice_selected_coefficient] using hm
    have hbase := ih q hq hτ hc m.tail hqc
    have hstep := symmetricCubeMeasure_sublevel_step p hd (hp 0) (m 0) hu.le hτ
    apply hstep.trans
    calc
      _ ≤ ((n + 1 : ℝ) * univariateSublevelConstant d) *
          (τ / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) +
          univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) :=
        add_le_add hbase le_rfl
      _ = _ := by rw [hfirst, hsecond]; push_cast; ring

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

theorem exists_coefficient_of_unit_box_value {N d : ℕ}
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ i, p.degreeOf i ≤ d)
    (x : Fin N → ℝ) (hx : ∀ i, |x i| ≤ 1) {v : ℝ} (hv : 0 < v)
    (hval : v ≤ |MvPolynomial.eval x p|) :
    ∃ m : Fin N →₀ ℕ, v / (d + 1 : ℝ) ^ N ≤ |p.coeff m| := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    simp only [h, map_zero, abs_zero] at hval
    linarith
  obtain ⟨m, _hm, hmax⟩ := p.support.exists_max_image
    (fun monomial => |p.coeff monomial|) (MvPolynomial.support_nonempty.mpr hp0)
  refine ⟨m, (div_le_iff₀ (by positivity : 0 < (d + 1 : ℝ) ^ N)).mpr ?_⟩
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ N := by
    exact_mod_cast mvPolynomial_support_card_le p hp
  calc
    v ≤ |MvPolynomial.eval x p| := hval
    _ ≤ ∑ monomial ∈ p.support, |p.coeff monomial| := mvPolynomial_eval_abs_le_sum_coeff p x hx
    _ ≤ ∑ _monomial ∈ p.support, |p.coeff m| := Finset.sum_le_sum hmax
    _ = (p.support.card : ℝ) * |p.coeff m| := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d + 1 : ℝ) ^ N * |p.coeff m| :=
      mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
    _ = _ := mul_comm _ _

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

theorem multivariate_polynomial_sublevel_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (unitMvPolynomialSublevel p u) ≤
      multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have h := symmetricCube_polynomial_sublevel_bound d hd n p hp hu hc m hm
  rw [unitMvPolynomialSublevel, symmetricUnitBox_volume_inter _ _
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet]
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1))
  simpa only [multivariateSublevelConstant, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

theorem boxMvPolynomialSublevel_eq_smul {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) :
    boxMvPolynomialSublevel p R u = R • unitMvPolynomialSublevel (dilateMvPolynomial R p) u := by
  ext x
  constructor
  · intro hx
    have hback : R • (R⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    refine Set.mem_smul_set.mpr ⟨R⁻¹ • x, ⟨?_, ?_⟩, hback⟩
    · apply (symmetricUnitBox_mem N _).mpr
      intro i
      change |R⁻¹ * x i| ≤ 1
      rw [abs_mul, abs_inv, abs_of_pos hR]
      calc
        R⁻¹ * |x i| ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hx.1 i) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    · change |MvPolynomial.eval (R⁻¹ • x) (dilateMvPolynomial R p)| ≤ u
      rw [dilateMvPolynomial_eval, hback]
      exact hx.2
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    refine ⟨?_, ?_⟩
    · intro i
      change |R * y i| ≤ R
      rw [abs_mul, abs_of_pos hR]
      have hi := (symmetricUnitBox_mem N y).mp hy.1 i
      exact (mul_le_mul_of_nonneg_left hi hR.le).trans_eq (mul_one R)
    · rw [← dilateMvPolynomial_eval]
      exact hy.2

theorem boxMvPolynomialSublevel_volume {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) :
    volume.real (boxMvPolynomialSublevel p R u) =
      R ^ N * volume.real (unitMvPolynomialSublevel (dilateMvPolynomial R p) u) := by
  rw [boxMvPolynomialSublevel_eq_smul p hR, measureReal_def, Measure.addHaar_smul_of_nonneg volume hR.le,
    ENNReal.toReal_mul]
  simp [Module.finrank_fintype_fun_eq_card, measureReal_def, hR.le]

theorem boxMvPolynomialSublevel_volume_ne_top {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) : volume (boxMvPolynomialSublevel p R u) ≠ ⊤ := by
  rw [boxMvPolynomialSublevel_eq_smul p hR, Measure.addHaar_smul_of_nonneg volume hR.le]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (unitMvPolynomialSublevel_volume_ne_top _ _)

theorem polynomial_sublevel_box_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    {R u c : ℝ} (hR : 1 ≤ R) (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (boxMvPolynomialSublevel p R u) ≤
      R ^ N * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  rw [boxMvPolynomialSublevel_volume p (zero_lt_one.trans_le hR)]
  have h := multivariate_polynomial_sublevel_bound hN hd (dilateMvPolynomial R p)
    (fun j => dilateMvPolynomial_degree_le R p j (hp j)) hu hc m
    (hm.trans (dilateMvPolynomial_coeff_abs_le hR p m))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans hR) N)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {n N : ℕ}

theorem embeddedMatrixDeterminantPolynomial_derivative
    (e : Fin n × Fin n ↪ Fin N) (x : Fin N → ℝ) (hx : ∀ j, |x j| ≤ 2) :
    ‖fderiv ℝ (fun x => MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e)) x‖ ≤
      embeddedMatrixDeterminantLip n N := by
  have h := polynomial_det_fderiv_norm_le
    (coordinateMatrixPolynomial (fun i j => e (i,j))) x
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)
    (fun a b => by
      simpa only [coordinateMatrixPolynomial, MvPolynomial.eval_X] using hx (e (a,b)))
    (fun a b j => by
      simp only [coordinateMatrixPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> norm_num)
  rw [polynomial_det_eval_function] at h
  simpa only [Fintype.card_fin, mul_one, embeddedMatrixDeterminantLip,
    embeddedMatrixDeterminantPolynomial] using h

theorem embeddedMatrixDeterminantPolynomial_lipschitz
    (e : Fin n × Fin n ↪ Fin N) (x y : Fin N → ℝ)
    (hx : ∀ j, |x j| ≤ 2) (hy : ∀ j, |y j| ≤ 2) :
    |MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) -
      MvPolynomial.eval y (embeddedMatrixDeterminantPolynomial e)| ≤
      embeddedMatrixDeterminantLip n N * ‖x - y‖ := by
  let S : Set (Fin N → ℝ) := Set.Icc (fun _ => -2) (fun _ => 2)
  have hmem (z : Fin N → ℝ) : z ∈ S ↔ ∀ j, |z j| ≤ 2 := by
    simp only [S, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (mvPolynomial_contDiff_eval (embeddedMatrixDeterminantPolynomial e)).differentiable
      (by norm_num) z)
    (fun z hz => embeddedMatrixDeterminantPolynomial_derivative e z ((hmem z).mp hz))
    (convex_Icc _ _) ((hmem y).mpr hy) ((hmem x).mpr hx)
  simpa only [Real.norm_eq_abs] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem samplerTupleIndex_card {D G : Type*} [Fintype D] [Fintype G]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    Fintype.card (SamplerTupleIndex G B h) = Fintype.card G + ∑ d, Fintype.card (B d) * h d := by
  simp only [SamplerTupleIndex, PrincipalTupleIndex, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem independentProductPMF_marginal {I J X : Type*} [Fintype I] [Fintype J]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (e : J → I) (he : Function.Injective e) :
    (independentProductPMF p).map (fun (x : I → X) (j : J) => x (e j)) =
      independentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : I → X) j => x (e j)) _ (by fun_prop)]
  simp only [independentProductPMF, Measure.toPMF_toMeasure]
  exact (finiteProductMarginal_measurePreserving (fun i => (p i).toMeasure) e he).map_eq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSpatialAmplitudeShift
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem rectangularLatticePoint_add_displacement {I : Type*} [Fintype I]
    (a S : I → ℝ) (x v : I → ℤ) :
    rectangularLatticePoint a S (x + v) - rectangularLatticePoint a S x =
      rectangularLatticePoint 0 S v := by
  funext i
  simp only [rectangularLatticePoint, Pi.sub_apply, Pi.add_apply, Pi.zero_apply,
    Int.cast_add]
  ring

theorem normalizedSpatialAmplitude_shift_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (F : (I → ℝ) → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (a S : I → ℝ) (x v : I → ℤ) :
    ‖F (rectangularLatticePoint a S (x + v)) - F (rectangularLatticePoint a S x)‖ ≤
      L * ‖rectangularLatticePoint 0 S v‖ := by
  have h := hF.norm_sub_le (rectangularLatticePoint a S (x + v))
    (rectangularLatticePoint a S x)
  rwa [rectangularLatticePoint_add_displacement] at h

theorem normalizedSpatialAmplitude_shift_le_of_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (F : (I → ℝ) → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (a S : I → ℝ) (x v : I → ℤ)
    {r : ℝ} (hv : ‖rectangularLatticePoint 0 S v‖ ≤ r) :
    ‖F (rectangularLatticePoint a S (x + v)) - F (rectangularLatticePoint a S x)‖ ≤
      L * r :=
  (normalizedSpatialAmplitude_shift_le F hF a S x v).trans
    (mul_le_mul_of_nonneg_left hv L.coe_nonneg)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget
namespace OAI


namespace Erdos3

theorem polynomialSublevelThreshold_root_bound {n m : ℕ} (hn : 0 < n)
    {C scale η : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    (2 * polynomialSublevelThreshold n m C scale η * scale) ^ ((n : ℝ)⁻¹) ≤
      (1 + 2 * C * (m + 1 : ℝ) / η)⁻¹ := by
  let L := 1 + 2 * C * (m + 1 : ℝ) / η
  have hL : 0 < L := by dsimp [L]; positivity
  have hscale : 0 < 1 + scale := by linarith
  have he : 2 * polynomialSublevelThreshold n m C scale η * scale =
      (scale / (1 + scale)) * (L ^ n)⁻¹ := by
    unfold polynomialSublevelThreshold
    dsimp only [L]
    field_simp
  have hfrac : scale / (1 + scale) ≤ 1 := (div_le_one hscale).mpr (by linarith)
  have hsmall : 2 * polynomialSublevelThreshold n m C scale η * scale ≤ (L ^ n)⁻¹ := by
    rw [he]
    exact mul_le_of_le_one_left (by positivity) hfrac
  have hnonneg : 0 ≤ 2 * polynomialSublevelThreshold n m C scale η * scale :=
    mul_nonneg (mul_nonneg (by norm_num) (polynomialSublevelThreshold_pos n m hC hs hη).le) hs
  calc
    _ ≤ ((L ^ n)⁻¹) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hnonneg hsmall (by positivity)
    _ = L⁻¹ := by
      rw [Real.inv_rpow (pow_nonneg hL.le n), Real.pow_rpow_inv_natCast hL.le hn.ne']

theorem polynomialSublevelThreshold_total_bound {n m : ℕ} (hn : 0 < n)
    {C scale η : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    (m : ℝ) * C * (2 * polynomialSublevelThreshold n m C scale η * scale) ^ ((n : ℝ)⁻¹) ≤
      η / 2 := by
  let L := 1 + 2 * C * (m + 1 : ℝ) / η
  have hL : 0 < L := by dsimp [L]; positivity
  have he : (η / 2) * L = η / 2 + C * (m + 1 : ℝ) := by
    dsimp only [L]
    field_simp
  calc
    _ ≤ (m : ℝ) * C * L⁻¹ := mul_le_mul_of_nonneg_left
      (polynomialSublevelThreshold_root_bound hn hC hs hη) (by positivity)
    _ ≤ η / 2 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hL).mpr
      rw [he]
      nlinarith

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3


noncomputable def scalarKernelConditioningConstant (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) : ℝ := (scalarCubeResidueDensityCap I (M * D)) ^ Fintype.card J

noncomputable def scalarKernelAdjustedAccuracy (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℝ := η / scalarKernelConditioningConstant I J M D

noncomputable def scalarKernelThreshold (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℝ :=
  discreteScalarMinorThreshold I J (Fintype.card (J × Option I))
    (scalarKernelAdjustedAccuracy I J M D η)

noncomputable def scalarKernelCutoff (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℕ :=
  jointKernelCutoff (Fintype.card I + 1) (D * ((Fintype.card I + 1) * M))
    (coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))))
    (scalarKernelTailConstant I J) (scalarKernelAdjustedAccuracy I J M D η)
    (scalarKernelThreshold I J M D η)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PMFPointMassMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_bind_toReal {X Y : Type*} (p : PMF X) (q : X → PMF Y) (y : Y) :
    ((p.bind q) y).toReal = ∑' x, (p x).toReal * (q x y).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

noncomputable def uniformResidueSmallPeriodDensity {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J] (A : Matrix I J ℤ) (d period : ℕ) [NeZero d]
    (r : I → ZMod period) : ℝ :=
  (d : ℝ) ^ Fintype.card I *
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z))
        (fun i => ((r i).val : ZMod d))).toReal

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_ae_of_support {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (P : X → Prop)
    (hP : ∀ x, f x ≠ 0 → P x) : ∀ᵐ x ∂realDensityMeasure μ f, P x := by
  apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
  exact Filter.Eventually.of_forall (fun x hx => hP x (fun hz => hx (by simp [hz])))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

include hK hT hγ hlarge in
theorem principalIntervalLength_bounds :
    2 * γ * (K / T) ≤ (principalIntervalLength K T γ : ℝ) ∧
      (principalIntervalLength K T γ : ℝ) ≤ 4 * γ * (K / T) := by
  have hP : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hwidth : 16 ≤ γ * (K / T) := by nlinarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * γ * (K / T) by positivity)
  constructor
  · exact Nat.le_ceil _
  · change (Nat.ceil (2 * γ * (K / T)) : ℝ) ≤ _
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoverBasisResidues
namespace OAI

section

namespace Erdos3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (Γ : AddSubgroup E)

theorem coverLatticeResidueEquiv_mk (d : ℕ) (hd : 0 < d) (x : Γ) :
    coverLatticeResidueEquiv Γ d hd (QuotientAddGroup.mk' _ x) =
      coverLatticePoint Γ d hd x := rfl

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Γ : AddSubgroup E) (b : Basis I ℤ Γ)

omit [Module ℝ E] in
theorem coverLatticeBasisEquiv_mk (d : ℕ) (x : Γ) :
    coverLatticeBasisEquiv Γ b d (QuotientAddGroup.mk' _ x) =
      latticeBasisResidue Γ b d x := rfl

theorem coverKernelBasisEquiv_residue (d : ℕ) (hd : 0 < d) (x : Γ) :
    coverKernelBasisEquiv Γ b d hd (latticeBasisResidue Γ b d x) =
      coverLatticePoint Γ d hd x := by
  rw [← coverLatticeBasisEquiv_mk]
  simp only [coverKernelBasisEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact coverLatticeResidueEquiv_mk Γ d hd x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialThresholdBudget
namespace OAI

section

namespace Erdos3

theorem polynomialSublevelThreshold_inverse_le_exp (n m : ℕ) {C scale η Pc Ps Pe : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η)
    (hPc : 0 ≤ Pc) (hPs : 0 ≤ Ps) (hPe : 0 ≤ Pe)
    (hCb : C ≤ Real.exp Pc) (hsb : scale ≤ Real.exp Ps) (hηb : η⁻¹ ≤ Real.exp Pe) :
    (polynomialSublevelThreshold n m C scale η)⁻¹ ≤
      Real.exp (Ps+2+(n : ℝ)*(Pc+m+Pe+2)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm : (m : ℝ)+1 ≤ Real.exp m := Real.add_one_le_exp _
  have hb : 2*C*((m : ℝ)+1)/η ≤ Real.exp (Pc+m+Pe+1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1*Real.exp Pc*Real.exp m*Real.exp Pe := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbase : 1+2*C*((m : ℝ)+1)/η ≤ Real.exp (Pc+m+Pe+2) := by
    have he : Pc+m+Pe+1+1 = Pc+m+Pe+2 := by ring
    simpa only [he] using one_add_le_exp_succ (by positivity : 0 ≤ Pc+m+Pe+1) hb
  rw [polynomialSublevelThreshold, inv_inv]
  calc
    _ ≤ Real.exp 1*Real.exp (Ps+1)*(Real.exp (Pc+m+Pe+2))^n := by
      gcongr
      exact one_add_le_exp_succ hPs hsb
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def smoothSpatialDisplacementCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) : ℝ :=
  scalarSpatialIndexAllowance I M *
    spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
      (scalarSpatialInverseAllowance I M) 1
      ((Fintype.card (UnselectedColumn s)+Fintype.card (Unit ⊕ I))*probabilityProfileLipschitz) *
    Fintype.card N

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

def CoefficientJetScalar : LayerSamplerAxis I n → Type
  | ⟨_, .inl _⟩ => ℝ
  | ⟨_, .inr _⟩ => ℤ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def integerBooleanSitesFromRows (rows : Finset (Finset α))
    (z : rows → ℤ) : Finset α → ℤ :=
  booleanReconstructionMatrix α *ᵥ (fun t => if ht : t ∈ rows then z ⟨t, ht⟩ else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def rowRestrictedSiteMatrix (rows : Finset (Finset α)) :
    Matrix (Finset α) rows ℤ := fun s t => booleanReconstructionMatrix α s t.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

noncomputable def siteFamilyCoefficient (k : ∀ a, (e a).Term) : ℂ :=
  ∏ a, (e a).coefficient (k a)

noncomputable def siteFamilyFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : A → ℝ) : ℂ :=
  ∏ a, (e a).factor (k a) s (r a) (x a)

noncomputable def siteFamilyEval (y : S → A → ℤ) (x : S → A → ℝ) : ℂ :=
  ∑ k, siteFamilyCoefficient e k * ∏ s,
    siteFamilyFactor e k s (fun a => (y s a : ZMod ((e a).period (k a)))) (x s)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

noncomputable def commonSitePeriod (k : ∀ a, (e a).Term) : ℕ := ∏ a, (e a).period (k a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PatchKernelGridBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_patch_kernel_mesh (d : ℕ) {L p : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hd : (d : ℝ) ≤ p) (hLp : L ≤ Real.exp p) :
    ∃ N : ℕ, 8 ≤ N ∧ ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 10) ∧
      2 * L * (patchKernelGridRadius N : ℝ) ≤ Real.exp (-p) / 2 ∧
      (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 1) * (2 * p + 11)) ∧
      (((2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N : ℝ≥0) : ℝ) ≤
        Real.exp (2 * ((p + 1) * (2 * p + 11)) + 2) := by
  let b := 2 * p + 8
  let N := ⌈Real.exp b⌉₊
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hNlo : Real.exp b ≤ (N : ℝ) := Nat.le_ceil _
  have h8 : (8 : ℝ) ≤ N := by
    have hexp : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    exact (hexp.trans (Real.exp_le_exp.mpr (by dsimp only [b]; linarith))).trans hNlo
  have hN : 8 ≤ N := by exact_mod_cast h8
  have hNhi : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (b + 2) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_nonneg b)).le
    have h1 := Real.one_le_exp hb
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_add]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg b)
    dsimp only [N] at *
    linarith
  have hbound : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 10) := by
    convert hNhi using 1; dsimp only [b]; congr 1; ring
  have herr : L / N ≤ Real.exp (-p - 8) := by
    calc
      L / N ≤ L / Real.exp b := div_le_div_of_nonneg_left hL (Real.exp_pos b) hNlo
      _ ≤ Real.exp p / Real.exp b := div_le_div_of_nonneg_right hLp (Real.exp_nonneg b)
      _ = Real.exp (-p - 8) := by
        rw [← Real.exp_sub]
        congr 1
        dsimp only [b]
        ring
  have h8exp : (2 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hinv : Real.exp (-8 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h8exp
  have haccuracy : 2 * L * (patchKernelGridRadius N : ℝ) ≤ Real.exp (-p) / 2 := by
    have heq : 2 * L * (patchKernelGridRadius N : ℝ) = L / N := by
      simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
        NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
      ring
    rw [heq]
    apply herr.trans
    rw [sub_eq_add_neg, Real.exp_add]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-p))
  let q := (p + 1) * (2 * p + 11)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hq2 : 2 * p + 11 ≤ q := by dsimp only [q]; nlinarith
  have hcount : (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (by positivity) hbound d).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 2 * p + 10)
    dsimp only [q]
    nlinarith
  have hradius : 1 / (patchKernelGridRadius N : ℝ) ≤ Real.exp q := by
    have heq : 1 / (patchKernelGridRadius N : ℝ) = 2 * (N : ℝ) := by
      simp [patchKernelGridRadius]
    rw [heq]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ 2 * ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp (2 * p + 10) := mul_le_mul h2 hbound (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 11) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq2
  exact ⟨N, hN, hbound, haccuracy, hcount,
    metricPartition_constant_le_exp ((N + 1) ^ d) (patchKernelGridRadius N) hq hcount hradius⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PatchTopNetBudget
namespace OAI

section

namespace Erdos3

theorem patchTopNetError_eq_div (d s N : ℕ) (M : ℝ) :
    patchTopNetError d s N M = patchTopNetNumerator d s M / N := by
  unfold patchTopNetError patchTopNetNumerator
  ring

theorem patchTopNetNumerator_le_exp (d s : ℕ) {M p : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hd : (d : ℝ) ≤ p) (hMp : M ≤ Real.exp p) :
    patchTopNetNumerator d s M ≤ Real.exp (patchTopNetNumeratorLog s p) := by
  have hs : (s : ℝ) + 1 ≤ Real.exp s := Real.add_one_le_exp _
  have hd1 : (d : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hM1 : 1 + M ≤ Real.exp (p + 1) := by
    simpa only [zero_add] using add_le_exp_add_one (le_refl (0 : ℝ)) hp
      (by simp : (1 : ℝ) ≤ Real.exp 0) hMp
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    patchTopNetNumerator d s M ≤
        (Real.exp s * (Real.exp p) ^ s) * Real.exp 3 * Real.exp (p + 1) *
          ((Real.exp (p + 1)) ^ (s * d)) ^ s := by
      unfold patchTopNetNumerator
      push_cast
      gcongr
    _ = Real.exp (s + s * p + 3 + (p + 1) + s * ((s * d : ℕ) : ℝ) * (p + 1)) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold patchTopNetNumeratorLog
      push_cast
      have h := mul_le_mul_of_nonneg_left hd
        (by positivity : 0 ≤ (s : ℝ) * s * (p + 1))
      nlinarith

theorem exists_small_patch_top_mesh (d s : ℕ) {M L p : ℝ}
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hd : (d : ℝ) ≤ p) (hMp : M ≤ Real.exp p) (hLp : L ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧
      ((N + 1 : ℕ) : ℝ) ≤ Real.exp (patchTopNetNumeratorLog s p + 2 * p + 6) ∧
      patchTopNetError d s N M < 1 / 4 ∧
      L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
  let b := patchTopNetNumeratorLog s p
  let E := b + 2 * p + 4
  let N := ⌈Real.exp E⌉₊
  have hb : 0 ≤ b := patchTopNetNumeratorLog_nonneg s hp
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hNlo : Real.exp E ≤ (N : ℝ) := Nat.le_ceil _
  have hNr : (0 : ℝ) < N := (Real.exp_pos E).trans_le hNlo
  have hN : 0 < N := by exact_mod_cast hNr
  have hNhi : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (E + 2) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_nonneg E)).le
    have h1 := Real.one_le_exp hE
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_add]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg E)
    dsimp only [N] at *
    linarith
  have herr : patchTopNetError d s N M ≤ Real.exp (-2 * p - 4) := by
    rw [patchTopNetError_eq_div]
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ Real.exp b := patchTopNetNumerator_le_exp d s hp hM hd hMp
      _ = Real.exp (-2 * p - 4) * Real.exp E := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [E]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNlo (Real.exp_nonneg _)
  have hfour : (4 : ℝ) < Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsmall : Real.exp (-4 : ℝ) < 1 / 4 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hfour
  have hsmall' : patchTopNetError d s N M < 1 / 4 :=
    (herr.trans (Real.exp_le_exp.mpr (by linarith))).trans_lt hsmall
  have hloss : L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp p * Real.exp (-2 * p - 4) :=
        (mul_le_mul_of_nonneg_left herr hL).trans
          (mul_le_mul_of_nonneg_right hLp (Real.exp_nonneg _))
      _ = Real.exp (-p) * Real.exp (-4) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (hsmall.le.trans (by norm_num)) (Real.exp_nonneg _)
      _ = _ := by ring
  have he : E + 2 = patchTopNetNumeratorLog s p + 2 * p + 6 := by dsimp only [E, b]; ring
  rw [he] at hNhi
  exact ⟨N, hN, hNhi, hsmall', hloss⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

def allocatedWitnessScaleLog (P Qw : ℝ) : ℝ :=
  allocatedScaleLog P + P ^ 2 * Qw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteRowChartRadiusBudget
namespace OAI

section

namespace Erdos3

theorem finiteRowChartRadius_budget (rows dim : ℕ) {C T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hsmall : R ≤ finiteRowChartRadius rows dim C T) :
    (rows : ℝ) * (C * (((dim : ℝ) + 1) * (T * R))) ≤ 1 / 4 := by
  have hd : 0 < 4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by positivity
  have hr := (le_div_iff₀ hd).mp hsmall
  have hb : (rows : ℝ) * C * ((dim : ℝ) + 1) * T ≤
      ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by gcongr <;> linarith
  have hm := mul_le_mul_of_nonneg_right hb hR
  nlinarith only [hr, hm]

end Erdos3

end

section

namespace Erdos3

theorem finiteRowChartRadius_inv_le_exp (rows dim : ℕ) {C T P : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hr : (rows : ℝ) ≤ Real.exp P) (hd : (dim : ℝ) ≤ Real.exp P)
    (hCP : C ≤ Real.exp P) (hTP : T ≤ Real.exp P) :
    (finiteRowChartRadius rows dim C T)⁻¹ ≤ Real.exp (4 * P + 6) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hunit : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 1 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add _ _).symm
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  simp only [finiteRowChartRadius, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (P + 1) := by
      gcongr
      · exact hadd hr
      · exact hadd hCP
      · exact hadd hd
      · exact hadd hTP
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

noncomputable def normalizedTupleTolerance (X : Type*) [Fintype X] (p E : ℝ) : ℝ :=
  spatialTupleTolerance (Fintype.card X) (Real.exp (p ^ 3 + anisotropicSpatialCapLog p))
    (Real.exp (coefficientErrorVolumeLog p + 4)) (normalizedSpatialShare E / 2)

noncomputable def normalizedTupleNarrowWidth (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ) : ℝ :=
  twoTermErrorWidth (smoothSpatialDisplacementCost N s M) (normalizedTupleTolerance X p E)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockJetScaleBound_four_exp (q h b : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hb : (b : ℝ) ≤ D) :
    blockJetScaleBound q h b 4 ≤ Real.exp (D ^ 2 + 2 * D + 4) := by
  have hbexp : (b : ℝ) ≤ Real.exp D := hb.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : ((q + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ h ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) h hh
  have hpowq := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (q + 1)) hqexp hD h hh
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  unfold blockJetScaleBound
  calc
    _ ≤ Real.exp D * Real.exp D * Real.exp (D * D) * Real.exp 4 := by
      gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def coverSiteCoefficient {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) (k : ∀ a, (e a).Term) : ℂ :=
  (2 : ℂ) ^ Fintype.card S * siteFamilyCoefficient e k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius
namespace OAI

section

namespace Erdos3

theorem finiteRowChartRadius_support_le_inv (rows dim : ℕ) {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) :
    T ≤ (finiteRowChartRadius rows dim C T)⁻¹ := by
  simp only [finiteRowChartRadius, one_div, inv_inv]
  calc
    T ≤ 1 * 1 * 1 * 1 * (T + 1) := by linarith
    _ ≤ 4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by
      gcongr <;> linarith [Nat.cast_nonneg (α := ℝ) rows, Nat.cast_nonneg (α := ℝ) dim]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedSmoothPolynomialSublevel
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothMatrixBlockBudget
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem matrixBlock_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

end Erdos3

end

section

namespace Erdos3

theorem embeddedMatrixDeterminantLip_le_exp (n N : ℕ) :
    embeddedMatrixDeterminantLip n N ≤
      Real.exp ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) := by
  have hN : (N : ℝ) ≤ Real.exp (N : ℝ) := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    linarith [Real.add_one_le_exp (n : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) htwo n
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  unfold embeddedMatrixDeterminantLip
  calc
    _ ≤ Real.exp (N : ℝ) *
        (Real.exp ((n : ℝ) ^ 2) * (Real.exp (n : ℝ) * Real.exp (n : ℝ))) := by
      gcongr
      exact factorial_le_exp_sq n
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothMatrixBlockMesh_width_spec (n N : ℕ) {κ S : ℝ} (hκ : 0 < κ)
    (hS : max (8 * (probabilityProfileLipschitz : ℝ))
      (smoothMatrixBlockMesh n N κ)⁻¹ ≤ S) :
    0 < S ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ S ∧
      1 / S ≤ smoothMatrixBlockMesh n N κ := by
  have hδ := (smoothMatrixBlockMesh_spec n N hκ).1
  have hi : (smoothMatrixBlockMesh n N κ)⁻¹ ≤ S := (le_max_right _ _).trans hS
  have hS0 : 0 < S := (inv_pos.mpr hδ).trans_le hi
  refine ⟨hS0, (le_max_left _ _).trans hS, ?_⟩
  have h := (inv_le_inv₀ hS0 (inv_pos.mpr hδ)).mpr hi
  simpa only [inv_inv, one_div] using h

theorem smoothMatrixBlockMesh_inv_le_exp_of_lip_bound (n N : ℕ)
    {κ P Klog : ℝ} (hκ : 0 < κ) (hP : 0 ≤ P) (hKlog : 0 ≤ Klog)
    (hκP : κ⁻¹ ≤ Real.exp P)
    (hK : embeddedMatrixDeterminantLip n N ≤ Real.exp Klog) :
    (smoothMatrixBlockMesh n N κ)⁻¹ ≤ Real.exp (P + Klog + 1) := by
  have hK1 : embeddedMatrixDeterminantLip n N + 1 ≤ Real.exp (Klog + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hKlog hK
  unfold smoothMatrixBlockMesh
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp (by positivity : 0 ≤ P + Klog + 1)
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (Klog + 1) * Real.exp P :=
        mul_le_mul hK1 hκP (inv_nonneg.mpr hκ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smoothMatrixBlockMesh_inv_le_exp (n N : ℕ) {κ P : ℝ}
    (hκ : 0 < κ) (hP : 0 ≤ P) (hκP : κ⁻¹ ≤ Real.exp P) :
    (smoothMatrixBlockMesh n N κ)⁻¹ ≤
      Real.exp (P + ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) + 1) :=
  smoothMatrixBlockMesh_inv_le_exp_of_lip_bound n N hκ hP (by positivity) hκP
    (embeddedMatrixDeterminantLip_le_exp n N)

end Erdos3

end

section

namespace Erdos3
open scoped Classical

theorem smoothMatrixBlock_threshold_inverse_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (shiftedSmoothSublevelThreshold N n count η)⁻¹ ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget N n count E) := by
  exact polynomialSublevelThreshold_inverse_le_exp (N * n) count
    (shiftedSmoothSublevelConstant_nonneg hN n) (by positivity) hη
    (smoothMatrixBlockConstantLogBudget_nonneg N n) (by positivity) hE
    (shiftedSmoothSublevelConstant_le_exp hN hn)
    (smoothMatrixBlock_scale_le_exp N n) hηb

noncomputable def smoothMatrixBlockWidthLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  smoothMatrixBlockMeshLogBudget N n count E + 8 + probabilityProfileLipschitz

theorem smoothMatrixBlock_actual_mesh_inverse_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (smoothMatrixBlockMesh n N (shiftedSmoothSublevelThreshold N n count η))⁻¹ ≤
      Real.exp (smoothMatrixBlockMeshLogBudget N n count E) :=
  smoothMatrixBlockMesh_inv_le_exp n N (shiftedSmoothSublevelThreshold_pos hN n count hη)
    (smoothMatrixBlockThresholdLogBudget_nonneg N n count hE)
    (smoothMatrixBlock_threshold_inverse_le_exp hN hn count hη hE hηb)

theorem smoothMatrixBlock_actual_width_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    max (8 * (probabilityProfileLipschitz : ℝ))
      (smoothMatrixBlockMesh n N (shiftedSmoothSublevelThreshold N n count η))⁻¹ ≤
      Real.exp (smoothMatrixBlockWidthLogBudget N n count E) := by
  have hB := smoothMatrixBlockMeshLogBudget_nonneg N n count hE
  have hL : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  apply max_le
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    have hLip : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
      linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
    calc
      _ ≤ Real.exp 8 * Real.exp probabilityProfileLipschitz :=
        mul_le_mul h8 hLip hL (Real.exp_pos _).le
      _ = Real.exp (8 + probabilityProfileLipschitz) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold smoothMatrixBlockWidthLogBudget; linarith)
  · apply (smoothMatrixBlock_actual_mesh_inverse_le_exp hN hn count hη hE hηb).trans
    apply Real.exp_le_exp.mpr
    unfold smoothMatrixBlockWidthLogBudget
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem spatialRankPolynomial_degree {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) : (spatialRankPolynomial c).totalDegree ≤ 1 := by
  unfold spatialRankPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  apply (totalDegree_monomial_le _ _).trans
  cases e <;> simp [spatialRankExponent]

theorem spatialRankPolynomial_eq {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) :
    spatialRankPolynomial c = C (c none) + ∑ k, C (c (some k)) * X k := by
  rw [spatialRankPolynomial, Fintype.sum_option]
  simp only [spatialRankExponent, monomial_zero', C_mul_X_eq_monomial]

theorem spatialRankPolynomial_top {K R : Type*} [Fintype K] [CommRing R]
    (base : R) (c : Option K → R) :
    homogeneousComponent 1 (C base + spatialRankPolynomial c) =
      ∑ k, C (c (some k)) * X k := by
  rw [spatialRankPolynomial_eq, map_add, map_add, map_sum]
  have hc (r : R) : homogeneousComponent 1 (C r : MvPolynomial K R) = 0 :=
    homogeneousComponent_eq_zero 1 (C r) (by simp)
  simp only [hc, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [C_mul_X_eq_monomial]
  exact homogeneousComponent_eq_self (isHomogeneous_monomial _ (by simp))

theorem spatialKernelRankSlot_injective {G P A : Type*} (e : A ↪ G) :
    Function.Injective (spatialKernelRankSlot (P := P) e) := by
  intro a b hab
  exact e.injective (Sum.inl.inj (Option.some.inj hab))

theorem spatial_kernel_selected_sum {G P A R : Type*}
    [Fintype A] [CommRing R] (e : A ↪ G) (c : A → R) :
    (∑ a, monomial (spatialRankExponent (spatialKernelRankSlot (P := P) e a)) (c a) :
      MvPolynomial (G ⊕ P) R) = ∑ a, c a • X (.inl (e a)) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_C_mul, C_mul_X_eq_monomial]
  rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K J R : Type*} [Fintype K] [CommRing R]

theorem spatialRankPolynomial_top_congr (f g : Option K → R)
    (hfg : ∀ k, f (some k) = g (some k)) :
    homogeneousComponent 1 (spatialRankPolynomial f) =
      homogeneousComponent 1 (spatialRankPolynomial g) := by
  have hf := spatialRankPolynomial_top (0 : R) f
  have hg := spatialRankPolynomial_top (0 : R) g
  simp only [map_zero, zero_add] at hf hg
  rw [hf, hg]
  apply Finset.sum_congr rfl
  intro k _
  rw [hfg k]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def spatialMatrixBlockSlot {G P X : Type*} (e : Fin 2 × X ↪ G) :
    SpatialMatrixBlockIndex X ↪ Option (G ⊕ P) × X where
  toFun t := (some (.inl (e (t.1,t.2.1))),t.2.2)
  inj' := by
    rintro ⟨b,j,x⟩ ⟨c,k,y⟩ h
    have hx : x = y := congrArg Prod.snd h
    have hbj : (b,j) = (c,k) := e.injective
      (Sum.inl.inj (Option.some.inj (congrArg Prod.fst h)))
    have hb : b = c := congrArg Prod.fst hbj
    have hj : j = k := congrArg Prod.snd hbj
    subst c
    subst k
    subst y
    rfl

noncomputable def spatialMatrixNormalizedEntries {G P X : Type*} (e : Fin 2 × X ↪ G)
    (V : Option (G ⊕ P) × X → ℝ) (z : Option (G ⊕ P) × X → ℤ) :
    SpatialMatrixBlockIndex X → ℝ :=
  fun t => (z (spatialMatrixBlockSlot e t) : ℝ) / V (spatialMatrixBlockSlot e t)

noncomputable def spatialMatrixIndexCenter {G P X : Type*} (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) : SpatialMatrixBlockIndex X → ℝ :=
  fun t => -(residue (spatialMatrixBlockSlot e t) : ℝ) / q t.2.2

noncomputable def spatialMatrixIndexWidth {G P X : Type*} (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (V : Option (G ⊕ P) × X → ℝ) : SpatialMatrixBlockIndex X → ℝ :=
  fun t => V (spatialMatrixBlockSlot e t) / q t.2.2

theorem spatialMatrixIndexWidth_pos {G P X : Type*} (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z) (t : SpatialMatrixBlockIndex X) :
    0 < spatialMatrixIndexWidth e q V t :=
  div_pos (hV _) (by exact_mod_cast hq t.2.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def spatialMatrixBlockEquiv (n : ℕ) :
    SpatialMatrixBlockIndex (Fin n) ≃ Fin (2 * n * n) :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_assoc 2 n n).symm))

def spatialMatrixBlockEntry (n : ℕ) (b : Fin 2) :
    Fin n × Fin n ↪ Fin (2 * n * n) where
  toFun rc := spatialMatrixBlockEquiv n (b, rc.2, rc.1)
  inj' := by
    intro x y h
    have hs := (spatialMatrixBlockEquiv n).injective h
    have hp := congrArg Prod.snd hs
    exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

@[simp] theorem spatialMatrixBlockEntry_apply (n : ℕ) (b : Fin 2) (r c : Fin n) :
    spatialMatrixBlockEntry n b (r,c) = spatialMatrixBlockEquiv n (b,c,r) := rfl

@[simp] theorem spatialMatrixBlockEntry_symm (n : ℕ) (b : Fin 2) (r c : Fin n) :
    (spatialMatrixBlockEquiv n).symm (spatialMatrixBlockEntry n b (r,c)) = (b,c,r) :=
  (spatialMatrixBlockEquiv n).symm_apply_apply _

theorem spatialMatrixBlockEntry_reindex_eval {R : Type*}
    (n : ℕ) (z : SpatialMatrixBlockIndex (Fin n) → R) (b : Fin 2) (r c : Fin n) :
    z ((spatialMatrixBlockEquiv n).symm (spatialMatrixBlockEntry n b (r,c))) = z (b,c,r) := by
  rw [spatialMatrixBlockEntry_symm]

theorem rectangularLatticePoint_reindex {D J : Type*} (e : D → J)
    (a S : J → ℝ) (z : J → ℤ) :
    rectangularLatticePoint (fun d => a (e d)) (fun d => S (e d)) (fun d => z (e d)) =
      fun d => rectangularLatticePoint a S z (e d) := rfl

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def spatialMatrixBlockBad {G P : Type*} {n : ℕ} (e : Fin 2 × Fin n ↪ G)
    (V : Option (G ⊕ P) × Fin n → ℝ) (κ : ℝ)
    (z : Option (G ⊕ P) × Fin n → ℤ) : Prop :=
  ∃ b : Fin 2, |Matrix.det (fun i j : Fin n => spatialMatrixNormalizedEntries e V z (b,j,i))| ≤ κ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedDeterminantCutoff
namespace OAI

section

namespace Erdos3
open scoped NNReal Classical

noncomputable def spatialMatrixBlockCutoff {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ) (x : Option (G ⊕ P) × Fin n → ℝ) : ℝ :=
  normalizedDeterminantCutoff n (fun b i j => spatialMatrixBlockSlot e (b,j,i)) κ x

theorem spatialMatrixBlockCutoff_range {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ) (x : Option (G ⊕ P) × Fin n → ℝ) :
    spatialMatrixBlockCutoff e κ x ∈ Set.Icc (0 : ℝ) 1 := by
  exact normalizedDeterminantCutoff_range n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) κ x

theorem spatialMatrixBlockCutoff_lipschitz {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith (⟨2 / κ, by positivity⟩ * ((n * n.factorial : ℕ) : ℝ≥0))
      (spatialMatrixBlockCutoff (P := P) e κ) := by
  unfold spatialMatrixBlockCutoff
  exact normalizedDeterminantCutoff_lipschitz n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) hκ

theorem spatialMatrixBlockCutoff_indicator_bounds {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (V : Option (G ⊕ P) × Fin n → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (z : Option (G ⊕ P) × Fin n → ℤ)
    (hz : ∀ t, |(z t : ℝ) / V t| ≤ 1) :
    (if spatialMatrixBlockBad e V (κ / 2) z then (1 : ℝ) else 0) ≤
      spatialMatrixBlockCutoff e κ (fun t => (z t : ℝ) / V t) ∧
    spatialMatrixBlockCutoff e κ (fun t => (z t : ℝ) / V t) ≤
      (if spatialMatrixBlockBad e V κ z then (1 : ℝ) else 0) := by
  unfold spatialMatrixBlockBad spatialMatrixBlockCutoff spatialMatrixNormalizedEntries
  have hh := normalizedDeterminantCutoff_indicator_bounds n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) hκ
    (fun t => (z t : ℝ) / V t) (fun _ _ _ => hz _)
  split_ifs at hh ⊢ <;> exact hh

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointExceptionalGainBudget
namespace OAI

section

namespace Erdos3

theorem jointSpatialError_pos (gainLog : ℝ) : 0 < jointSpatialError gainLog := by
  unfold jointSpatialError
  positivity

theorem jointSpatialError_inverse_le_exp (gainLog : ℝ) :
    (jointSpatialError gainLog)⁻¹ ≤ Real.exp (gainLog + 8) := by
  have he : 0 < Real.exp gainLog := Real.exp_pos _
  calc
    (jointSpatialError gainLog)⁻¹ = 128 * Real.exp gainLog := by
      simp [jointSpatialError, Real.exp_neg]
    _ ≤ Real.exp 8 * Real.exp gainLog := by
      exact mul_le_mul_of_nonneg_right (by linarith [jointExceptional_exp_eight]) he.le
    _ = Real.exp (gainLog + 8) := by rw [← Real.exp_add]; congr 1; ring

theorem jointExceptionalGainBudget {gainLog gain P : ℝ}
    (hg : 0 ≤ gainLog) (hP : gainLog + 8 ≤ P)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-(gainLog + 8)) + jointSpatialError gainLog / 2 +
      6 * positiveProjectionAccuracy P ≤ (gain / 4) / 4 := by
  have he : 0 < Real.exp (-gainLog) := Real.exp_pos _
  have hshift : Real.exp (-(gainLog + 8)) ≤ Real.exp (-gainLog) / 256 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (8 : ℝ), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left he.le (by norm_num) jointExceptional_exp_eight
  have hprecision : positiveProjectionAccuracy P ≤ Real.exp (-gainLog) / 256 := by
    apply le_trans _ hshift
    apply Real.exp_le_exp.mpr
    change -(2 * P + 4) ≤ -(gainLog + 8)
    linarith
  unfold jointSpatialError
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTwoBlockEquiv
namespace OAI

section

namespace Erdos3
open scoped Classical

noncomputable def spatialTwoBlockEquiv {X G : Type*} (blocks : Fin 2 × X ↪ G) :
    G ≃ X ⊕ (X ⊕ SpatialKernelRemainder blocks) :=
  ((Equiv.sumCongr (Equiv.ofInjective (twoKernelEmbedding blocks)
      (twoKernelEmbedding blocks).injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (twoKernelEmbedding blocks)))).symm.trans
      (Equiv.sumAssoc X X (SpatialKernelRemainder blocks))

@[simp] theorem spatialTwoBlockEquiv_symm_first {X G : Type*}
    (blocks : Fin 2 × X ↪ G) (x : X) :
    (spatialTwoBlockEquiv blocks).symm (Sum.inl x) = blocks (0, x) := rfl

@[simp] theorem spatialTwoBlockEquiv_symm_second {X G : Type*}
    (blocks : Fin 2 × X ↪ G) (x : X) :
    (spatialTwoBlockEquiv blocks).symm (Sum.inr (Sum.inl x)) = blocks (1, x) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] independentProductPMF

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineFullWitnessSelectedDeckFintype_r52efbd_1 :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance affineFullWitnessSelectedDeckDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_congr_on_tested {Ω : Type*}
    (A : ℕ → ℕ) (bad other : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω)
    (h : ∀ a, 0 < a → a ≤ A p → (bad p a x ↔ other p a x)) :
    largestTestedBadDepth A bad p x = largestTestedBadDepth A other p x := by
  unfold largestTestedBadDepth
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact h a (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2

theorem largestBadPrimeProduct_congr_on_tested {Ω : Type*}
    (S : Finset ℕ) (A : ℕ → ℕ) (bad other : ℕ → ℕ → Ω → Prop) (x : Ω)
    (h : ∀ p ∈ S, ∀ a, 0 < a → a ≤ A p → (bad p a x ↔ other p a x)) :
    (∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) =
      ∏ p ∈ S, p ^ largestTestedBadDepth A other p x := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [largestTestedBadDepth_congr_on_tested A bad other p x (h p hp)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem largestTestedBadDepth_measurable {Ω : Type*} [MeasurableSpace Ω]
    (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop) (p : ℕ)
    (hbad : ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x}) :
    Measurable (largestTestedBadDepth A bad p) := by
  unfold largestTestedBadDepth
  have h := finite_nat_sup_measurable (Finset.Icc 1 (A p))
    (fun a x => if bad p a x then a else 0)
    (fun a ha => Measurable.ite (hbad a ha) measurable_const measurable_const)
  convert h using 1
  funext x
  rw [Finset.sup_ite]
  simp only [show (0 : ℕ) = ⊥ from rfl, Finset.sup_bot, sup_bot_eq]
  rfl

theorem largestBadPrimeProduct_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hbad : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x}) :
    Measurable (fun x => ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x) := by
  apply Finset.measurable_prod
  intro p hp
  exact (measurable_of_countable (fun a : ℕ => p ^ a)).comp
    (largestTestedBadDepth_measurable A bad p (hbad p hp))

theorem largestBadPrimeProduct_tail_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hbad : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x})
    (cutoff : ℕ) :
    MeasurableSet {x | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x} :=
  measurableSet_lt measurable_const (largestBadPrimeProduct_measurable P A bad hbad)

end Erdos3

end

end OAI
end


