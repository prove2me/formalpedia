-- Prove2me | Definitions.Def_OAIErdos3B1382
-- name    : OAIErdos3B1382
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T04:24:57.717443+00:00
-- url     : https://prove2.me/theorems/c64ebc20-c9fc-4e40-bf5d-ffe78b60b158
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1383 of 1395
-- statement:
--   Definitions bundle 1383 of 1395 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1381`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1383 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.complexMean_commute`, `OAI.Erdos3.FiniteProbabilityWeights.pi_uniform_complexMean`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenCoefficientSource_probability`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetDensity_law`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetDensity_le_card`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetDensity_nonneg`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetDensity_probability`, `OAI.Erdos3.affineProductProfile_measurable_center`, `OAI.Erdos3.booleanConstantJet_measurable_comp`, `OAI.Erdos3.centeredFiniteMarginal_sampledSliceSeminorm`, `OAI.Erdos3.conditionalRegularizedDensity_measurable`, `OAI.Erdos3.containedProgressionTupleLaw_mean`, `OAI.Erdos3.containedProgressionTupleMap_normalized`, `OAI.Erdos3.density_bounded_complex_test_error`, `OAI.Erdos3.exists_center_of_sampledSliceSeminorm`, `OAI.Erdos3.integerMatrixImagePMF_law`, `OAI.Erdos3.integrable_snd_probability`, `OAI.Erdos3.integral_norm_le_centeredFiniteMarginal`, `OAI.Erdos3.integral_selected_slice_residual_le`, `OAI.Erdos3.integral_snd_probability`, `OAI.Erdos3.pmf_realDensity_uniform`, `OAI.Erdos3.polynomialPerturbationScale_inverse_le_exp`, `OAI.Erdos3.polynomialPerturbationScale_spec`, `OAI.Erdos3.quantitativeBadPrimeRadius_error`, `OAI.Erdos3.regularizedImageDensity_bounds`, `OAI.Erdos3.regularizedImageDensity_joint_measurable`, `OAI.Erdos3.regularizedImageDensity_probability`, `OAI.Erdos3.slicedPrincipalBoundaryRadius_spec`, `OAI.Erdos3.slicedPrincipalComparisonBudget_nonneg`, `OAI.Erdos3.smoothSpatialDisplacementCost_le_exp`, `OAI.Erdos3.smoothSpatialDisplacementCost_nonneg`, `OAI.Erdos3.spatialKernelErrorConstant_le_exp`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1374
import Definitions.Def_OAIErdos3B1381

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineProductProfile_measurable_center {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (c x : Ω → I → ℝ) (w : I → ℝ)
    (hc : ∀ i, Measurable (fun a => c a i)) (hx : ∀ i, Measurable (fun a => x a i)) :
    Measurable (fun a => affineProductProfile (c a) w (x a)) := by
  unfold affineProductProfile affineProbabilityProfile
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.mul (smoothProbabilityProfile_contDiff.continuous.measurable.comp
    (((hx i).sub (hc i)).div_const (w i)))

theorem regularizedImageDensity_joint_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : Ω × (I → ℝ) => affineProductProfile (U p.1) (fun _ => (δ : ℝ)) p.2) :=
  affineProductProfile_measurable_center _ _ _
    (fun i => (measurable_pi_apply i).comp (hU.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem regularizedImageDensity_probability {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, 0 ≤ regularizedImageDensity μ U δ x) ∧ Integrable (regularizedImageDensity μ U δ) ∧
      (∫ x, regularizedImageDensity μ U δ x) = 1 := by
  apply densityMixture_probability_density μ volume _ (regularizedImageDensity_joint_measurable U hU δ)
  exact Filter.Eventually.of_forall (fun a =>
    ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩)

theorem regularizedImageDensity_bounds {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, regularizedImageDensity μ U δ x ∈ Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card I : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip I δ) (regularizedImageDensity μ U δ) := by
  apply densityMixture_uniform_bound μ _ (δ⁻¹ ^ Fintype.card I) (affineProductProfileLip I δ)
  · intro x
    exact ((regularizedImageDensity_joint_measurable U hU δ).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro a
    refine ⟨?_, affineProductProfile_lipschitz (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl)⟩
    intro x
    have hn := affineProductProfile_nonneg (U a) (fun _ => (δ : ℝ)) (fun _ => hδ) x
    have hc := affineProductProfile_cap (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl) x
    rw [Real.norm_of_nonneg hn] at hc
    exact ⟨hn, hc⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_measurable {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (ν : Measure X) [SFinite ν] (U : W × X → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : W × (I → ℝ) => regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2) := by
  have hm := affineProductProfile_measurable_center
    (fun p : (W × (I → ℝ)) × X => U (p.1.1, p.2)) (fun p => p.1.2) (fun _ => (δ : ℝ))
    (fun i => (measurable_pi_apply i).comp (hU.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalComparisonBudget_nonneg (N m : ℕ) {C A r κ : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) :
    0 ≤ slicedPrincipalComparisonBudget N m C A r κ := by
  unfold slicedPrincipalComparisonBudget
  positivity

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalBoundaryRadius_spec (N : ℕ) {η : ℝ} (hη : 0 < η) :
    let r := slicedPrincipalBoundaryRadius N η
    0 < r ∧ r ≤ 1 / 4 ∧ 8 * N * r ≤ η / 2 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := by dsimp [r, slicedPrincipalBoundaryRadius]; positivity
  have hr1 : r ≤ 1 / 4 := min_le_left _ _
  have he : r ≤ η / (16 * ((N : ℝ) + 1)) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((N : ℝ) + 1))).mp he
  refine ⟨hr, hr1, ?_⟩
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleLowerBound
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_inverse_le_exp {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hMP : M ≤ Real.exp P) (hQP : Q ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ Real.exp (6*P+8) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ)^4 := by norm_num
      _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hm1 : (m : ℝ)+1 ≤ Real.exp (P+1) := by
    simpa only [add_comm] using one_add_le_exp_succ hP hm
  have hK1 := one_add_le_exp_succ hP hKP
  have hM1 := one_add_le_exp_succ hP hMP
  have hQ1 := one_add_le_exp_succ hP hQP
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 6*P+8)
  · apply inv_min_le_of_inv_le
    · calc
        (1/(2*(1+K)*(1+M)))⁻¹ = 2*(1+K)*(1+M) := by simp
        _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp (P+1) := by gcongr
        _ = Real.exp (2*P+3) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc
        (τ^2/(16*((m : ℝ)+1)^2*(1+Q)*(1+M)))⁻¹ =
            16*((m : ℝ)+1)^2*(1+Q)*(1+M)*(τ⁻¹)^2 := by
              rw [inv_div, div_eq_mul_inv, inv_pow]
        _ ≤ Real.exp 4*(Real.exp (P+1))^2*Real.exp (P+1)*Real.exp (P+1)*(Real.exp P)^2 := by
          gcongr
        _ = _ := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantJetPostprocessing
namespace OAI

section

namespace Erdos3

theorem booleanConstantJet_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α)
    (constant : Ω → D → ℝ) (hc : ∀ d, Measurable (fun a => constant a d)) :
    Measurable (fun a => booleanConstantJet sets (constant a)) := by
  apply measurable_pi_iff.mpr
  intro o
  by_cases hs : sets o.1 o.2 = ∅
  · simpa only [booleanConstantJet, hs, ite_true] using hc o.1
  · simpa only [booleanConstantJet, hs, ite_false] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem pmf_realDensity_uniform {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    p.toMeasure = realDensityMeasure (PMF.uniformOfFintype X).toMeasure
      (fun x => (Fintype.card X : ℝ) * (p x).toReal) := by
  apply Measure.ext_of_singleton
  intro x
  rw [realDensityMeasure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  rw [p.toMeasure_apply_singleton x (measurableSet_singleton x),
    (PMF.uniformOfFintype X).toMeasure_apply_singleton x (measurableSet_singleton x)]
  simp only [PMF.uniformOfFintype_apply,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_toReal (p.apply_ne_top x)]
  have hc : (Fintype.card X : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_right_comm, ENNReal.mul_inv_cancel hc (by simp), one_mul]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem coefficientDeckJetDensity_nonneg (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : 0 ≤ coefficientDeckJetDensity root A rows d r :=
  mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

theorem coefficientDeckJetDensity_le_card (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root A rows d r ≤ Fintype.card (∀ j, O j → B j → ZMod d) := by
  let p := (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
    (coefficientDeckJetMap root A rows d)
  have hp : (p r).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one r)
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans_eq (mul_one _)

theorem coefficientDeckJetDensity_law (d : ℕ) [NeZero d] :
    ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)).toMeasure =
    realDensityMeasure (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d) :=
  pmf_realDensity_uniform _

theorem coefficientDeckJetDensity_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (realDensityMeasure
      (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d)) := by
  rw [← coefficientDeckJetDensity_law]
  infer_instance

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem integrable_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    Integrable (fun x : Z × X => f x.2) (μ.prod ν) := by
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Z => (1 : ℝ)) μ).mul_prod hf

theorem integral_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    (∫ x : Z × X, f x.2 ∂μ.prod ν) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (integrable_snd_probability μ ν f hf)]
  simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem density_bounded_complex_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(∫ x, (f x : ℂ) * φ x ∂μ) - ∫ x, (g x : ℂ) * φ x ∂μ‖ ≤
      B * ∫ x, |f x - g x| ∂μ := by
  have hfi : Integrable (fun x => (f x : ℂ) * φ x) μ :=
    hf.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgi : Integrable (fun x => (g x : ℂ) * φ x) μ :=
    hg.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ x, B * |f x - g x| ∂μ := by
      apply integral_mono (hfi.sub hgi).norm ((hf.sub hg).abs.const_mul B)
      intro x
      change ‖(f x : ℂ) * φ x - (g x : ℂ) * φ x‖ ≤ B * |f x - g x|
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x - g x))
    _ = _ := integral_const_mul _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {I Z O J : Type*} [Fintype I] [Fintype Z]
variable [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_law (p : J → PMF ℤ) :
    (Measure.pi (fun j => (p j).toMeasure)).map (fun z => A *ᵥ z) =
      (integerMatrixImagePMF A p).toMeasure := by
  rw [integerMatrixImagePMF, ← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  congr 1
  exact (Measure.toPMF_toMeasure _).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {I Q : Type*} [Fintype I] [Fintype Q] {Y : I → Type*} {X : Q → Type*}
variable [∀ i, MeasurableSpace (Y i)] [∀ q, Countable (X q)]
variable [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical Matrix

namespace VectorPolynomial
variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O O' B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] [∀ j, Fintype (B j)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O I : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]
variable [∀ j, DecidableEq (O j)]
variable {n : Fin m → ℕ} (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m : ℕ}
variable {I O : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (O j)]
variable [∀ j, DecidableEq (O j)] {n : Fin m → ℕ}
variable (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val + 1)) ℤ)
variable (s : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hA : ∀ j, ((A j).submatrix id (s j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem quantitativeBadPrimeRadius_error {E : ℝ} (hE : 0 ≤ E) (Q : ℕ) (hQ : 1 ≤ Q) :
    let R := quantitativeBadPrimeRadius E
    0 < Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
    2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ Real.exp (-E) := by
  dsimp only
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))) =
      Real.exp (-E) / 2 := by field_simp
  rw [heq]
  linarith [(quantitativeBadPrimeRadius_bounds hE).2.2]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

theorem centeredFiniteMarginal_sampledSliceSeminorm
    {T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (f : X → ℂ) :
    sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests f =
      ∫ c, sampledSliceSeminorm (law c) physical slices tests f ∂μ :=
  centeredFiniteMarginal_mean μ law hweight _

theorem exists_center_of_sampledSliceSeminorm
    {T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (f : X → ℂ)
    {α : ℝ} (hα : 0 < α)
    (hlarge : α ≤ sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical slices tests f) :
    ∃ c, α / 2 ≤ sampledSliceSeminorm (law c) physical slices tests f := by
  by_contra! hn
  have hi : Integrable (fun c => sampledSliceSeminorm (law c) physical slices tests f) μ :=
    centeredFinite_mean_integrable μ law hweight _ (fun _ => integrable_const _)
  rw [centeredFiniteMarginal_sampledSliceSeminorm] at hlarge
  have hle := integral_mono hi (integrable_const (α / 2)) (fun c => (hn c).le)
  simp only [integral_const, probReal_univ, one_smul] at hle
  linarith

section Joint
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem integral_norm_le_centeredFiniteMarginal
    (f : C × Ω → ℂ) (hf : Measurable f) (envelope : Ω → ℝ)
    (hbound : ∀ c z, ‖f (c, z)‖ ≤ envelope z) :
    Integrable f (centeredFiniteProbabilityMeasure μ law) ∧
      (∫ y, ‖f y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤
        (centeredFiniteMarginal μ law hweight).mean envelope := by
  classical
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have henv (y : C × Ω) : ‖envelope y.2‖ ≤ ∑ z, ‖envelope z‖ :=
    Finset.single_le_sum (fun z _ => norm_nonneg _) (Finset.mem_univ y.2)
  have henvMeas : Measurable (fun y : C × Ω => envelope y.2) :=
    measurable_from_prod_countable_left
      (fun z => (measurable_const : Measurable (fun _ : C => envelope z)))
  have hi : Integrable f (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall (fun y =>
      (hbound y.1 y.2).trans ((le_abs_self _).trans (henv y))))
  have hei : Integrable (fun y : C × Ω => envelope y.2)
      (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound henvMeas.aestronglyMeasurable _ (Filter.Eventually.of_forall henv)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, envelope y.2 ∂centeredFiniteProbabilityMeasure μ law :=
      integral_mono hi.norm hei (fun y => hbound y.1 y.2)
    _ = ∫ c, (law c).mean envelope ∂μ :=
      centeredFiniteProbabilityMeasure_integral μ law hweight _ hei
    _ = _ := (centeredFiniteMarginal_mean μ law hweight envelope).symm

theorem integral_selected_slice_residual_le
    {T X : Type*} [Fintype T] [Nonempty T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : X → ℂ) (err : C × Ω → ℂ) (hmeas : Measurable err)
    (hselected : ∀ c z, ∃ j, err (c, z) =
      𝔼 t ∈ slices z j, signal (physical z t) * tests z j t) :
    Integrable err (centeredFiniteProbabilityMeasure μ law) ∧
      (∫ y, ‖err y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
          physical slices tests signal := by
  let W := fun z j => normalizedSliceTest (slices z j) (tests z j)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ K :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (htests z j) t
  apply integral_norm_le_centeredFiniteMarginal μ law hweight err hmeas
    (fun z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal)
  intro c z
  obtain ⟨j, hj⟩ := hselected c z
  rw [hj, Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
  have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
      ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ := by
    change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
    rw [normalizedSliceTest_mean _ (hslices z j)]
  rw [← he]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j

end Joint
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

include hweight

section Site

variable {T X : Type*} [Fintype T] [Nonempty T] [Fintype X]
variable (physical : Ω → T → X)

end Site

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.pi_uniform_complexMean
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : (∀ i, A i) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (A i))).complexMean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, A i, ((∏ i, (Fintype.card (A i) : ℝ)⁻¹ : ℝ) : ℂ) * f x) = _
  have hcard : (∏ i, (Fintype.card (A i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, A i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_commute {I J : Type*} [Fintype I] [Fintype J]
    (p : FiniteProbabilityWeights I) (q : FiniteProbabilityWeights J) (f : I → J → ℂ) :
    p.complexMean (fun i => q.complexMean (f i)) =
      q.complexMean (fun j => p.complexMean (fun i => f i j)) := by
  simp only [complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

omit [DecidableEq D] [∀ d, DecidableEq (B d)] in
theorem containedProgressionTupleMap_normalized [DecidableEq D] [∀ d, DecidableEq (B d)]
    (v : PrincipalIntegerTuples B h α H)
    (hv : ∀ j, IntegerScalarCube (H j) (fun i => (v j i : ℤ))) :
    principalTupleNormalized L (containedProgressionTupleMap B h L H step c hL hsubset v) =
      principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j) := by
  funext a
  simp only [principalTupleNormalized, principalTupleIntegers, containedProgressionTupleMap,
    containedProgressionCubeMap_value _ _ _ _ _ _ _ _ (hv _), principalTupleFlatten_apply,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero]

theorem containedProgressionTupleLaw_mean
    (p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α H))
    (hp : ∀ v, p.weight v ≠ 0 → ∀ j, IntegerScalarCube (H j) (fun i => (v j i : ℤ)))
    (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (p.fiberLaw (containedProgressionTupleMap B h L H step c hL hsubset)).mean
        (fun v => f (principalTupleNormalized L v)) =
      p.mean (fun v => f (principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j))) := by
  rw [p.fiberLaw_mean]
  apply p.mean_congr_on_support
  intro v hv
  rw [containedProgressionTupleMap_normalized B h L H step c hL hsubset v (hp v hv)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α] [DecidableEq α]
variable (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
variable (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ) (L k : ℤ))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)


section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


theorem allocatedFrozenCoefficientSource_probability :
    IsProbabilityMeasure (allocatedFrozenCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end


