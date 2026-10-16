-- Prove2me | Definitions.Def_OAIErdos3B079
-- name    : OAIErdos3B079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T00:44:00.318969+00:00
-- url     : https://prove2.me/theorems/417cc7d1-1a09-4236-94cc-d07f3ddb4967
-- title:
--   OpenAI Erdős-3 split, definitions bundle 80 of 1379
-- statement:
--   Definitions bundle 80 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B078`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 80 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.forecastAugmented_envelope_le_on_good`, `OAI.Erdos3.FiniteProbabilityWeights.forecastAugmented_envelope_tail_le`, `OAI.Erdos3.VectorPolynomial.ActualForecastData`, `OAI.Erdos3.VectorPolynomial.ActualForecastData.zero`, `OAI.Erdos3.VectorPolynomial.ActualForecastData.zero_centerConstant`, `OAI.Erdos3.VectorPolynomial.ActualForecastData.zero_target`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.refilteredMiddle`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.refiltered_mark_on_slice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_finite_freezing_refinement_of_dictionary`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_frozen_refinement_of_local_slices`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredFrozenObservable`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredFrozenObservable_eq_localFrozen`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredFrozenObservable_recovery_of_coveredDiagram`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredFrozenScore`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredFrozen_mark_on_slice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredLocalCoordinates`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredLocalCoordinates_value`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredQuotientObservable`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredScoredAssembly_mark_on_slice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.topQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.topQuotient_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.topQuotient_value`, `OAI.Erdos3.VectorPolynomial.actualForecastOptionFamily`, `OAI.Erdos3.VectorPolynomial.actualForecastOptionFamily_none_centerConstant`, `OAI.Erdos3.VectorPolynomial.actualForecastOptionFamily_none_target`, `OAI.Erdos3.VectorPolynomial.actualForecastOptionFamily_some`, `OAI.Erdos3.VectorPolynomial.centeredForecastTwist_mem_common_family`, `OAI.Erdos3.VectorPolynomial.centeredForecastTwist_sum_eq`, `OAI.Erdos3.VectorPolynomial.forecastFiniteTwists_common_family`, `OAI.Erdos3.VectorPolynomial.forecastNormalizedTwist_mem_fixed_native_family`, `OAI.Erdos3.forecastAugmentedUnitThreshold`, `OAI.Erdos3.forecastAugmentedUnitThreshold_atom_gain`, `OAI.Erdos3.forecastAugmentedUnitThreshold_bounds`, `OAI.Erdos3.forecastAugmented_approximation_precision`, `OAI.Erdos3.forecastAugmented_model_error`, `OAI.Erdos3.forecastAugmented_model_parameters`, `OAI.Erdos3.forecastAugmented_model_size`, `OAI.Erdos3.forecastCorrelationLinearMap`, `OAI.Erdos3.forecastFamilySeminorm`, `OAI.Erdos3.forecastFamilySeminorm_apply`, `OAI.Erdos3.forecastFamilySeminorm_bddAbove`, `OAI.Erdos3.forecastFamilySeminorm_le`, `OAI.Erdos3.forecastSingleSeminorm`, `OAI.Erdos3.forecastSingleSeminorm_le`, `OAI.Erdos3.forecast_correlation_le_family`, `OAI.Erdos3.forecast_detector_of_atom_approximation`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B076
import Definitions.Def_OAIErdos3B077
import Definitions.Def_OAIErdos3B153

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

theorem forecastAugmented_envelope_tail_le
    (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    {K F C ε : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F) (hC : 1 ≤ C)
    (hexcess : p.excessMass q C ≤ ε) :
    p.mean (fun x => if x ∈ Finset.univ.filter
      (fun y => p.relativeDensity q y ≤ 2 * C)
      then 0 else K * p.relativeDensity q x + F) ≤ 2 * (K + F) * ε := by
  let G := Finset.univ.filter (fun x => p.relativeDensity q x ≤ 2 * C)
  have htail : p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) ≤ 2 * ε := by
    rw [p.relativeDensity_tail_mass q hp]
    exact mass_above_double_cap_le_of_excess p q hexcess
  have hpoint (x : Ω) :
      (if x ∈ G then 0 else K * p.relativeDensity q x + F) ≤
        (K + F) * (if x ∈ G then 0 else p.relativeDensity q x) := by
    by_cases hx : x ∈ G
    · simp only [hx, ↓reduceIte, mul_zero, le_refl]
    · have hbad : 2 * C < p.relativeDensity q x := by
        simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hx
      simp only [hx, ↓reduceIte]
      have hFscale := mul_le_mul_of_nonneg_left (show 1 ≤ p.relativeDensity q x by linarith) hF
      nlinarith
  calc
    _ ≤ p.mean (fun x => (K + F) * (if x ∈ G then 0 else p.relativeDensity q x)) :=
      p.mean_mono hpoint
    _ = (K + F) * p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) := by
      unfold mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ (K + F) * (2 * ε) := mul_le_mul_of_nonneg_left htail (add_nonneg hK hF)
    _ = 2 * (K + F) * ε := by ring

theorem forecastAugmented_envelope_le_on_good
    (p q : FiniteProbabilityWeights Ω) {K F C : ℝ} (hK : 0 ≤ K)
    (x : Ω) (hx : x ∈ Finset.univ.filter (fun y => p.relativeDensity q y ≤ 2 * C)) :
    K * p.relativeDensity q x + F ≤ 2 * K * C + F := by
  have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 hK
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def forecastCorrelationLinearMap {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : X → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := r.correlation g forecast
  map_add' g h := by
    simp [FiniteProbabilityWeights.correlation, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
  map_smul' a g := by
    simp only [FiniteProbabilityWeights.correlation, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

noncomputable def forecastSingleSeminorm {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : X → ℂ) : Seminorm ℂ (X → ℂ) :=
  (normSeminorm ℂ ℂ).comp (forecastCorrelationLinearMap r forecast)

theorem forecastSingleSeminorm_le {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast g : X → ℂ) {cap : ℝ}
    (hcap : ∀ x, ‖forecast x‖ ≤ cap) :
    forecastSingleSeminorm r forecast g ≤ cap * r.mean (fun x => ‖g x‖) := by
  change ‖r.correlation g forecast‖ ≤ _
  unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.mean
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (r.nonneg x)]
  calc
    r.weight x * (‖g x‖ * ‖forecast x‖) ≤ r.weight x * (‖g x‖ * cap) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcap x) (norm_nonneg _))
        (r.nonneg x)
    _ = cap * (r.weight x * ‖g x‖) := by ring

noncomputable def forecastFamilySeminorm {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) : Seminorm ℂ (X → ℂ) :=
  ⨆ f, forecastSingleSeminorm r (forecast f)

theorem forecastFamilySeminorm_bddAbove {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) :
    BddAbove (Set.range (fun f => forecastSingleSeminorm r (forecast f))) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro g
  refine ⟨cap * r.mean (fun x => ‖g x‖), ?_⟩
  rintro _ ⟨f, rfl⟩
  exact forecastSingleSeminorm_le r (forecast f) g (hcap f)

theorem forecastFamilySeminorm_apply {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) :
    forecastFamilySeminorm r forecast g = ⨆ f, ‖r.correlation g (forecast f)‖ := by
  rw [forecastFamilySeminorm, Seminorm.iSup_apply
    (forecastFamilySeminorm_bddAbove r forecast hcap)]
  rfl

theorem forecastFamilySeminorm_le {X F : Type*} [Fintype X] [Nonempty F]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) :
    forecastFamilySeminorm r forecast g ≤ cap * r.mean (fun x => ‖g x‖) := by
  rw [forecastFamilySeminorm_apply r forecast hcap]
  exact ciSup_le (fun f => forecastSingleSeminorm_le r (forecast f) g (hcap f))

theorem forecast_correlation_le_family {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) (f : F) :
    ‖r.correlation g (forecast f)‖ ≤ forecastFamilySeminorm r forecast g := by
  rw [forecastFamilySeminorm_apply r forecast hcap]
  have hb : BddAbove (Set.range (fun i => ‖r.correlation g (forecast i)‖)) := by
    refine ⟨cap * r.mean (fun x => ‖g x‖), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact forecastSingleSeminorm_le r (forecast i) g (hcap i)
  exact le_ciSup hb f

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem forecast_detector_of_atom_approximation
    {X Term : Type*} [Fintype X] [Fintype Term]
    (r : FiniteProbabilityWeights X) (forecast g : X → ℂ)
    (coefficient : Term → ℂ) (atom : Term → X → ℂ)
    {atoms : Set (X → ℂ)} {α M beta : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hatom : ∀ i, atom i ∈ atoms)
    (happrox : ∀ x, ‖forecast x - ∑ i, coefficient i * atom i x‖ ≤ α / 8)
    (hmass : (∑ i, ‖coefficient i‖) ≤ M)
    (hbeta : beta ≤ α / (8 * (M + 1)))
    (hlarge : α / 2 ≤ ‖r.correlation g forecast‖) :
    ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
  have hconj (x : X) :
      ‖star (forecast x) - ∑ i, star (coefficient i) * star (atom i x)‖ ≤
        (α / 2) / (2 * ((1 : ℝ) + 1)) := by
    have h := happrox x
    rw [← norm_star] at h
    simpa only [star_sub, star_sum, star_mul, mul_comm (star (atom _ _)), div_div, mul_assoc,
      show (2 : ℝ) * (2 * (1 + 1)) = 8 by norm_num] using h
  have hmass' : (∑ i, ‖star (coefficient i)‖) ≤ M := by
    simpa only [norm_star] using hmass
  obtain ⟨i, hi⟩ := exists_forecast_detecting_atom r (fun x => star (forecast x)) g
    (fun i => star (coefficient i)) (fun i x => star (atom i x))
    (half_pos hα) zero_le_one hM hg hconj hmass' hlarge
  change (α / 2) / (4 * (M + 1)) ≤ ‖r.correlation g (atom i)‖ at hi
  refine ⟨atom i, hatom i, hbeta.trans ?_⟩
  simpa only [div_div, show (2 : ℝ) * (4 * (M + 1)) = 8 * (M + 1) by ring] using hi

end Erdos3

end

section

namespace Erdos3

noncomputable def forecastAugmentedUnitThreshold (u p K C Fcap : ℝ) : ℝ :=
  (Real.exp (-(u + 3)) / Real.exp p ^ 2) /
    max 1 ((2 * K * C + Fcap) / Real.exp (-(u + 3)))

theorem forecastAugmentedUnitThreshold_bounds {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 < forecastAugmentedUnitThreshold u p K C Fcap ∧
      forecastAugmentedUnitThreshold u p K C Fcap ≤ 1 ∧
      Real.exp (-(2 * u + 4 * p + 8)) ≤ forecastAugmentedUnitThreshold u p K C Fcap := by
  let τ := Real.exp (-(u + 3))
  let D := max 1 ((2 * K * C + Fcap) / τ)
  have hτ : 0 < τ := Real.exp_pos _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hτ1 : τ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hep : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hnum : τ / Real.exp p ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos p))).mpr (by nlinarith)
  have hKC : K * C ≤ Real.exp p * Real.exp p := mul_le_mul hKp hCp hC (Real.exp_nonneg p)
  have hbound : D ≤ 3 * Real.exp (2 * p + u + 3) := by
    apply max_le
    · have he := Real.one_le_exp (show 0 ≤ 2 * p + u + 3 by positivity)
      linarith
    · calc
        _ ≤ (3 * (Real.exp p * Real.exp p)) / τ := by
          apply div_le_div_of_nonneg_right _ hτ.le
          nlinarith
        _ = 3 * Real.exp (2 * p + u + 3) := by
          dsimp only [τ]
          rw [show 2 * p + u + 3 = p + p + (u + 3) by ring]
          simp only [Real.exp_add, Real.exp_neg, div_eq_mul_inv, inv_inv]
          ring
  refine ⟨div_pos (div_pos hτ (sq_pos_of_pos (Real.exp_pos p))) hD,
    (div_le_iff₀ hD).mpr (by nlinarith [le_max_left 1 ((2 * K * C + Fcap) / τ)]), ?_⟩
  change _ ≤ (τ / Real.exp p ^ 2) / D
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 6)) / 3 := by
      rw [show -(2 * u + 4 * p + 8) = -(2 * u + 4 * p + 6) - 2 by ring, Real.exp_sub]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)])
    _ = (τ / Real.exp p ^ 2) / (3 * Real.exp (2 * p + u + 3)) := by
      dsimp only [τ]
      rw [show -(2 * u + 4 * p + 6) = -(u + 3) - (p + p) - (2 * p + u + 3) by ring,
        Real.exp_sub, Real.exp_sub, Real.exp_add]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD hbound

theorem forecastAugmentedUnitThreshold_atom_gain {u p q K C Fcap M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p)
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) :
    Real.exp (-(2 * u + 4 * p + q + 20)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / (8 * (M + 1)) := by
  have hα := (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2
  have hden : 8 * (M + 1) ≤ Real.exp (q + 12) := by
    rw [Real.exp_add]
    have heq := Real.one_le_exp hq
    have he12 : (16 : ℝ) ≤ Real.exp 12 := by
      have h6 := Real.add_one_le_exp (6 : ℝ)
      have h12 : Real.exp (12 : ℝ) = Real.exp 6 * Real.exp 6 := by
        rw [← Real.exp_add]; norm_num
      rw [h12]
      nlinarith
    nlinarith [Real.exp_pos q]
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp (q + 12) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / (8 * (M + 1)) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right hα (by positivity)

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_model_error {u p Q P K Fcap cap tau ε : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hF : 0 ≤ Fcap) (hcap : 0 ≤ cap)
    (hKp : K ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) (hcapP : cap ≤ Real.exp p)
    (htau : tau ≤ Real.exp (-(u + 3)))
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hε : ε ≤ 6 * positiveProjectionAccuracy P) :
    2 * tau + 2 * (cap + 2 / Real.exp (-Q)) * (K + Fcap) * ε ≤ Real.exp (-u) := by
  have hKP : K + Fcap ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos p]
  have hcapP' : cap ≤ Real.exp (p + 1) :=
    hcapP.trans (Real.exp_le_exp.mpr (by linarith))
  have h := allocated_native_approximation_error hu (show 0 ≤ p + 1 by linarith) hQ
    (add_nonneg hK hF) hcap hKP hcapP' htau (by linarith : u + 2 * (p + 1) + Q + 30 ≤ P) hε
  convert h using 1
  ring

theorem forecastAugmented_model_size {u p Q K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hF : 0 ≤ Fcap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    2 / Real.exp (-Q) ≤ Real.exp (Q + 2) ∧
      1 + 4 * (2 * K * C + Fcap) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤
        Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  have hKP : K + Fcap ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos p]
  have hCp' : C ≤ Real.exp (p + 1) := hCp.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨hcoeff, hterms⟩ := allocatedModel_size_bounds hu (show 0 ≤ p + 1 by linarith)
    hQ (add_nonneg hK hF) (by linarith : 0 ≤ C) hKP hCp'
  refine ⟨hcoeff, ?_⟩
  have hL : 2 * K * C + Fcap ≤ (K + Fcap) * (2 * C) := by nlinarith
  have hL0 : 0 ≤ 2 * K * C + Fcap := by positivity
  calc
    _ ≤ 1 + 4 * ((K + Fcap) * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) := by gcongr
    _ ≤ Real.exp (2 * Q + 2 * u + 4 * (p + 1) + 30) := hterms
    _ = _ := by congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_approximation_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * u + 4 * p + 12)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 8 := by
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have he : Real.exp (4 : ℝ) = Real.exp 2 * Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 4 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 8 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h8
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2
      (by norm_num)

theorem forecastAugmented_model_parameters {u p q sourceGain : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsource : 0 ≤ sourceGain) :
    let Q := max sourceGain (2 * u + 4 * p + q + 20)
    let Ptail := u + 2 * p + Q + 32
    0 ≤ Q ∧ 0 ≤ Ptail ∧ sourceGain ≤ Q ∧
      2 * u + 4 * p + q + 20 ≤ Q ∧
      Real.exp (-Q) ≤ Real.exp (-sourceGain) ∧
      u + 2 * p + Q + 32 ≤ Ptail := by
  dsimp only
  have hQ : 0 ≤ max sourceGain (2 * u + 4 * p + q + 20) :=
    hsource.trans (le_max_left _ _)
  exact ⟨hQ, by positivity, le_max_left _ _, le_max_right _ _,
    Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _)), le_rfl⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem forecastNormalizedTwist_mem_fixed_native_family
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0} {budget : ℝ}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (hperiod : periodCap ≤ Real.exp budget) (hcover : coverCap ≤ Real.exp budget)
    (hL : (L : ℝ) ≤ Real.exp budget) (hbudget : 2 ≤ budget)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) :
    (fun t => W.eval N poly (sample t)) ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp budget) (Real.exp budget)
        ⟨Real.exp budget, Real.exp_nonneg _⟩) t => V.eval N poly (sample t)) := by
  let V := W.mono hperiod hcover (show L ≤ ⟨Real.exp budget, Real.exp_nonneg _⟩ from hL)
  have h := normalizedTwist_eval_mem_twistedNativeSampleFunctions V N poly sample w degree hbudget
  have he : (fun t => V.eval N poly (sample t)) = (fun t => W.eval N poly (sample t)) := rfl
  rw [he] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem forecastFiniteTwists_common_family
    {X Ω Term : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (localBudget Pnative : ℝ) (hPn : 0 ≤ Pnative)
    (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) :
    let budget := max localBudget (3 * Pnative + 3)
    (∀ t, (fun ω => (twists t).eval N poly (sample ω)) ∈
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω))) ∧
    (twistedNativeSampleFunctions w degree localBudget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩) ω => W.eval N poly (sample ω)) ⊆
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω))) := by
  intro budget
  have hle : 3 * Pnative + 3 ≤ budget := le_max_right _ _
  have hbudget : 2 ≤ budget := (show 2 ≤ 3 * Pnative + 3 by linarith).trans hle
  refine ⟨?_, normalizedNativeSampleFunctions_mono N poly w degree sample (le_max_left _ _)⟩
  intro t
  exact forecastNormalizedTwist_mem_fixed_native_family (twists t)
    (Real.exp_le_exp.mpr hle) (Real.exp_le_exp.mpr hle) (Real.exp_le_exp.mpr hle)
    hbudget N poly sample w degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X Ω Forecast : Type*} [Fintype X]
variable {Term : Forecast → Type*} {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem centeredForecastTwist_mem_common_family
    {sample : Ω → X → ℤ} {w : X → ℕ} {degree : ℕ}
    (localBudget Pnative : ℝ) (hPn : 0 ≤ Pnative)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Forecast → ∀ j, J j → ℝ) (f : Forecast) (i : Term f) :
    let budget := max localBudget (3 * Pnative + 3)
    (fun ω => ((twists f i).shiftConstant (c f)).eval N poly (sample ω)) ∈
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω)) := by
  exact (forecastFiniteTwists_common_family localBudget Pnative hPn
    (fun i => (twists f i).shiftConstant (c f)) N poly sample w degree).1 i

theorem centeredForecastTwist_sum_eq
    [∀ f, Fintype (Term f)] {periodCap coverCap : ℝ} {L : ℝ≥0}
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (coeff : ∀ f, Term f → ℂ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Forecast → ∀ j, J j → ℝ) (f : Forecast) (u : X → ℤ) :
    (∑ i, coeff f i * ((twists f i).shiftConstant (c f)).eval N poly u) =
      ∑ i, coeff f i * (twists f i).eval N (fun j => subtractConstant (c f j) (poly j)) u := by
  simp only [NormalizedPolynomialTwist.eval_shiftConstant]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

structure ActualForecastData (N : X → ℕ)
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Pnative massLog capLog E : ℝ) where
  target : integerBox N → ℂ
  centerConstant : ∀ j, J j → ℝ
  Term : Type
  [fintypeTerm : Fintype Term]
  coefficient : Term → ℂ
  twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
    (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
    ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩
  cap : ∀ v, ‖target v‖ ≤ Real.exp capLog
  mass : (∑ i, ‖coefficient i‖) ≤ Real.exp massLog
  approximation : ∀ v, ‖target v - ∑ i, coefficient i *
    (twists i).eval N (fun j => subtractConstant (centerConstant j) (originalpoly j)) v.val‖ ≤
      Real.exp (-E)

attribute [instance] ActualForecastData.fintypeTerm

namespace ActualForecastData

variable (N : X → ℕ) (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (Pnative massLog capLog E : ℝ)

noncomputable def zero : ActualForecastData N originalpoly Pnative massLog capLog E where
  target := fun _ => 0
  centerConstant := fun _ _ => 0
  Term := Empty
  coefficient := fun i => nomatch i
  twists := fun i => nomatch i
  cap := fun _ => by simpa only [norm_zero] using Real.exp_nonneg capLog
  mass := by simpa using Real.exp_nonneg massLog
  approximation := fun _ => by simpa using Real.exp_nonneg (-E)

@[simp] theorem zero_target (v : integerBox N) :
    (zero N originalpoly Pnative massLog capLog E).target v = 0 := rfl

@[simp] theorem zero_centerConstant (j : Fin m) (i : J j) :
    (zero N originalpoly Pnative massLog capLog E).centerConstant j i = 0 := rfl

end ActualForecastData

variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ} {F : Type*}

noncomputable def actualForecastOptionFamily
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) :
    Option F → ActualForecastData N originalpoly Pnative massLog capLog E
  | none => ActualForecastData.zero N originalpoly Pnative massLog capLog E
  | some f => data f

@[simp] theorem actualForecastOptionFamily_some
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) (f : F) :
    actualForecastOptionFamily data (some f) = data f := rfl

@[simp] theorem actualForecastOptionFamily_none_target
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E)
    (v : integerBox N) : (actualForecastOptionFamily data none).target v = 0 := rfl

@[simp] theorem actualForecastOptionFamily_none_centerConstant
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E)
    (j : Fin m) (i : J j) :
    (actualForecastOptionFamily data none).centerConstant j i = 0 := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualForecastData
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ}
variable (data : ActualForecastData N originalpoly Pnative massLog capLog E)

end Erdos3.VectorPolynomial.ActualForecastData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e dQ dQF : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s dQ)
    (hQ : Q.filtration = D.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold (M ⧸ Fmark.filtration.layerIdeal (s + 1)) s dQF)
    (hQF : QF.filtration = Fmark.filtration.quotientTop)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark.filtration φ marked)

noncomputable def topQuotient :
    AllocatedExternalLocalCandidate C Q QF.filtration
      (D.topQuotientMarkedMap Fmark φ hφ) (Fmark.topQuotientOrbit QF hQF marked) where
  orbit := D.topQuotientOrbit Q hQ candidate.orbit
  mark_on_slice u hu := by
    rw [D.topQuotientOrbit_eval Q hQ, Fmark.topQuotientOrbit_eval QF hQF]
    have hsquare :
        realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
          (hM := QF.filtration.lowerCentralSeries_eq_bot)
          (D.topQuotientMarkedMap Fmark φ hφ)
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) =
        realificationMap (hnil := Fmark.filtration.lowerCentralSeries_eq_bot)
          (hM := QF.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (Fmark.filtration.layerIdeal (s + 1)))
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) := by
      apply NilpotentLieBCHGroup.ext
      exact D.topQuotientMarkedMap_real_mk Fmark φ hφ _
    rw [hsquare, candidate.mark_on_slice u hu]

@[simp] theorem topQuotient_orbit :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).orbit =
      D.topQuotientOrbit Q hQ candidate.orbit := rfl

theorem topQuotient_value (u : C.Variables → ℤ) :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).value u =
      (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
          (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) : Q.Space) := by
  unfold value
  rw [topQuotient_orbit, D.topQuotientOrbit_eval Q hQ]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e dQ dQF : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s dQ)
    (hQ : Q.filtration = D.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold (M ⧸ Fmark.filtration.layerIdeal (s + 1)) s dQF)
    (hQF : QF.filtration = Fmark.filtration.quotientTop)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
        observable x (QuotientGroup.mk g))

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

noncomputable def refilteredFrozenObservable (x : X → ℤ) (source : Dref.RealGroup) : ℂ :=
  observable x (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) left *
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source *
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) right))

noncomputable def refilteredQuotientObservable (x : X → ℤ) : Q.Space → ℂ :=
  positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
    (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) markedMiddle))

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (hrecovery : ∀ x source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)
    (hfactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      D.filtration.realification.polynomialOrbitEval (fun _ => 1) u (P.candidate z).orbit =
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) left *
          realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
          D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) right)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

universe u

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

theorem refilteredFrozenObservable_recovery_of_coveredDiagram
    {inputDenominator k : ℕ} {p coverCost dictBound : ℝ}
    (rightDictionary : D.NativeGridRightDictionary inputDenominator dictBound)
    (covered : RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram
      D Fmark φ hφ W k rightDictionary.denominator p coverCost)
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ Real.exp ((p + 2) ^ k))
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid inputDenominator) :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 covered.Fref.basis
    letI := moduleTopology ℝ (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1)))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 covered.Q.basis
    letI := covered.Q.metricSpace
    letI := covered.Fref.metricSpace
    let diagram := covered.Dref.markedTopQuotientDiagram covered.Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) covered.Q
    let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    ∀ x ∈ integerBox N, ∀ source,
      positiveImageSlice diagram K
        (P.refilteredFrozenObservable A Fmark φ W covered.Dref left right x)
        (diagram source).2 (diagram source).1 =
          P.refilteredFrozenObservable A Fmark φ W covered.Dref left right x source := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 covered.Fref.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 covered.Q.basis
  let := covered.Q.metricSpace
  let := covered.Fref.metricSpace
  dsimp only
  intro x hx
  apply rightDictionary.markedTopQuotient_recovery D Fmark φ hφ W
    covered.Dref covered.Fref covered.Q ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    (observable x)
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) left)
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) right) (hright x hx)
  dsimp only
  intro j
  exact covered.recovery
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) left)
    (rightDictionary.representative j) (hleft x hx)
    (rightDictionary.representative_bounds j).2 (observable x) ℓ hℓ
    (hLip x hx) (hpositive x hx)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

section Operator

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

end Operator

section ActualProblem

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

end AllocatedExternalCandidateProblem
end ActualProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

variable {Physical Bin : Type*}
    (left right : Physical → D.RealGroup) (mark : Physical → Fref.Space)
    (F : Physical → D.Space → ℂ) (centers : Bin → D.Space → ℂ)
    {ε : ℝ} (hnet : ∀ x, ∃ i, ∀ z, ‖F x z - centers i z‖ ≤ ε)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateNativeFrozenScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (hrecovery : ∀ x source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)

noncomputable def refilteredFrozenScore (z : P.productive) : ℝ :=
  (𝔼 u ∈ (P.chart z).slice.integerPoints, weight ((P.chart z).physical u) *
    P.refilteredFrozenObservable A Fmark φ W Dref left right ((P.chart z).physical u)
      (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)).re

variable {frozenScoreThreshold : ℝ}
    (hscore : ∀ z : P.productive, frozenScoreThreshold ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z)

variable (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked)

omit [PseudoMetricSpace Fref.Space] in
include hmarkFactor in

theorem refilteredScoredAssembly_mark_on_slice
    (ambientMiddle : Dref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (hmarkedMiddle : map (realLieHomToRat (realificationLieHom (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W))).toLinearMap
      ambientMiddle.log = markedMiddle.log)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
        (D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked := by
  have hglobal := Dref.filtration.formal_mark_realEval Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (fullTaggedVariableWeight (X := X) J)
    ambientMiddle markedMiddle hmarkedMiddle (fun i => ((P.chart z).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hglobal
  have heval := D.externalCandidateOrbit_realEval W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
    (fun i => ((P.chart z).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at heval
  rw [heval, ← hmarkFactor z u hu]
  simp only [map_mul]
  rw [D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    hglobal, (middle z).mark_on_slice u hu]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

noncomputable def refilteredLocalCoordinates (z : P.productive) :
    (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : (P.chart z).Variables => 1)).Group :=
  D.filtration.realification.polynomialOrbitCoordinates _
    (D.includedRefilteredOrbit W Dref hDref _ (middle z).orbit)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem refilteredLocalCoordinates_value (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
      (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z) =
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
  simpa only [refilteredLocalCoordinates,
    NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    polynomialOrbitRealEval_integer] using
      D.includedRefilteredOrbit_realEval W Dref hDref (fun _ => 1) (middle z).orbit
        (fun i => (u i : ℝ))

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hfactor : ∀ z : P.productive,
      localLeft z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle z * localRight z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)
    (hcoset : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1)
        (fun i => (u i : ℝ))
        ((D.filtration.filteredRealPolynomialSection Fmark.filtration (fun _ => 1)
          sectionMap hSectionFilt (localRightMark z))⁻¹ * localRight z)) : D.Space) =
        QuotientGroup.mk kR)
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
include hsection hkE hkR hfactor hleft hright in

theorem refilteredFrozen_mark_on_slice
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localRight z) = localRightMark z)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE) *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked := by
  have he := D.filtration.frozenMarkedOuter_product_mark_eq Fmark.filtration φ hφ
    sectionMap hSectionFilt hsection (fun _ : (P.chart z).Variables => 1)
    (D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (localLeft z)
    (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
    (localRight z) (hfactor z) (localLeftMark z) (localRightMark z)
    (hprojLeft z) (hprojRight z) (fullTaggedVariableWeight (X := X) J) leftMark rightMark kE kR hkE hkR
    (fun i => (u i : ℝ)) (fun i => ((P.chart z).chartValues u i : ℝ))
    (hleft z u hu) (hright z u hu)
  simp only [NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle,
    polynomialOrbitRealEval_integer] at he
  exact he.trans ((P.candidate z).mark_on_slice u hu)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFiniteFreezingDictionaryProducer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
include hleft hright hσ1 H hH hchart hsmall hp in

theorem refilteredFrozenObservable_eq_localFrozen
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    P.refilteredFrozenObservable A Fmark φ W Dref
      (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE)
      (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)
      ((P.chart z).physical u)
      (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) =
    observable ((P.chart z).physical u) (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (D.filtration.frozenMarkedLeft Fmark.filtration (fun _ => 1) sectionMap hSectionFilt
            (localLeftMark z) kE *
          P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z *
          D.filtration.frozenMarkedRight Fmark.filtration (fun _ => 1) sectionMap hSectionFilt
            (localRightMark z) kR))) := by
  have hl := D.filtration.frozenMarkedLeftOrbit_realEval_eq_local Fmark.filtration (fullTaggedVariableWeight (X := X) J)
    sectionMap hSectionFilt leftMark kE (fun _ : (P.chart z).Variables => 1)
    (localLeftMark z) (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hleft z u hu)
  have hr := D.filtration.frozenMarkedRightOrbit_realEval_eq_local Fmark.filtration (fullTaggedVariableWeight (X := X) J)
    sectionMap hSectionFilt rightMark kR (fun _ : (P.chart z).Variables => 1)
    (localRightMark z) (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hright z u hu)
  simp only [polynomialOrbitRealEval_integer] at hl hr
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  unfold refilteredFrozenObservable
  rw [← htags, hl, hr]
  simp only [map_mul,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

namespace Refinement
variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def refilteredMiddle : ∀ z : refinement.problem.productive,
    AllocatedExternalLocalCandidate (refinement.problem.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      markedMiddle := fun z =>
  (middle ⟨z.val, refinement.subset z.property⟩).refineSlice
    (refinement.step z) (refinement.step_pos z) (refinement.slice z) (refinement.dense z)
    (refinement.inside z)

end Refinement

variable {Index : Type*} [Fintype Index] [Nonempty Index]
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (leftCenter rightCenter : Index → D.RealGroup)

theorem exists_frozen_refinement_of_local_slices
    {newCost frozenThreshold Bweight ε : ℝ}
    (hcost : cost ≤ newCost) (hBweight : 0 ≤ Bweight) (hε : 0 ≤ ε)
    (step : P.productive → ℕ) (hstep : ∀ z, 0 < step z)
    (slice : ∀ z : P.productive,
      ResidueBoxSlice (fun i : (P.chart z).Variables => A.sides i.val) (step z))
    (hdense : ∀ z, IsDenseCommonStrideBox (fun i : (P.chart z).Variables => A.sides i.val)
      newCost (slice z).integerPoints)
    (hinside : ∀ z, (slice z).integerPoints ⊆ (P.chart z).slice.integerPoints)
    (label : P.productive → Index)
    (hweight : ∀ z, ∀ u ∈ (slice z).integerPoints, ‖weight ((P.chart z).physical u)‖ ≤ Bweight)
    (herror : ∀ z, ∀ u ∈ (slice z).integerPoints,
      ‖observable ((P.chart z).physical u) ((P.candidate z).value u) -
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)‖ ≤ ε)
    (hfrozen : ∀ z, frozenThreshold ≤
      (𝔼 u ∈ (slice z).integerPoints, weight ((P.chart z).physical u) *
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)).re) :
    ∃ chosen : Index,
      ∃ refinement : P.Refinement newCost
        (massThreshold / (Fintype.card Index : ℝ)) (frozenThreshold - Bweight * ε),
      ∀ z : refinement.problem.productive, frozenThreshold ≤
        refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter chosen))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter chosen)) markedMiddle
          (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  have hscore (z : P.productive) : frozenThreshold - Bweight * ε ≤
      (𝔼 u ∈ (slice z).integerPoints, weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u) ((P.candidate z).value u)).re := by
    have he := complex_expect_error_le (slice z).integerPoints
      (fun u => weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u) ((P.candidate z).value u))
      (fun u => weight ((P.chart z).physical u) *
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit))
      (mul_nonneg hBweight hε) (by
        intro u hu
        rw [← mul_sub, norm_mul]
        exact mul_le_mul (hweight z u hu) (herror z u hu) (norm_nonneg _) hBweight)
    have hre := (Complex.abs_re_le_norm _).trans he
    rw [Complex.sub_re] at hre
    have hlo := (abs_le.mp hre).1
    have hs := hfrozen z
    linarith
  let initial : P.Refinement newCost massThreshold (frozenThreshold - Bweight * ε) := {
    retained := P.productive
    subset := fun _ hz => hz
    mass := P.mass
    cost_le := hcost
    step := step
    step_pos := hstep
    slice := slice
    dense := hdense
    inside := hinside
    scoreLower := hscore }
  obtain ⟨chosen, paths, hpaths, hmass, hlabel⟩ := initial.exists_common_label label
  let refinement := initial.restrictPaths paths hpaths hmass
  refine ⟨chosen, refinement, ?_⟩
  intro z
  have hl : label ⟨z.val, hpaths z.property⟩ = chosen := hlabel z
  have hs := hfrozen ⟨z.val, hpaths z.property⟩
  rw [hl] at hs
  exact hs

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

namespace Refinement

variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)
    (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

theorem refiltered_mark_on_slice
    (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
            ((P.chart z).chartValues u) left *
          realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
          D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
            ((P.chart z).chartValues u) right) =
        Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P.chart z).chartValues u) marked)
    (z : refinement.problem.productive) (u : (refinement.problem.chart z).Variables → ℤ)
    (hu : u ∈ (refinement.problem.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u
            ((refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((refinement.problem.chart z).chartValues u) marked :=
  hmarkFactor ⟨z.val, refinement.subset z.property⟩ u (refinement.inside z hu)

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem exists_finite_freezing_refinement_of_dictionary
    {l : ℕ} {slow ε budget Bweight Bobs Lip frozenThreshold θ densityCost : ℝ}
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow ε budget)
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * budget * max 1 budget) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hthreshold : 0 ≤ frozenThreshold) (hθ : 0 < θ)
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold) :
    ∃ chosen : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∃ refinement : (P₀.withKeep keep hkeep).Refinement
        (max cost (densityCost +
          Real.log ((4 * dictionary.modulus * dictionary.Q * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))
        (massThreshold / (Fintype.card ((Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) : ℝ))
        (frozenThreshold - Bweight * (Lip * ε)),
      ∀ z : refinement.problem.productive, frozenThreshold ≤
        refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
            (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left chosen.1))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration
            (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right chosen.2))
          markedMiddle (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  let grid := dictionary.grid
  let Q := dictionary.Q
  let modulus := dictionary.modulus
  let rightCount := dictionary.rightCount
  let left := dictionary.left
  let right := dictionary.right
  have hQ := dictionary.Q_pos
  have hQbound := dictionary.Q_bound
  have hmodulus := dictionary.modulus_pos
  have hrightCount := dictionary.rightCount_pos
  have hmodulusBound := dictionary.modulus_bound
  have hselect := dictionary.select
  let : Nonempty (Fin rightCount) := ⟨⟨0, hrightCount⟩⟩
  have hlength (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      max 2 (2 * budget * max 1 budget) ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) := by
    calc
      _ = Real.exp (-densityCost) *
          (Real.exp densityCost * max 2 (2 * budget * max 1 budget)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (-densityCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hfloor i) (Real.exp_nonneg _)
      _ ≤ _ := ((P₀.withKeep keep hkeep).chart z).slice.length_lower_of_dense ((P₀.withKeep keep hkeep).chart z).step_pos (hdensity z) i
  have htwo (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) : 2 ≤ ((P₀.withKeep keep hkeep).chart z).slice.length i := by
    exact_mod_cast (le_max_left (2 : ℝ) _).trans (hlength z i)
  have hlong (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      2 * budget * max 1 budget ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) :=
    (le_max_right (2 : ℝ) _).trans (hlength z i)
  have hlocal (z : (P₀.withKeep keep hkeep).productive) :=
    ((P₀.withKeep keep hkeep).chart z).finiteFreezing_of_selection ((P₀.withKeep keep hkeep).candidate z) sectionMap hSectionFilt
      (localLeftMark z) (localRightMark z)
      ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
      Q modulus hQ hmodulus left right tests weight hQbound hmodulusBound
      (htwo z) (hlong z) (hdensity z) hθ (mul_nonneg hBweight (mul_nonneg hLip hε))
      (by simpa only [htests] using (P₀.withKeep keep hkeep).score z)
      (by
        intro hNp hparent hwidth hlarge hindexed
        obtain ⟨_, hselected⟩ := hselect (localLeft z) (localLeftMark z)
          (localRight z) (localRightMark z) (hslowLeft z) (hslowMark z)
          (hrationalRight z) (hrationalMark z) (hprojLeft z) (hprojRight z)
        exact hselected tests ((P₀.withKeep keep hkeep).chart z).physical (fun u => weight (((P₀.withKeep keep hkeep).chart z).physical u))
          Bweight Bobs Lip hBweight hBobs hLip (fun u _ => hweight _) hnorm hlip
          (((P₀.withKeep keep hkeep).chart z).freezingNativeOrbit ((P₀.withKeep keep hkeep).candidate z))
          ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
          (hfactor z) ((P₀.withKeep keep hkeep).chart z).slice.length hNp
          (fun i => (((P₀.withKeep keep hkeep).chart z).slice.start i : ℤ)) ((P₀.withKeep keep hkeep).chart z).step
          hparent hwidth hlarge frozenThreshold θ scoreThreshold hthreshold hθ hindexed hbudget)
  choose slice hdense hinside ileft iright herror _hweighted hfrozen _hscore using hlocal
  have hvalue (z : (P₀.withKeep keep hkeep).productive) (i : Fin d → Fin (grid + 1)) (j : Fin rightCount)
      (u : ((P₀.withKeep keep hkeep).chart z).Variables → ℤ) (hu : u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints) :
      ((P₀.withKeep keep hkeep).chart z).freezingFrozenValue sectionMap hSectionFilt
        (localLeftMark z) (localRightMark z)
        ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
        tests (left i) (right j) u =
      (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref
        (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (left i))
        (D.filtration.frozenMarkedRightOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (right j))
        (((P₀.withKeep keep hkeep).chart z).physical u)
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
    symm
    simpa only [AllocatedExternalLocalChart.freezingFrozenValue,
      RationalFilteredNilmanifold.Niltest.markedFrozenValue, htests] using
      (P₀.withKeep keep hkeep).refilteredFrozenObservable_eq_localFrozen A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle sectionMap hSectionFilt leftMark rightMark (left i) (right j)
        localLeftMark localRightMark hleft hright hσ1 H hH hchart hsmall hp z u hu
  obtain ⟨chosen, refinement, hscore⟩ :=
    (P₀.withKeep keep hkeep).exists_frozen_refinement_of_local_slices A Fmark φ hφ W Dref Fref markedMiddle middle
      sectionMap hSectionFilt leftMark rightMark
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => left ij.1)
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => right ij.2)
      (le_max_left cost _) hBweight (mul_nonneg hLip hε)
      (fun z => ((P₀.withKeep keep hkeep).chart z).step * modulus)
      (fun z => Nat.mul_pos ((P₀.withKeep keep hkeep).chart z).step_pos hmodulus)
      slice (fun z => (hdense z).mono (by
        exact le_max_right cost (densityCost +
          Real.log ((4 * modulus * Q *
            (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))) hinside
      (fun z => (ileft z, iright z))
      (fun z u _ => hweight (((P₀.withKeep keep hkeep).chart z).physical u))
      (by
        intro z u hu
        have he := herror z u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)] at he
        simpa only [htests] using he)
      (by
        intro z
        apply (hfrozen z).le.trans_eq
        apply congrArg Complex.re
        apply Finset.expect_congr rfl
        intro u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)])
  exact ⟨chosen, refinement, hscore⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end


