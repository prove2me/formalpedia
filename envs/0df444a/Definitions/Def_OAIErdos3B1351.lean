-- Prove2me | Definitions.Def_OAIErdos3B1351
-- name    : OAIErdos3B1351
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T01:31:05.954509+00:00
-- url     : https://prove2.me/theorems/1a9adcea-9aa4-4bbd-a728-54eeaaba658c
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1352 of 1379
-- statement:
--   Definitions bundle 1352 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1350`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1352 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.exists_marked_topQuotientOrbit_lift_externalFamily_on`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_ambientPhysicalValue_score`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_complexMean_physical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_score`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_refilteredQuotientScored_on`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredQuotientCandidate_score_eq_frozen_on`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.refilteredQuotientScoredProblem_on`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.restrictObservable`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.restrictObservable_physicalIntegerPoint`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.physical_mem_integerBox`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.sides_pos`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.trimMargin_proper`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.physical_mem_integerBox`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.physical_retainedSite`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedLaw_complexMean_parameter`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedLaw_complexMean_physical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedParameter_retainedSite`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedSite`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedSite_val`, `OAI.Erdos3.VectorPolynomial.exists_fixedLaw_centered_forecast_twist_model`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_forecast_approximation`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_forecast_model`, `OAI.Erdos3.exists_forecast_augmented_model`, `OAI.Erdos3.exists_forecast_augmented_model_of_expansions`, `OAI.Erdos3.exists_forecast_augmented_native_model_of_expansions`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B079

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_forecast_augmented_model
    {Ω T X F : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    [Nonempty F] {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (physical : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (forecast : F → X → ℂ) {atoms : Set (X → ℂ)}
    (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatom : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C forecastCap B beta tau ε : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f x, ‖forecast f x‖ ≤ forecastCap)
    (hlocal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g →
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖)
    (hglobal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) → ∀ f,
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 2 ≤
        ‖r.correlation g (forecast f)‖ →
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖)
    (hexcess : r.excessMass (μ.siteLaw physical) C ≤ ε)
    (input : X → ℂ) (hinput : ∀ x, ‖input x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (err : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ input = (∑ i, c i • Q i) + err ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε ∧
      (∀ f, ‖r.correlation err (forecast f)‖ ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε) ∧
      (n : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let q := μ.siteLaw physical
  let density := fun x => K * r.relativeDensity q x + forecastCap
  let good := Finset.univ.filter (fun x => r.relativeDensity q x ≤ 2 * C)
  let seminorm := sampledSliceSeminorm μ physical slices tests ⊔
    forecastFamilySeminorm r forecast
  let cap := max 1 ((2 * K * C + forecastCap) / tau)
  have hcap : 1 ≤ cap := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have henvelope (g : X → ℂ) :
      seminorm g ≤ 1 * r.mean (fun x => density x * ‖g x‖) := by
    have hmean : r.mean (fun x => density x * ‖g x‖) =
        K * q.mean (fun x => ‖g x‖) + forecastCap * r.mean (fun x => ‖g x‖) := by
      simp only [density, add_mul, r.mean_add, mul_assoc, r.mean_const_mul,
        r.mean_relativeDensity q hr]
    rw [one_mul, hmean]
    apply max_le
    · exact (sampledSliceSeminorm_le_siteLaw μ physical slices tests hsize htests g).trans
        (le_add_of_nonneg_right (mul_nonneg hforecastCap (r.mean_nonneg (fun _ => norm_nonneg _))))
    · exact (forecastFamilySeminorm_le r forecast hforecast g).trans
        (le_add_of_nonneg_left (mul_nonneg hK (q.mean_nonneg (fun _ => norm_nonneg _))))
  have hunit (g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
      (hlarge : (tau / B ^ 2) / cap ≤ seminorm g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    rcases le_max_iff.mp hlarge with hl | hf
    · exact hlocal g hg hl
    · have hpos : 0 < (tau / B ^ 2) / cap := by
        apply div_pos (div_pos htau (sq_pos_of_pos hB))
        exact lt_of_lt_of_le zero_lt_one hcap
      have hex : ∃ f, ((tau / B ^ 2) / cap) / 2 ≤ ‖r.correlation g (forecast f)‖ := by
        by_contra! hnot
        have hu := forecastFamilySeminorm_apply r forecast hforecast g
        have hle : forecastFamilySeminorm r forecast g ≤ ((tau / B ^ 2) / cap) / 2 := by
          rw [hu]
          exact ciSup_le (fun f => (hnot f).le)
        linarith only [hf, hle, hpos]
      obtain ⟨f, hf⟩ := hex
      exact hglobal g hg f hf
  have hdetector (g : X → ℂ)
      (hg : ∀ x, ‖g x‖ ≤ 1 * (2 * K * C + forecastCap) / tau)
      (hlarge : tau / B ^ 2 ≤ seminorm g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    have hbounded (x : X) : ‖g x‖ ≤ (2 * K * C + forecastCap) / tau := by
      simpa only [one_mul] using hg x
    obtain ⟨Q, hQ, hc⟩ := detector_of_unit_detector r seminorm atoms
      (lt_of_lt_of_le zero_lt_one hcap) hunit g
      (fun x => (hbounded x).trans (le_max_right _ _)) hlarge
    refine ⟨Q, hQ, le_trans ?_ hc⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap hbeta.le
  obtain ⟨n, hn, Q, c, err, hQ, heq, hc, he, hnterms⟩ :=
    exists_model_with_tail_error r good seminorm density hbal hatoms hatom
      zero_le_one (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hC0) hforecastCap)
      hB hbeta htau
      (fun x => add_nonneg (mul_nonneg hK (r.relativeDensity_nonneg q x)) hforecastCap)
      (fun x hx => r.forecastAugmented_envelope_le_on_good q hK x hx)
      henvelope hdetector input hinput
  have htail := r.forecastAugmented_envelope_tail_le q hr hK hforecastCap hC hexcess
  have herr : seminorm err ≤ 2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε := by
    have hmul := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ B + 2 / beta by positivity)
    dsimp only [density, good] at he
    simp only [one_mul] at he
    nlinarith only [he, hmul]
  refine ⟨n, hn, Q, c, err, hQ, heq, hc, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans herr
  · intro f
    exact (forecast_correlation_le_family r forecast hforecast err f).trans
      ((le_max_right _ _).trans herr)
  · simpa only [one_mul] using hnterms

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_forecast_augmented_model_of_expansions
    {Ω T X F : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    [Nonempty F] {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (physical : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (forecast : F → X → ℂ) {atoms : Set (X → ℂ)}
    (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatom : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C forecastCap B beta tau ε M : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f x, ‖forecast f x‖ ≤ forecastCap)
    (hlocal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g →
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖)
    (Term : F → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → X → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ atoms)
    (hM : 0 ≤ M) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f x, ‖forecast f x - ∑ i, coefficient f i * atom f i x‖ ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 8)
    (hforecastGain : beta ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / (8 * (M + 1)))
    (hexcess : r.excessMass (μ.siteLaw physical) C ≤ ε)
    (input : X → ℂ) (hinput : ∀ x, ‖input x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (err : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ input = (∑ i, c i • Q i) + err ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε ∧
      (∀ f, ‖r.correlation err (forecast f)‖ ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε) ∧
      (n : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  have hα : 0 < (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) :=
    div_pos (div_pos htau (sq_pos_of_pos hB))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply exists_forecast_augmented_model μ physical slices tests r hr forecast
    hbal hatoms hatom hK hC hforecastCap hB hbeta htau hsize htests hforecast hlocal
    (fun g hg f hlarge => forecast_detector_of_atom_approximation r (forecast f) g
      (coefficient f) (atom f) hα hM hg (hexpansionAtoms f) (happrox f) (hmass f)
      hforecastGain hlarge) hexcess input hinput

theorem exists_forecast_augmented_native_model_of_expansions
    {Ω T X F σ I : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    [Nonempty F] {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (physical : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (forecast : F → X → ℂ)
    (w : σ → ℕ) (degree : ℕ) (complexity : ℝ) (sample : X → σ → ℤ)
    (twist : I → X → ℂ) (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    {K C forecastCap B beta tau ε M : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f x, ‖forecast f x‖ ≤ forecastCap)
    (hlocal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g →
      ∃ Q ∈ twistedNativeSampleFunctions w degree complexity sample twist, beta ≤ ‖r.correlation g Q‖)
    (Term : F → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → X → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity sample twist)
    (hM : 0 ≤ M) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f x, ‖forecast f x - ∑ i, coefficient f i * atom f i x‖ ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 8)
    (hforecastGain : beta ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / (8 * (M + 1)))
    (hexcess : r.excessMass (μ.siteLaw physical) C ≤ ε)
    (input : X → ℂ) (hinput : ∀ x, ‖input x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (err : X → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity sample twist) ∧ input = (∑ i, c i • Q i) + err ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε ∧
      (∀ f, ‖r.correlation err (forecast f)‖ ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε) ∧
      (n : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  exact exists_forecast_augmented_model_of_expansions μ physical slices tests r hr forecast
    (twistedNativeSampleFunctions_balanced twist)
    ⟨0, twistedNativeSampleFunctions_zero twist⟩
    (fun Q hQ x => twistedNativeSampleFunctions_norm twist htwist hQ x)
    hK hC hforecastCap hB hbeta htau hsize htests hforecast hlocal
    Term coefficient atom hexpansionAtoms hM hmass happrox hforecastGain hexcess input hinput

end Erdos3

end

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_forecast_approximation
    {Ω T X Forecast : Type*} [Nonempty Forecast] [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    (forecast : Forecast → integerBox N → ℂ)
    {K C forecastCap cap beta tau εtail M : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap) (hcap : 0 < cap)
    (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      (tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → integerBox N → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity
      (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (u : integerBox N) => W.eval N poly u.val))
    (hM : 0 ≤ M) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f u, ‖forecast f u - ∑ i, coefficient f i * atom f i u‖ ≤
      ((tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 8)
    (hforecastGain : beta ≤
      ((tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / (8 * (M + 1)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤ εtail)
    (input : integerBox N → ℂ) (hinput : ∀ u, ‖input u‖ ≤ cap) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (cap + 2 / beta) * (K + forecastCap) * εtail ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        2 * tau + 2 * (cap + 2 / beta) * (K + forecastCap) * εtail) ∧
      (nterms : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let : Nonempty (integerBox N) := (integerBox_nonempty N).to_subtype
  have htwist (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) : ‖W.eval N poly u.val‖ ≤ 1 := W.norm_eval_le N poly u.val
  have hdetector (g : integerBox N → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1)
      (hlarge : (tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation g
          (fun u => star (W.eval N poly u.val) * G u)‖ := by
    let ext := finiteSiteExtension (Subtype.val : integerBox N → X → ℤ) g
    let signal := zeroExtendFinset (integerBox N) ext
    have hsignal (u) : ‖signal u‖ ≤ 1 :=
      zeroExtendFinset_norm_le_one (integerBox N) ext
        (fun u _ => finiteSiteExtension_norm_le _ g hg u) u
    have hzero (u) (hu : u ∉ integerBox N) : signal u = 0 := by
      simp only [signal, zeroExtendFinset, if_neg hu]
    have hvalue (u : integerBox N) : signal u.val = g u := by
      simpa only [signal, zeroExtendFinset, if_pos u.property, ext] using
        finiteSiteExtension_apply Subtype.val Subtype.val_injective g u
    have hseminorm := sampledSliceSeminorm_congr_values μ site physical slices tests
      hsize htests signal g (fun z t => by rw [← hphysical z t]; exact hvalue _)
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero
      (hseminorm.symm ▸ hlarge)
    exact ⟨W, G, hG, by simpa only [hvalue] using hc⟩
  have hr (u : integerBox N) : 0 <
      (FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).weight u := by
    change 0 < (Fintype.card (integerBox N) : ℝ)⁻¹
    positivity
  apply exists_forecast_augmented_native_model_of_expansions μ physical slices tests
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)) hr forecast
    w degree complexity (fun u : integerBox N => u.val)
    (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) => W.eval N poly u.val)
    htwist hK hC hforecastCap hcap hbeta htau hsize htests hforecast ?_
    Term coefficient atom hexpansionAtoms hM hmass happrox hforecastGain hexcess input hinput
  intro g hg hlarge
  obtain ⟨W, G, hG, hc⟩ := hdetector g hg hlarge
  exact ⟨_, Or.inr ⟨W, G, hG, rfl⟩, hc⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_forecast_model
    {Ω T X Forecast : Type*} [Nonempty Forecast] [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p Q P q K C forecastCap εtail M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hQlarge : 2 * u + 4 * p + q + 20 ≤ Q)
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → integerBox N → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity
      (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (u : integerBox N) => W.eval N poly u.val))
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
      (forecastAugmentedUnitThreshold u p K C forecastCap) / 8)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  have hgain : Real.exp (-Q) ≤
      forecastAugmentedUnitThreshold u p K C forecastCap / (8 * (M + 1)) :=
    (Real.exp_le_exp.mpr (neg_le_neg hQlarge)).trans
      (forecastAugmentedUnitThreshold_atom_gain hu hp hq hK (zero_le_one.trans hC)
        hKp hCp hforecastCapP hM hMq)
  obtain ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff, herr, hforecasts, hterms⟩ :=
    exists_normalizedTwist_forecast_approximation N poly μ physical site hphysical slices tests
      w degree complexity forecast hK hC hforecastCap (Real.exp_pos p)
      (Real.exp_pos (-Q)) (Real.exp_pos (-(u + 3))) hsize htests hforecast
      hdetect Term coefficient atom hexpansionAtoms hM hmass happrox hgain hexcess input hinput
  have herror := forecastAugmented_model_error hu hp hQ hK hforecastCap (Real.exp_nonneg p)
    hKp hforecastCapP le_rfl (le_refl (Real.exp (-(u + 3)))) hP htail
  have hbudget := forecastAugmented_model_size hu hp hQ hK hC hforecastCap
    hKp hCp hforecastCapP
  exact ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff.trans hbudget.1,
    herr.trans herror, fun f => (hforecasts f).trans herror, hterms.trans hbudget.2⟩

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X Ω Forecast : Type*} [Fintype X]
variable {Term : Forecast → Type*} {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

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

theorem exists_fixedLaw_centered_forecast_twist_model (s : ℕ)
    {Ω T X Forecast : Type*} [Nonempty Forecast] [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (localBudget Pnative : ℝ) (hlocalBudget : 0 ≤ localBudget) (hPnative : 0 ≤ Pnative)
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (law : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p P massLog K C forecastCap εtail : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hmassLog : 0 ≤ massLog)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hP : u + 2 * p +
      max (max localBudget (3 * Pnative + 3)) (2 * u + 4 * p + massLog + 20) + 32 ≤ P)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm law site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) s localBudget
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-localBudget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ)
    (centerConstant : Forecast → ∀ j, J j → ℝ)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ Real.exp massLog)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i *
      (twists f i).eval N (fun j => subtractConstant (centerConstant f j) (poly j)) v.val‖ ≤
        Real.exp (-(2 * u + 4 * p + 12)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (law.siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Q := max commonBudget (2 * u + 4 * p + massLog + 20)
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) s commonBudget
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm law physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  intro commonBudget Q
  have hlocalCommon : localBudget ≤ commonBudget := le_max_left _ _
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans hlocalCommon
  obtain ⟨hQ, _, hcommonQ, hthreshold, hgain, _⟩ :=
    forecastAugmented_model_parameters hu hp hmassLog hcommon
  let shifted := fun f i => (twists f i).shiftConstant (centerConstant f)
  let atom := fun f i (v : integerBox N) => (shifted f i).eval N poly v.val
  have hatom (f) (i) : atom f i ∈
      twistedNativeSampleFunctions (1 : X → ℕ) s commonBudget
        (fun v : integerBox N => v.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) v => W.eval N poly v.val) :=
    centeredForecastTwist_mem_common_family localBudget Pnative hPnative
      twists N poly centerConstant f i
  have happrox' (f) (v : integerBox N) :
      ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
        forecastAugmentedUnitThreshold u p K C forecastCap / 8 := by
    have he := (happrox f v).trans (forecastAugmented_approximation_precision
      hu hp hK (zero_le_one.trans hC) hKp hCp hforecastCapP)
    change ‖forecast f v - ∑ i, coefficient f i *
      ((twists f i).shiftConstant (centerConstant f)).eval N poly v.val‖ ≤ _
    rw [centeredForecastTwist_sum_eq twists coefficient N poly centerConstant f v.val]
    exact he
  have hdetectCommon (signal : (X → ℤ) → ℂ)
      (hsignal : ∀ v, ‖signal v‖ ≤ 1)
      (hzero : ∀ v, v ∉ integerBox N → signal v = 0)
      (hlarge : forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm law site slices tests signal) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) s commonBudget
          (fun v : integerBox N => v.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun v => signal v.val)
          (fun v => star (W.eval N poly v.val) * G v)‖ := by
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero hlarge
    have he : Real.exp localBudget ≤ Real.exp commonBudget := Real.exp_le_exp.mpr hlocalCommon
    let W' := W.mono he he
      (show (⟨Real.exp localBudget, Real.exp_nonneg _⟩ : ℝ≥0) ≤
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩ from he)
    refine ⟨W', G, hG.map (fun model => model.mono hlocalCommon), ?_⟩
    exact hgain.trans ((Real.exp_le_exp.mpr (neg_le_neg hlocalCommon)).trans hc)
  exact exists_normalizedTwist_forecast_model N poly law
    physical site hphysical slices tests (1 : X → ℕ) s commonBudget forecast
    hu hp hQ hmassLog hK hC hforecastCap hKp hCp hforecastCapP hthreshold hP
    hsize htests hforecast hdetectCommon Term coefficient atom hatom
    (Real.exp_nonneg massLog) le_rfl hmass happrox' hexcess htail input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

attribute [instance] ActualForecastData.fintypeTerm

namespace ActualForecastData

variable (N : X → ℕ) (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (Pnative massLog capLog E : ℝ)

end ActualForecastData

variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ} {F : Type*}

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (points : Finset (C.Variables → ℤ))
    (hpoints : points.Nonempty)
    (hbox : points ⊆ integerBox (fun i : C.Variables => A.sides i.val))

noncomputable def retainedSite (u : points) : A.Site :=
  C.site u.val (hbox u.property)

@[simp] theorem retainedSite_val (u : points) :
    (C.retainedSite points hbox u).val = C.parameter u.val := rfl

@[simp] theorem physical_retainedSite (u : points) :
    A.physical C.path (C.retainedSite points hbox u) = C.physical u.val := rfl

@[simp] theorem retainedParameter_retainedSite (u : points) :
    C.retainedParameter (C.retainedSite points hbox u).val = u.val :=
  C.retainedParameter_parameter u.val

noncomputable def retainedLaw : FiniteProbabilityWeights A.Site :=
  (FiniteProbabilityWeights.uniformFinset points hpoints).finitePushforward
    (C.retainedSite points hbox)

theorem retainedLaw_complexMean_parameter
    (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    (C.retainedLaw points hpoints hbox).complexMean (fun site => f site.val) =
      𝔼 u ∈ points, f (C.parameter u) := by
  rw [retainedLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_complexMean _ _ (fun u => f (C.parameter u))

theorem retainedLaw_complexMean_physical (f : (X → ℤ) → ℂ) :
    (C.retainedLaw points hpoints hbox).complexMean
        (fun site => f (A.physical C.path site)) =
      𝔼 u ∈ points, f (C.physical u) :=
  C.retainedLaw_complexMean_parameter points hpoints hbox
    (fun x => f (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

noncomputable def siteLaw (z : out.retained) : FiniteProbabilityWeights A.Site :=
  (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw
    (out.slice z).integerPoints (out.dense z).nonempty
    (out.slice z).integerPoints_subset_integerBox

theorem siteLaw_complexMean_physical (z : out.retained) (f : (X → ℤ) → ℂ) :
    (out.siteLaw z).complexMean (fun site => f (A.physical z.val site)) =
      𝔼 u ∈ (out.slice z).integerPoints,
        f ((P.chart ⟨z.val, out.subset z.property⟩).physical u) := by
  have h := (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_complexMean_physical
    (out.slice z).integerPoints (out.dense z).nonempty
    (out.slice z).integerPoints_subset_integerBox f
  rw [P.chart_path] at h
  exact h

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem siteLaw_ambientPhysicalValue_score
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : out.retained) :
    ((out.siteLaw z).complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue ambient (A.physical z.val site)))).re =
      P.ambientScore ambient ⟨z.val, out.subset z.property⟩ (out.slice z).integerPoints := by
  rw [P.ambientScore_eq_physical hσ1 H hH hchart hsmall hp ambient
    ⟨z.val, out.subset z.property⟩ _ (out.inside z)]
  exact congrArg Complex.re (out.siteLaw_complexMean_physical z (fun x =>
    weight x * observable x (P.ambientPhysicalValue ambient x)))

theorem siteLaw_score (z : out.retained) :
    outputScore ≤ ((out.siteLaw z).complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue out.ambient (A.physical z.val site)))).re := by
  rw [out.siteLaw_ambientPhysicalValue_score hσ1 H hH hchart hsmall hp]
  exact out.score z

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateObservableRestriction
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def restrictObservable
    (newObservable : (X → ℤ) → D.Space → ℂ)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained,
      newScore ≤ (P.candidate ⟨z.val,hsub z.property⟩).score newObservable weight) :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked newObservable weight
      cost newMass newScore where
  productive := retained
  mass := hmass
  chart z := P.chart ⟨z.val,hsub z.property⟩
  chart_path z := P.chart_path ⟨z.val,hsub z.property⟩
  centerLift := P.centerLift
  chart_centerLift z := P.chart_centerLift ⟨z.val,hsub z.property⟩
  frozen_side z := P.frozen_side ⟨z.val,hsub z.property⟩
  candidate z := P.candidate ⟨z.val,hsub z.property⟩
  score := hscore

@[simp] theorem restrictObservable_physicalIntegerPoint
    (newObservable : (X → ℤ) → D.Space → ℂ)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained,
      newScore ≤ (P.candidate ⟨z.val,hsub z.property⟩).score newObservable weight) :
    (P.restrictObservable newObservable retained hsub hmass hscore).physicalIntegerPoint =
      P.physicalIntegerPoint := rfl

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

theorem exists_marked_topQuotientOrbit_lift_externalFamily_on
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace E.Space]
    {A : Type*} (K : ℝ≥0) (observable : A → D.RealGroup → ℂ) (allowed : A → Prop)
    (hrecovery : ∀ a, allowed a → ∀ source,
      positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K
        (observable a) (D.markedTopQuotientDiagram E φ Q source).2
          (D.markedTopQuotientDiagram E φ Q source).1 = observable a source)
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ a, allowed a → ∀ z : σ → ℝ,
        positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K (observable a)
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked))
          (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q)) =
        observable a (D.filtration.realification.polynomialOrbitRealEval w z g) := by
  obtain ⟨g, hg, hm, hdiagram⟩ :=
    D.exists_marked_topQuotientOrbit_lift_diagram E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro a ha z
  have h := hrecovery a ha (D.filtration.realification.polynomialOrbitRealEval w z g)
  rw [hdiagram z] at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem sides_pos (k : LayerSamplerVariables G I n B) : 0 < A.sides k := by
  cases k with
  | inl g => exact S.positive
  | inr j => exact allocatedPrincipalSides_pos B U b S j

include A in

theorem trimMargin_proper (x : X) : 2 * spatialTrimMargin τ N x < N x := by
  obtain ⟨base, hbase⟩ := A.bases_nonempty
  obtain ⟨a, ha, _⟩ := Finset.mem_image.mp hbase
  have hx := (mem_integerBox _ _).mp ha x
  omega

theorem physical_mem_integerBox (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) :
    A.physical z site ∈ integerBox N := by
  have hroot : (∑ k, |(site.val k : ℝ)|) ≤
      allocatedExternalCandidateRootBudget B U b S := by
    rw [allocatedExternalCandidateRootBudget_eq]
    exact allocatedParameterSite_sum_bound B U b S site
  exact jointIntegerPhysicalSite_mem_box site.val N (spatialTrimMargin τ N)
    (fun x => (A.trimMargin_proper x).le) A.widths
    (narrowTrimmedSpatialWidths_fit
      (allocatedExternalCandidateRootBudget_nonneg B U b S) A.trim_pos hξ1
      site.val hroot N A.size_pos) z

end AllocatedExternalCandidateSampler

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

namespace AllocatedExternalLocalChart

variable {A} {chartCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A chartCost)

theorem physical_mem_integerBox (hξ1 : ξ ≤ 1) (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) : C.physical u ∈ integerBox N := by
  rw [C.physical_eq_sampler u (C.slice.integerPoints_subset_integerBox hu)]
  exact A.physical_mem_integerBox hξ1 C.path _

end AllocatedExternalLocalChart

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
    (allowed : (X → ℤ) → Prop)
    (hphysical : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      allowed ((P.chart z).physical u))
    (hrecovery : ∀ x, allowed x → ∀ source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)

include hσ1 H hH hchart hsmall hp hphysical hrecovery in

theorem refilteredQuotientCandidate_score_eq_frozen_on (z : P.productive) :
    ((middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF).score
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight = P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z := by
  unfold AllocatedExternalLocalCandidate.score refilteredFrozenScore
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  congr 1
  rw [AllocatedExternalLocalCandidate.topQuotient_value]
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  have hmark := (middle z).mark_on_slice u hu
  rw [htags] at hmark
  have hr := hrecovery ((P.chart z).physical u) (hphysical z u hu)
    (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)
  simp only [RationalFilteredNilmanifold.markedTopQuotientDiagram, hmark] at hr
  exact hr

variable {frozenScoreThreshold : ℝ}
    (hscore : ∀ z : P.productive, frozenScoreThreshold ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z)

noncomputable def refilteredQuotientScoredProblem_on :
    AllocatedExternalCandidateProblem (E := E) A Q QF.filtration
      (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit QF hQF markedMiddle)
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight cost massThreshold frozenScoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF
  score z := by
    rw [P.refilteredQuotientCandidate_score_eq_frozen_on A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle allowed hphysical hrecovery z]
    exact hscore z

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

include hmarkFactor in

theorem conclusion_of_refilteredQuotientScored_on
    (db : Basis ι ℚ L) (dw : ι → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (db '' {i | j ≤ dw i}))
    (fb : Basis κ ℚ M) (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (fb '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis db dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.refilteredQuotientScoredProblem_on A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle allowed hphysical hrecovery hscore).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  have hcompat : Dref.topQuotientMarkedOrbit Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF lower.ambient =
      Fref.topQuotientOrbit QF hQF markedMiddle := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact lower.marked
  obtain ⟨ambientMiddle, _, hmarkedMiddle, hevalMiddle⟩ :=
    Dref.exists_marked_topQuotientOrbit_lift_externalFamily_on Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right) allowed hrecovery
      (D.refilteredMarkedMap_layer_surjective Fmark φ hφ W Dref hDref Fref hFref
        db dw hdb fb fw hfb hW hsurj)
      lower.ambient markedMiddle hcompat
  let candidate := D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
  obtain ⟨restored, hmark, _, hkeep⟩ :=
    D.filtration.exists_formal_marked_orbit_restoration Fmark.filtration φ hφ
      fb fw hfb hsurj (fullTaggedVariableWeight (X := X) J) candidate marked
  have hretained (z : P.productive) (u : (P.chart z).Variables → ℤ)
      (hu : u ∈ (P.chart z).slice.integerPoints) :
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) restored =
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) candidate := by
    have hk := hkeep (fun i => ((P.chart z).chartValues u i : ℝ)) (by
      simpa only [polynomialOrbitRealEval_integer] using
        P.refilteredScoredAssembly_mark_on_slice A Fmark φ hφ W Dref hDref Fref left right
          markedMiddle middle hmarkFactor ambientMiddle hmarkedMiddle z u hu)
    simpa only [polynomialOrbitRealEval_integer] using hk
  refine ⟨{
    ambient := restored
    marked := hmark
    retained := lower.retained
    subset := lower.subset
    mass := lower.mass
    step := lower.step
    step_pos := lower.step_pos
    slice := lower.slice
    dense := lower.dense
    inside := lower.inside
    score := ?_
  }⟩
  intro z
  apply (lower.score z).trans_eq
  unfold ambientScore
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  let zp : P.productive := ⟨z.val, lower.subset z.property⟩
  have huOriginal : u ∈ (P.chart zp).slice.integerPoints := lower.inside z hu
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp zp u huOriginal
  change weight ((P.chart zp).physical u) *
      P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K
        ((P.chart zp).physical u)
        (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P.chart zp).chartValues u) lower.ambient)) =
    weight ((P.chart zp).physical u) * observable ((P.chart zp).physical u)
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((P.chart zp).chartValues u) restored))
  congr 1
  rw [hretained zp u huOriginal]
  have ha := D.externalCandidateOrbit_realEval W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at ha
  change _ = observable ((P.chart zp).physical u)
    (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      ((P.chart zp).chartValues u) (D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle)))
  rw [ha]
  have hr := hevalMiddle ((P.chart zp).physical u) (hphysical zp u huOriginal)
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hr
  simpa only [refilteredQuotientObservable, refilteredFrozenObservable, ← htags] using hr

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end


