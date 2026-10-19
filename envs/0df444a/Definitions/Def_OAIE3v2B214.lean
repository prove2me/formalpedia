-- Prove2me | Definitions.Def_OAIE3v2B214
-- name    : OAIE3v2B214
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:08:11.138625+00:00
-- url     : https://prove2.me/theorems/ec4ed448-4a03-4e27-8af3-5b1e82189369
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 218 of 311
-- statement:
--   Definitions bundle 218 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B188`, `OAIE3v2B191`, `OAIE3v2B193`, `OAIE3v2B194`, `OAIE3v2B195` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateExponentialFreezingBudget.lean`, `Dynamics/AllocatedSlicedFactorBudget.lean`, `Dynamics/PreparedModularCanonicalDetectorPeriodBudget.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedSlicedNormalizedNativeModel.lean`, `Estimates/AllocatedSlicedRowsProjectedSource.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NormalizedTwistNativeApproximation.lean`, `Estimates/NormalizedTwistNativeMembership.lean`, `Estimates/QuadraticCyclicAntisymmetric.lean`, `Estimates/SampledNativeModel.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Geometry/AllocatedAmbientBoxTests.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Linear/AllocatedCanonicalSlicedConstructedProjection.lean`, `Linear/AllocatedExternalCandidateNormalizedKernelRestoration.lean`, `Linear/AllocatedFixedDensityProjection.lean`, `Nilpotent/PolynomialPatchWeightedChartNiltest.lean`, `Sampling/ActualForecastDataNativeProductBudget.lean`, `Sampling/AllocatedExternalCandidateFreezingScoreBudget.lean`, `Sampling/AveragedNormalizedTwistForecastJointModel.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B195

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_sampled_native_model {Ω T X σ I : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (w : σ → ℕ) (degree : ℕ) (complexity : ℝ) (sample : X → σ → ℤ)
    (twist : I → X → ℂ) (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 (K * (2 * C) / tau) ≤ sampledSliceSeminorm μ F slices tests g →
      ∃ (i : I) (G : X → ℂ), Nonempty (NativeSampleModel w degree complexity sample G) ∧
        beta ≤ ‖r.correlation g (fun x => star (twist i x) * G x)‖)
    (hexcess : r.excessMass (μ.siteLaw F) C ≤ ε)
    (b : X → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (e : X → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity sample twist) ∧
      b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ F slices tests e ≤ 2 * tau + 2 * K * (B + 2 / beta) * ε ∧
      (n : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let atoms := twistedNativeSampleFunctions w degree complexity sample twist
  let cap := max 1 (K * (2 * C) / tau)
  have hcap : 1 ≤ cap := le_max_left _ _
  have hdetector (g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ K * (2 * C) / tau)
      (hlarge : tau / B ^ 2 ≤ sampledSliceSeminorm μ F slices tests g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    have hunit (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
        (hX : (tau / B ^ 2) / cap ≤ sampledSliceSeminorm μ F slices tests v) :
        ∃ Q ∈ atoms, beta ≤ ‖r.correlation v Q‖ := by
      obtain ⟨i, G, hG, hcorr⟩ := hdetect v hv hX
      exact ⟨_, Or.inr ⟨i, G, hG, rfl⟩, hcorr⟩
    obtain ⟨Q, hQ, hc⟩ := detector_of_unit_detector r
      (sampledSliceSeminorm μ F slices tests) atoms (lt_of_lt_of_le zero_lt_one hcap)
      hunit g (fun x => (hg x).trans (le_max_right _ _)) hlarge
    have hscale : beta ≤ cap * beta := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap hbeta.le
    exact ⟨Q, hQ, hscale.trans hc⟩
  exact exists_sampled_slice_model μ F slices tests r hr
    (twistedNativeSampleFunctions_balanced twist) ⟨0, twistedNativeSampleFunctions_zero twist⟩
    (fun Q hQ x => twistedNativeSampleFunctions_norm twist htwist hQ x)
    hK hC hB hbeta htau hsize htests hdetector hexcess b hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest
namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct

theorem exists_mass_bounded_patch_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} {d : ℕ} (P : PolynomialPatch X s d)
      [Fintype (PolynomialShearIndex P.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      (M : ℝ≥0) (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (M : ℝ) ≤ p → (P.kernel.lip : ℝ) ≤ Real.exp p →
      (P.shearNiltest M hP).ComplexityLE ((p + 2) ^ C) := by
  obtain ⟨a, ha, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_shear_parameter_budget s a
  refine ⟨C, hC, ?_⟩
  intro X d P _ _ _ _ _ M hP p hp hd hMp hLip
  let D := Fintype.card (PolynomialShearIndex P.weight)
  have hD : D ≤ d * (d + 1) ^ s := by
    simpa only [Fintype.card_fin] using polynomialShearIndex_card_le P.weight s
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (P.weight_pos i)) P.weight_le
  obtain ⟨t, ht, hgeom, htotal⟩ := hbudget d D M p hp M.coe_nonneg hMp hd hD
  have hDt : (D : ℝ) ≤ t := by
    have hle : D ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHt : ((2 * s + 1 : ℕ) : ℝ) ≤ t := by
    have hle : 2 * s + 1 ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHexp : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp t :=
    hHt.trans (by linarith [Real.add_one_le_exp t])
  have hClog := hlog D (2 * s + 1) t ht hDt hHexp
  have hv : 0 ≤ (t + a) ^ a + 1 := by positivity
  have hObs := shearObservable_log_bound P M hp hv hLip hClog
  have hK := shearKernelLogBudget_nonneg s d M.coe_nonneg hp
  have hT := shearActionLogBudget_nonneg s d M.coe_nonneg
  have htP : t ≤ (p + 2) ^ C := by
    linarith [pow_nonneg (by positivity : 0 ≤ t + a) a]
  apply P.shearNiltest_complexity M hP
  · exact RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (polynomialShearNilmanifold P.weight s P.weight_le)
      (polynomialShearNilmanifold_complexity_budget P.weight s
        (fun i => lt_of_lt_of_le Nat.zero_lt_one (P.weight_pos i)) P.weight_le)
      (hgeom.trans htP)
  · linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem cyclicNativeInverse_one : CyclicNativeInverse 1 2 := by
  intro N _ p hp f hf hG
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_gowers_two f hf
  obtain ⟨T, hTn, hTc, hTeval⟩ := exists_cyclic_character_niltest χ
  have h12 : (12 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have h2p : 2 * p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hcorr : Real.exp (-(2 * p)) ≤ ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ gowersNorm 2 f ^ 2 := pow_le_pow_left₀ (Real.exp_nonneg _) hG 2
      _ ≤ _ := hχ
  let F : NativeCyclicModel 1 N ((p + 2) ^ 2) (fun x => χ x) := {
    L := RationalTorus.Algebra 1
    dim := 1
    model := RationalTorus.nilmanifold 1
    test := T
    norm := hTn
    complexity := hTc.mono h12
    eval := fun x => (hTeval x).symm }
  exact ⟨fun x => χ x, ⟨F⟩, (Real.exp_le_exp.mpr (neg_le_neg h2p)).trans hcorr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicAntisymmetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_phase_aligned_derivatives (f : G → ℂ) (g : G → G → ℂ) :
    ∃ c : G → ℂ, (∀ h, ‖c h‖ = 1) ∧
      (𝔼 h, 𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) =
        ((𝔼 h, ‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖ : ℝ) : ℂ) := by
  choose c hc hphase using fun h =>
    exists_complex_unit_phase (𝔼 n, multiplicativeDerivative f h n * star (g h n))
  refine ⟨c, hc, ?_⟩
  have heq (h : G) : (𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) =
      (‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖ : ℂ) := by
    rw [← hphase h, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    simp only [star_mul, star_star]
    ring
  simp_rw [heq]
  simp [Fintype.expect_eq_sum_div_card]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistNativeApproximation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_native_approximation
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
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
    {K C cap beta tau εtail : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hcap : 0 < cap)
    (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
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
        2 * tau + 2 * K * (cap + 2 / beta) * εtail ∧
      (nterms : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let : Nonempty (integerBox N) := (integerBox_nonempty N).to_subtype
  have htwist (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) : ‖W.eval N poly u.val‖ ≤ 1 := W.norm_eval_le N poly u.val
  have hdetector (g : integerBox N → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1)
      (hlarge : (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
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
  exact exists_sampled_native_model μ physical slices tests
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)) hr
    w degree complexity (fun u : integerBox N => u.val)
    (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) => W.eval N poly u.val)
    htwist hK hC hcap hbeta htau hsize htests hdetector hexcess input hinput

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_derivative_correlators {s C N : ℕ} [NeZero N]
    (hI : CyclicNativeInverse s C) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-derivativeInverseBudget s p) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∃ (g : {h // h ∈ H} → ZMod N → ℂ)
        (_F : ∀ h, NativeCyclicModel s N ((derivativeInverseBudget s p + C) ^ C) (g h)),
        ∀ h, Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g h x)‖ := by
  classical
  obtain ⟨H, hH, hdense, hlarge⟩ := exists_many_large_gowers_derivatives s f hf hp hG
  have hchoose (h : {h // h ∈ H}) :
      ∃ g ∈ nativeCyclicFunctions s N ((derivativeInverseBudget s p + C) ^ C),
        Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g x)‖ :=
    hI (derivativeInverseBudget_ge_two s hp) (multiplicativeDerivative f h.val)
      (multiplicativeDerivative_norm_le_one f hf h.val) (hlarge h.val h.property)
  choose g hg hcorr using hchoose
  exact ⟨H, hH, hdense, g, (fun h => Classical.choice (hg h)), hcorr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedDensityProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

open BooleanCubeKernel

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)

theorem allocatedPhysicalCube_site_le_exp {q : ℕ}
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q)
      (allocatedPrincipalSides B U basis S))
    {P : ℝ} (hroot : allocatedPhysicalRootBudget B U basis S c ≤ Real.exp P)
    (hL : (S.value : ℝ) ≤ Real.exp P) (s : Finset (Fin q)) (k : LayerSamplerVariables G I n B) :
    |((affineSite (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) s (some k) : ℤ) : ℝ)| ≤
      Real.exp (P + (q + 2 : ℕ)) := by
  have hs : (s.card : ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q from by simpa only [Fintype.card_fin] using s.card_le_univ)
  have hd (i) : |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ Real.exp P :=
    (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans hL
  have hr : |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ Real.exp P :=
    (allocatedPhysicalCube_root_budget B U basis S c x y k).trans hroot
  have hsum : |∑ i ∈ s, (allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤
      (q : ℝ) * Real.exp P := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ s, Real.exp P := Finset.sum_le_sum (fun i _ => hd i)
      _ = (s.card : ℝ) * Real.exp P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg P)
  calc
    _ ≤ Real.exp P + (q : ℝ) * Real.exp P := by
      simp only [affineSite, Int.cast_add, Int.cast_sum]
      exact (abs_add_le _ _).trans (add_le_add hr hsum)
    _ ≤ Real.exp ((q : ℝ) + 2) * Real.exp P := by
      have hq : (q : ℝ) + 1 ≤ Real.exp ((q : ℝ) + 2) := by
        linarith [Real.add_one_le_exp ((q : ℝ) + 2)]
      nlinarith [Real.exp_pos P]
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem narrowPhysicalSiteMap_cast {G J X T : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (root : T → G ⊕ J → ℤ) (hroot : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W)
    (z) (t) :
    (fun i => ((narrowPhysicalSiteMap hW hτ hξ N hN hmargin root hroot z t).val i : ℝ)) =
      (fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val :=
  jointIntegerPhysicalSite_cast (root t) (z.1.val, z.2.val)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_oneSite_domination (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ),
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
    ∀ (φ : (X → ℝ) → ℝ), (∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) →
      (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
        (φ (fun i => (base i : ℝ) + physicalAffineSite root z i) * density base z)) ≤
      (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) *
        (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
          φ (fun i => (base i : ℝ) + physicalAffineSite root z i)) +
        3 * positiveProjectionAccuracy P := by
  obtain ⟨A₀, _, hcompare⟩ := exists_affine_oneSite_density_comparison m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hfiber (root : LayerSamplerVariables G I n B → ℤ) (y) :=
    allocatedCoefficientDensity_fiber_cap B U basis hb o hR hσ S (fun j => (V j : ℝ))
      (fun j => (V j).coe_nonneg) (fun j => (hV j).2) μ ν hσ1 Cinv hCinv hchart hsmall root y
  have hlocal (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
      (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
      (φ : (X → ℝ) → ℝ) (hφ : ∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
      (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
        (φ (fun i => (base i : ℝ) + physicalAffineSite root z i) * density base z)) ≤
      (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) *
        (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
          φ (fun i => (base i : ℝ) + physicalAffineSite root z i)) +
        3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    let ψ : (X → ℝ) → ℂ := fun v => (φ (fun i => (base i : ℝ) + v i) : ℂ)
    have hψ (v) : ‖ψ v‖ ≤ 1 := by
      dsimp only [ψ]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ _).1]
      exact (hφ _).2
    obtain ⟨hZ, he⟩ := hcompare hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      root (fun i => Fin.elim0 i) (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
      (fun s k => by
        have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
        simpa [affineSite, hs] using (hroot k).trans hExp)
      frequency (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank)
      0 (by simp) (fun _ => ψ) (fun _ v => hψ v) T hT widths hwidths hwidthLower
      (allocatedCoefficientDensity B U basis hb o hR hσ S) (fun y => (hfiber root y).1)
      hη.le (fun y => by simpa only [norm_sub_rev] using happ y)
    simp only [layeredSiteWeight_physical, ψ] at he
    have hbound := selectedResidueSmoothPMF_test_le_of_complex stride T widths hwidths hZ
      (density base)
      (fun z => coefficientFiberAverage U μ root (allocatedCoefficientDensity B U basis hb o hR hσ S)
        (coefficientEvaluationTorus U root (affineSampleCoefficientTorus U (pa base) (hma base)
          (fun k i => (z (k, i) : ℝ)))))
      (fun z => φ (fun i => (base i : ℝ) + physicalAffineSite root z i))
      (fun z => (hfiber root _).2.2) (fun z => (hφ _).1) he
    refine ⟨hZ, hbound.trans_eq ?_⟩
    ring
  obtain ⟨hZ, _⟩ := hlocal 0 0 (by intro k; simpa using (Real.exp_nonneg P))
    (fun _ => 0) (fun _ => by simp)
  refine ⟨hwidths, hZ, ?_⟩
  intro base root hroot φ hφ
  exact (hlocal base root hroot φ hφ).choose_spec

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))

noncomputable def allocatedSlicedTupleValue
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) : ℂ :=
  (𝔼 base ∈ bases, ∑' z,
    ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
      (physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
        (baseDensity base z : ℂ))) /
    (selectedJointDensityMass bases stride cells widths baseDensity : ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "Z" => selectedJointDensityMass bases stride cells widths baseDensity

include hbases in
omit [DecidableEq G] [∀ index, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedTupleValue_select_base
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin dim) (allocatedPrincipalSides B U b S)))
    (f : (X → ℤ) → ℂ) {κ : ℝ}
    (hsource : κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f)).re) :
    ∃ base ∈ bases,
      κ ≤ (law.complexMean (fun y => ∑' z,
        ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U b S x y) base z) * (baseDensity base z : ℂ))) /
        (Z : ℂ)).re := by
  let value := fun base => law.complexMean (fun y => ∑' z,
    ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
      (physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) * (baseDensity base z : ℂ))) / (Z : ℂ)
  have hmean : law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f) = 𝔼 base ∈ bases, value base := by
    simp only [allocatedSlicedTupleValue, FiniteProbabilityWeights.complexMean_div,
      FiniteProbabilityWeights.complexMean_finset_expect, Finset.expect_div, value]
  rw [hmean, ← FiniteProbabilityWeights.uniformFinset_complexMean bases hbases value] at hsource
  obtain ⟨base, _, hbase⟩ := (FiniteProbabilityWeights.uniformFinset bases hbases).exists_positive_weight_ge_complexMean_re
    (fun base => value base.val)
  exact ⟨base.val, base.property, hsource.trans hbase⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

noncomputable def allocatedRecenteredSpatialTwist (r : labels)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
    (t : terms) (s : Finset (Fin dim)) (u : X → ℤ) : ℂ :=
  physicalResidueSpatialSiteFactor
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r))
    (allocatedPhysicalCubeDirections B U b S x (wholeReference r)) base
    (boundedColumnResidueRepresentative q a) q 4 mesh (trimmedSpatialRootScale τ N q) t s u

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistNativeMembership
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem normalizedTwist_eval_mem_twistedNativeSampleFunctions
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) {budget : ℝ} (hbudget : 2 ≤ budget) :
    (fun t => W.eval N poly (sample t)) ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        V.eval N poly (sample t)) := by
  refine Or.inr ⟨W.conjugate, fun _ => 1, ⟨NativeSampleModel.constOne hbudget⟩, ?_⟩
  funext t
  simp only [NormalizedPolynomialTwist.conjugate_eval, star_star, mul_one]

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorPeriodBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_canonicalSlicedModelPrefactor_budget (m dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Fin m → Type*} [∀ j, Fintype (I j)]
      {n : Fin m → ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
      {P Pnum Pk : ℝ}, 0 ≤ P → Pnum ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
        Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))
      Fmodel ∈ Set.Icc 0 ((P + C) ^ C) := by
  let rows : ℕ := ∑ j : Fin m,
    Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let poly := Polynomial.C (m * 2 ^ dim) * (X + 8) * (1 + 4 * X) +
    X * (Polynomial.C (m * 2 ^ (m + 1)) * X) +
    X * (Polynomial.C rows * (Polynomial.C (m + 1) * X))
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro I _ n Q _ P Pnum Pk hP hPnum hPk haxes hQ Fmodel
  have hnum : 0 ≤ Pnum := hPnum.1
  have hk : 0 ≤ Pk := hPk.1
  have hsum : (∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
      (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))) ≤
      P * (rows * ((m + 1 : ℕ) * P)) := by
    calc
      _ ≤ ∑ j : Fin m, P *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * P)) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
        exact hPk.2
      _ = _ := by
        simp only [rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hF : Fmodel ≤ (m * (2 : ℝ) ^ dim) * (P + 8) * (1 + 4 * P) +
      P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * ((m + 1 : ℕ) * P)) := by
    dsimp only [Fmodel]
    simp only [Fintype.card_fin]
    apply add_le_add _ hsum
    gcongr
    exact hPnum.2
    exact hPnum.2
    exact hPk.2
  refine ⟨by dsimp only [Fmodel]; positivity, hF.trans ?_⟩
  simpa [poly, X, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

def allocatedActualPrimeBad (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∃ hp : p ∈ P, letI : NeZero p := inferInstanceAs (NeZero (⟨p, hp⟩ : P).val)
    allocatedActualModulusBad inactive spatial kernel block C (p ^ a) f

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_exp_densityLoss (k : ℕ) {b t : ℝ} (hb : 0 ≤ b) :
    Real.log ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) / Real.exp (-t)) =
      Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + t := by
  rw [max_eq_right (Real.one_le_exp_iff.mpr hb),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity : (4 * Real.exp b * Real.exp b : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity : (4 * Real.exp b : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
    Real.log_exp, Real.log_exp]
  ring

theorem finiteFreezing_exp_cost_le (k : ℕ) {cost densityCost p b t : ℝ}
    (hcost : cost ≤ p) (hdensity : densityCost ≤ p) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    max cost (densityCost + Real.log
      ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) / Real.exp (-t))) ≤
      p + Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + t := by
  rw [finiteFreezing_exp_densityLoss k hb]
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hk : 0 ≤ Real.log (k + 1 : ℝ) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg k))
  apply max_le <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedSlicedFactorBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped Classical NNReal

theorem exists_allocatedSlicedFactor_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G X K Y : Type*} [Fintype G] [Fintype X] [Fintype K]
      [PseudoMetricSpace Y] (selection : Fin dim ↪ G)
      {M modulus : ℕ} {p E analytic : ℝ},
      0 ≤ p → 0 ≤ E → 0 ≤ analytic →
      (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p → ((dim + 1 : ℕ) : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      ∀ (r : ℝ≥0), (r : ℝ) = allocatedEarlyRecenteredMesh X selection M modulus p E →
      ∀ (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
        (residue : Option K × X → ℤ) (stride N : X → ℕ) {τ : ℝ},
      (∀ i, 0 < N i) → (∀ i, 0 < stride i) → 0 < τ → 1 / τ ≤ Real.exp p →
      ∀ (t : X → SpatialSiteLabel (Fin dim) modulus 4 r) (site : Finset (Fin dim))
        (F : Y → ℂ) {L : ℝ≥0}, LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) → (L : ℝ) ≤ Real.exp analytic →
      (∀ v, ‖physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N r t site F v‖ ≤ 1) ∧
      LipschitzWith ⟨Real.exp ((p + E + analytic + A) ^ A), Real.exp_nonneg _⟩
        (physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N r t site F) := by
  obtain ⟨a, ha, hmeshBudget⟩ := exists_allocatedEarlyRecenteredMesh_budget m dim
  let poly : Polynomial ℕ := 4 * Polynomial.X + 3 * (Polynomial.X + Polynomial.C a) ^ a + 27
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro G X K Y _ _ _ _ selection M modulus p E analytic hp hE hanalytic hG hX hdim hM hMP hmod
    r hrEq root D base residue stride N τ hN hstride hτ hτexp t site F L hF hFb hL
  obtain ⟨hr, _, hri, _⟩ := hmeshBudget X selection hp hE hG hX hM hMP hmod
  rw [← hrEq] at hr hri
  let P := (p + E + a) ^ a + 4
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hfourP : (4 : ℝ) ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_left (pow_nonneg (by positivity) _)
  have hbox : (4 : ℝ) ≤ Real.exp P := (by linarith [Real.add_one_le_exp (4 : ℝ)] : (4 : ℝ) ≤ Real.exp 4).trans
    (Real.exp_le_exp.mpr hfourP)
  have hinv : 1 / (r : ℝ) ≤ Real.exp P := by
    rw [one_div]
    exact hri.trans (Real.exp_le_exp.mpr (by dsimp only [P]; linarith))
  have hpExp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hframe : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.add_comm] using hdim.trans hpExp
  have hnorm := physicalSpatialAnalyticContinuous_bounds root D base residue stride N r t site F
    hN hstride hτ hr hF hFb hP hbox hinv (hX.trans hpExp) hframe hτexp
  refine ⟨hnorm.1, hnorm.2.weaken ?_⟩
  apply NNReal.coe_le_coe.mp
  change Real.exp (p + p + (3 * P + 6) + (p + 8)) + (L : ℝ) ≤ _
  let B := p + p + (3 * P + 6) + (p + 8)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : Real.exp B + (L : ℝ) ≤ Real.exp (B + analytic + 1) := by
    have h1 : Real.exp B ≤ Real.exp (B + analytic) := Real.exp_le_exp.mpr (by linarith only [hanalytic])
    have h2 : (L : ℝ) ≤ Real.exp (B + analytic) := hL.trans
      (Real.exp_le_exp.mpr (by linarith only [hB]))
    calc
      _ ≤ 2 * Real.exp (B + analytic) := by linarith only [h1, h2]
      _ ≤ Real.exp 1 * Real.exp (B + analytic) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply hsum.trans (Real.exp_le_exp.mpr ?_)
  let R := p + E + analytic
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpow : (p + E + a) ^ a ≤ (R + a) ^ a :=
    pow_le_pow_left₀ (by positivity) (by dsimp only [R]; linarith only [hanalytic]) _
  have hb : B + analytic + 1 ≤ poly.eval₂ (Nat.castRingHom ℝ) R := by
    simp [poly, Polynomial.eval₂_pow]
    change B + analytic + 1 ≤ 4 * R + 3 * (R + (a : ℝ)) ^ a + 27
    dsimp only [B, P, R] at *
    linarith only [hpow, hp, hE, hanalytic]
  exact hb.trans (hpoly R hR)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedNormalizedNativeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocatedRecenteredFactor_normalization (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
      {J : Fin m → Type*} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
      {X Y : Type*} [Fintype X] [PseudoMetricSpace Y]
      (selection : Fin dim ↪ G) {M modulus : ℕ} [NeZero modulus]
      {p E analytic : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ analytic →
      (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p → ((dim + 1 : ℕ) : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      ∀ (r : ℝ≥0), (r : ℝ) = allocatedEarlyRecenteredMesh X selection M modulus p E →
      ∀ (stride N : X → ℕ) {τ : ℝ},
      (∀ i, 0 < N i) → (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp p) →
      0 < τ → 1 / τ ≤ Real.exp p →
      ∀ (wholeReference :
        (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
          PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
        (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
        (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride))
        (cell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)
        (t : X → SpatialSiteLabel (Fin dim) modulus 4 r) (site : Finset (Fin dim))
        (F : Y → ℂ) {L : ℝ≥0}, LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) → (L : ℝ) ≤ Real.exp analytic →
      0 < residueRefinedPeriod modulus stride ∧
      (residueRefinedPeriod modulus stride : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * p + Fintype.card X * p) ∧
      ∃ (mask : (X → ZMod (residueRefinedPeriod modulus stride)) → ℂ)
        (H : (X → ℝ) × Y → ℂ),
        (∀ z, ‖mask z‖ ≤ 1) ∧ (∀ v, ‖H v‖ ≤ 1) ∧
        LipschitzWith ⟨Real.exp ((p + E + analytic + A) ^ A), Real.exp_nonneg _⟩ H ∧
        ∀ (u : X → ℤ) (y : Y),
          allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus stride wholeReference x N r base label cell t site u * F y =
            mask (fun i => (u i : ZMod (residueRefinedPeriod modulus stride))) * H (fun i => (u i : ℝ) / N i, y) := by
  obtain ⟨A, hA, hfactor⟩ := exists_allocatedSlicedFactor_budget m dim
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S X Y _ _ selection M modulus _ p E analytic hp hE ha hG hX hdim
    hM hMP hmodulus r hr stride N τ hN hs hsP hτ hτP wholeReference x base label cell t site F L hF hFb hL
  let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
  let dirs := allocatedPhysicalCubeDirections B U b S x (wholeReference label)
  let residue := boundedColumnResidueRepresentative stride cell
  let hdiv := stride_mul_dvd_residueRefinedPeriod modulus stride
  let mask := physicalResidueSpatialMaskMod root dirs base residue stride 4 r hdiv t site
  let H := physicalSpatialAnalyticContinuous (τ := τ) root dirs base residue stride N r t site F
  have hmod : (modulus : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * p) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp p) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
      _ = _ := (Real.exp_nat_mul _ _).symm
  obtain ⟨hHb, hHL⟩ := hfactor selection hp hE ha hG hX hdim hM hMP hmodulus r hr root dirs base residue stride N
    hN hs hτ hτP t site F hF hFb hL
  refine ⟨residueRefinedPeriod_pos (Nat.pos_of_ne_zero (NeZero.ne modulus)) stride hs,
    residueRefinedPeriod_exp_bound modulus stride hmod hsP, mask, H,
    physicalResidueSpatialMaskMod_norm root dirs base residue stride 4 r hdiv t site, hHb, hHL, ?_⟩
  intro u y
  exact physicalSpatialAnalytic_normalized root dirs base residue stride N r t site F hN hdiv u y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalSlicedConstructedProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

def AllocatedSlicedSourceProjection {m q : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (d : ℕ)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U (fun j => {t : Finset (Fin q) // t ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}) → ℝ)
    (Asample : ℕ) (P : ℝ) : Prop :=
    ∀ {W : ℝ}, 1 ≤ P → ∀ (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + Asample) ^ Asample) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + Asample) ^ Asample) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let Z := selectedJointDensityMass bases stride T widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X p hm)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
      (|Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
      ∀ (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))) (signal : (X → ℤ) → ℂ),
      (∀ v, ‖signal v‖ ≤ 1) → ∀ {κ : ℝ},
      κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X p hm
        N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
      ∃ base ∈ bases,
        let projected := fun y => ∑' z,
          ((selectedResidueSmoothPMF stride T widths
            (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass z).toReal : ℂ) *
            (physicalCubeSiteTest (integerSelfSiteTest q signal) (physicalCubeRootDifferences
              (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U b S x y) base z) *
            (g y (physicalCubeRowSample U d (fun j =>
              (Subtype.val : {t : Finset (Fin q) // t ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} → Finset (Fin q))) p hm
              (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
                (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
        κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateNormalizedKernelRestoration
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exp_neg_add_two_le_half (p : ℝ) :
    Real.exp (-(p+2)) ≤ Real.exp (-p)/2 := by
  have hlog : Real.log (2 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  calc
    _ ≤ Real.exp (-p-Real.log 2) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem kernel_restoration_exp_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ 3*p+2 ∧
    Real.exp (-(3*p+2)) ≤ Real.exp (-p)/(2*Real.exp p)*Real.exp (-p) ∧
    Real.exp (-(3*p+2)) ≤ Real.exp (-p)/2 := by
  have hmass : Real.exp (-p)/(2*Real.exp p)*Real.exp (-p) = Real.exp (-(3*p))/2 := by
    rw [mul_comm (2 : ℝ) (Real.exp p), div_mul_eq_div_div, ← Real.exp_sub,
      div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  refine ⟨by linarith only [hp], ?_, ?_⟩
  · rw [hmass]
    exact exp_neg_add_two_le_half (3*p)
  · exact (Real.exp_le_exp.mpr (by linarith only [hp] : -(3*p+2) ≤ -(p+2))).trans
      (exp_neg_add_two_le_half p)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateFreezingScoreBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_exp_weighted_error_le
    {B C b q e : ℝ} (hC : 0 ≤ C)
    (hBbound : B ≤ Real.exp b) (hCbound : C ≤ Real.exp b)
    (he : 2 * b + q + Real.log 8 ≤ e) :
    B * (C * Real.exp (-e)) ≤ Real.exp (-q) / 8 := by
  have hprod : B * C ≤ Real.exp b * Real.exp b :=
    mul_le_mul hBbound hCbound hC (Real.exp_nonneg _)
  calc
    B * (C * Real.exp (-e)) = (B * C) * Real.exp (-e) := (mul_assoc _ _ _).symm
    _ ≤ (Real.exp b * Real.exp b) * Real.exp (-e) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Real.exp (2 * b - e) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-q - Real.log 8) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-q) / 8 := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 8)]

theorem finiteFreezing_exp_score_surplus
    {Bweight Bobs Lip b q e t scoreThreshold : ℝ}
    (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : Bweight ≤ Real.exp b) (hobs : Bobs ≤ Real.exp b)
    (hlip : Lip ≤ Real.exp b)
    (he : 2 * b + q + Real.log 8 ≤ e)
    (ht : 2 * b + q + Real.log 8 ≤ t)
    (hscore : Real.exp (-q) ≤ scoreThreshold) :
    Real.exp (-q) / 2 + Bweight * (Lip * Real.exp (-e)) +
      (Bweight * Bobs) * Real.exp (-t) < scoreThreshold := by
  have herror := finiteFreezing_exp_weighted_error_le hLip hweight hlip he
  have hdiscard := finiteFreezing_exp_weighted_error_le hBobs hweight hobs ht
  rw [← mul_assoc] at hdiscard
  have hpos := Real.exp_pos (-q)
  linarith

theorem finiteFreezing_exp_half_score_le {q recursionParameter : ℝ}
    (hparameter : q + Real.log 2 ≤ recursionParameter) :
    Real.exp (-recursionParameter) ≤ Real.exp (-q) / 2 := by
  calc
    _ ≤ Real.exp (-q - Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end Erdos3.VectorPolynomial

end

end OAI
end


