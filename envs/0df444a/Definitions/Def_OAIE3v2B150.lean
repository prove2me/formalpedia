-- Prove2me | Definitions.Def_OAIE3v2B150
-- name    : OAIE3v2B150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:19:47.068611+00:00
-- url     : https://prove2.me/theorems/c4dc496b-c83e-4d03-8fd4-a85020820b74
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 152 of 311
-- statement:
--   Definitions bundle 152 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B130`, `OAIE3v2B131`, `OAIE3v2B136`, `OAIE3v2B137`, `OAIE3v2B138`, `OAIE3v2B139` of this split.
--
--   Modules: `Dynamics/JointExceptionalGainBudget.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/ConstantCenterUniformLifts.lean`, `Estimates/FixedPatchFunction.lean`, `Estimates/PreparedRelativeEndpointNumericalBounds.lean`, `Estimates/ScaledConditionedComparison.lean`, `Fourier/UniformSpectrumAbsoluteCap.lean`, `Lattices/AffineBlockScale.lean`, `Lattices/AffineCubePlateauSite.lean`, `Lattices/AffineModeratePlateauModel.lean`, `Lattices/SelectedResidueCenterMix.lean`, `Lattices/WeightedCubeIntegerSupport.lean`, `Lattices/WeightedSliceIntegerImage.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/JointExceptionalPolynomialBudget.lean`, `Probability/PreparedCommonRadiusDensityCapNested.lean`, `Sampling/JointSamplerProductivity.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`, `Sampling/PreparedCenteredForecastPathLogEnvelope.lean`, `Sampling/PreparedConcreteComparisonGridBudget.lean`, `Sampling/PreparedSlicedForecastScalarEnvelope.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B130
import Definitions.Def_OAIE3v2B131
import Definitions.Def_OAIE3v2B136
import Definitions.Def_OAIE3v2B137
import Definitions.Def_OAIE3v2B138
import Definitions.Def_OAIE3v2B139

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

noncomputable def weightedAffineModerateGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  c.source.complexMean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((shift + (z none : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def weightedCubeIntegerSource {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (∀ b j, IntegerScalarCubeBox I (s b j).length) :=
  FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def weightedModerateIntegerSource {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (IntegerScalarCubeBox Empty c.length ×
      (∀ j, IntegerScalarCubeBox I (s j).length)) :=
  c.source.prod (FiniteProbabilityWeights.pi (fun j => (s j).source))

noncomputable def weightedModerateIntegerProductSource {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :=
  FiniteProbabilityWeights.pi (fun b => weightedModerateIntegerSource (c b) (s b))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def affineWeightedCubeGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean (fun z => character
    ((booleanBlockPhase (gridJetFrequency M J k)
      (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
variable (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)

noncomputable def affineCubePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v rows shift) K M F z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (J j)] in
theorem centeredAffineCoefficientTorus_eq_subtractive {V : Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (c : ∀ j, U j) (frame : Option K → V → ℝ) :
    centeredAffineCoefficientTorus U p hm c frame =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) +
      affineSampleCoefficientTorus U p hm frame := by
  rw [centeredAffineCoefficientTorus, centeredAffineCoefficientArray, map_sub]
  exact sub_eq_neg_add _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCenterMix
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedResidue_center_mixture_compare {C K I : Type*} [MeasurableSpace C]
    [Fintype K] [Fintype I] (μ : Measure C) [IsProbabilityMeasure μ]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : C → (K × I → ℤ) → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z) (hD : ∀ c, 0 < selectedResidueDensityMass modulus T W (D c))
    (F : C → (K × I → ℤ) → ℝ) (hF : ∀ z, Integrable (fun c => F c z) μ)
    (hFmass : ∀ z, (∫ c, F c z ∂μ) = 1)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (herror : ∀ c,
      ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D c) (hD0 c) (hD c) z).toReal : ℂ)*f z) -
        (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*(f z*(F c z : ℂ)))‖ ≤ ε) :
    ‖(∫ c, ∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D c) (hD0 c) (hD c) z).toReal : ℂ)*f z ∂μ) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*f z)‖ ≤ ε := by
  simp_rw [selectedResidueDensityPMF_normalizedDensityTest]
  rw [← selectedResidueFiniteLaw_complexMean modulus T W hW hZ f]
  apply FiniteProbabilityWeights.integral_normalizedDensityTest_compare
    (selectedResidueFiniteLaw modulus T W hW hZ) μ
    (fun c z => D c z.val) (fun z => hDm z.val) (fun c z => hD0 c z.val)
    (fun c => by rw [selectedResidueFiniteLaw_densityMass]; exact hD c)
    (fun c z => F c z.val) (fun z => hF z.val) (fun z => hFmass z.val)
    (fun z => f z.val) (fun z => hf z.val)
  intro c
  have h := herror c
  rw [selectedResidueDensityPMF_normalizedDensityTest,
    ← selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => f z*(F c z : ℂ))] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointSamplerProductivity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem integral_productive_sampler_mass {C Ω : Type*}
    [MeasurableSpace C] [Fintype Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (score : C → Ω → ℝ)
    (bad : C → Finset Ω) {σ : ℝ} (hσ : 0 < σ)
    (hscore : ∀ c z, score c z ≤ 1)
    (hiScore : Integrable (fun c => (law c).mean (score c)) μ)
    (hiBad : Integrable (fun c => (law c).mass (bad c)) μ)
    (hiProductive : Integrable (fun c => (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad c ∧ σ / 2 ≤ score c z))) μ)
    (hmean : 7 * σ / 8 ≤ ∫ c, (law c).mean (score c) ∂μ)
    (hbad : (∫ c, (law c).mass (bad c) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad c ∧ σ / 2 ≤ score c z)) ∂μ := by
  have h := integral_mono ((hiScore.sub (integrable_const (σ / 2))).sub hiBad)
    hiProductive (fun c => (law c).productive_mass_lower_bound (score c) (bad c)
      (by positivity : 0 ≤ σ / 2) (hscore c))
  simp only [Pi.sub_apply] at h
  rw [integral_sub (f := fun c => (law c).mean (score c) - σ / 2)
      (g := fun c => (law c).mass (bad c))
      (hiScore.sub (integrable_const (σ / 2))) hiBad,
    integral_sub hiScore (integrable_const (σ / 2)),
    integral_const, probReal_univ, one_smul] at h
  linarith

theorem integral_productive_injective_mass {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable (fun c => (law c).mean (fun z => test (image z r))) μ)
    (hmarginal : ∀ r, parent - η ≤ ∫ c, (law c).mean (fun z => test (image z r)) ∂μ)
    (hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (image z))) μ)
    (hiProductive : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r))))) μ)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) ∂μ := by
  let score := fun z => sites.mean (fun r => test (image z r))
  let bad := Finset.univ.filter (fun z => ¬Function.Injective (image z))
  have hscore (z) : score z ≤ 1 := by
    calc
      _ ≤ sites.mean (fun _ => 1) := sites.mean_mono (fun r => htest _)
      _ = 1 := sites.mean_const 1
  have hbad (c) : (law c).mass bad =
      (law c).mean (fun z => noninjectivityIndicator (image z)) := by
    rw [← (law c).mean_indicator]
    congr 1
    funext z
    by_cases hz : Function.Injective (image z) <;> simp [bad, hz, noninjectivityIndicator]
  have hprod : (Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z)) =
      Finset.univ.filter (fun z => Function.Injective (image z) ∧
        σ / 2 ≤ sites.mean (fun r => test (image z r))) := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not, score]
  have he (c) : (law c).mean score =
      sites.mean (fun r => (law c).mean (fun z => test (image z r))) :=
    (law c).mean_comm sites (fun z r => test (image z r))
  have hi : Integrable (fun c => (law c).mean score) μ := by
    simp_rw [he]
    exact sites.mean_integrable μ _ hint
  have havg : 7 * σ / 8 ≤ ∫ c, (law c).mean score ∂μ := by
    simp_rw [he]
    rw [sites.integral_mean μ _ hint]
    calc
      _ ≤ parent - η := by linarith
      _ = sites.mean (fun _ => parent - η) := (sites.mean_const _).symm
      _ ≤ _ := sites.mean_mono hmarginal
  have hiBad' : Integrable (fun c => (law c).mass bad) μ := by
    simp_rw [hbad]
    exact hiBad
  have hiProd' : Integrable (fun c => (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z))) μ := by
    simpa only [hprod] using hiProductive
  have hbad' : (∫ c, (law c).mass bad ∂μ) ≤ σ / 16 := by
    simpa only [hbad] using hcollision
  have h := integral_productive_sampler_mass μ law (fun _ => score) (fun _ => bad)
    hσ (fun _ => hscore) hi hiBad' hiProd' havg hbad'
  simpa only [hprod] using h

theorem integral_productive_injective_mass_of_complex_marginals {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable
      (fun c => (law c).complexMean (fun z => (test (image z r) : ℂ))) μ)
    (hmarginal : ∀ r, ‖(∫ c, (law c).complexMean (fun z => (test (image z r) : ℂ)) ∂μ) -
      (parent : ℂ)‖ ≤ η)
    (hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (image z))) μ)
    (hiProductive : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r))))) μ)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) ∂μ := by
  apply integral_productive_injective_mass μ law sites image test hσ hη hparent htest
  · intro r
    have hi := (hint r).re
    change Integrable (fun c => ((law c).complexMean
      (fun z => (test (image z r) : ℂ))).re) μ at hi
    simpa only [FiniteProbabilityWeights.complexMean_ofReal, Complex.ofReal_re] using hi
  · intro r
    have h := hmarginal r
    simp only [FiniteProbabilityWeights.complexMean_ofReal, integral_complex_ofReal,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).1]
  · exact hiBad
  · exact hiProductive
  · exact hcollision

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

theorem centeredFiniteMarginal_mean (f : Ω → ℝ) :
    (centeredFiniteMarginal μ law hweight).mean f = ∫ c, (law c).mean f ∂μ := by
  unfold FiniteProbabilityWeights.mean
  rw [integral_finsetSum _ (fun z _ =>
    (centeredFinite_weight_integrable μ law hweight z).mul_const (f z))]
  simp only [integral_mul_const, centeredFiniteMarginal]

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

theorem centeredFiniteMarginal_excessMass_le (reference : FiniteProbabilityWeights Ω) (cap : ℝ) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤
      ∫ c, reference.excessMass (law c) cap ∂μ := by
  unfold FiniteProbabilityWeights.excessMass
  have hmax (z : Ω) : Integrable (fun c => max ((law c).weight z - cap * reference.weight z) 0) μ :=
    ((centeredFinite_weight_integrable μ law hweight z).sub
      (integrable_const (cap * reference.weight z))).sup (integrable_const 0)
  rw [integral_finsetSum _ (fun z _ => hmax z)]
  apply Finset.sum_le_sum
  intro z _
  change max ((∫ c, (law c).weight z ∂μ) - cap * reference.weight z) 0 ≤ _
  apply max_le
  · have hi := (centeredFinite_weight_integrable μ law hweight z).sub
      (integrable_const (cap * reference.weight z))
    have hm := hi.sup (integrable_const 0)
    have h := integral_mono hi hm (fun c => le_max_left ((law c).weight z - cap * reference.weight z) 0)
    change (∫ c, (law c).weight z - cap * reference.weight z ∂μ) ≤
      ∫ c, max ((law c).weight z - cap * reference.weight z) 0 ∂μ at h
    simpa only [integral_sub (centeredFinite_weight_integrable μ law hweight z)
      (integrable_const _), integral_const, probReal_univ, one_smul] using h
  · exact integral_nonneg (fun _ => le_max_right _ _)

section Site

variable {T X : Type*} [Fintype T] [Nonempty T] [Fintype X]
variable (physical : Ω → T → X)

theorem centeredFiniteMarginal_siteLaw :
    (centeredFiniteMarginal μ law hweight).siteLaw physical =
      centeredFiniteMarginal μ (fun c => (law c).siteLaw physical)
        (centeredFinite_siteLaw_weight_measurable law hweight physical) := by
  apply FiniteProbabilityWeights.ext_weight
  funext x
  change ((centeredFiniteMarginal μ law hweight).siteLaw physical).weight x =
    ∫ c, ((law c).siteLaw physical).weight x ∂μ
  calc
    _ = ((centeredFiniteMarginal μ law hweight).siteLaw physical).mean
        (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖) :=
      (FiniteProbabilityWeights.mean_single_norm _ x).symm
    _ = ∫ c, (law c).mean
        (fun z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖) ∂μ := by
      rw [FiniteProbabilityWeights.siteLaw_mean, centeredFiniteMarginal_mean]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with c
      exact (FiniteProbabilityWeights.siteLaw_mean (law c) physical
        (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖)).symm.trans
          (FiniteProbabilityWeights.mean_single_norm _ x)

end Site

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {X Y R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem DegreeLE.subtractConstant {w : X → ℕ} {h : ℕ} {p : VectorPolynomial X R V}
    (hp : DegreeLE w h p) (c : V) : DegreeLE w h (subtractConstant c p) := by
  intro d hd
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    simp at hd
  rw [coefficients_subtractConstant, hp d hd, if_neg hd0, sub_zero]

theorem homogeneousPart_subtractConstant {h : ℕ} (hh : 0 < h) (c : V)
    (p : VectorPolynomial X R V) :
    homogeneousPart h (subtractConstant c p) = homogeneousPart h p := by
  classical
  apply coefficients.injective
  ext d
  by_cases hd : d.degree = h
  · have hd0 : d ≠ 0 := by
      intro he
      subst d
      have : h = 0 := by simpa using hd.symm
      omega
    simp only [coefficients_homogeneousPart, hd, ite_true, coefficients_subtractConstant,
      hd0, ite_false, sub_zero]
  · simp only [coefficients_homogeneousPart, hd, ite_false]

theorem hasLayerSamplingRank_subtractConstant_iff {I J : Type*} [Fintype J]
    {h : ℕ} (hh : 0 < h) (T : I → ℝ) (R : ℝ) (U : Submodule ℝ (J → ℝ))
    (c : J → ℝ) (p : VectorPolynomial I ℝ (J → ℝ)) :
    HasLayerSamplingRank h T R U (subtractConstant c p) ↔ HasLayerSamplingRank h T R U p := by
  rw [← hasLayerSamplingRank_homogeneousPart_iff h T R U (subtractConstant c p),
    homogeneousPart_subtractConstant hh, hasLayerSamplingRank_homogeneousPart_iff]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def weightedAffineModerateGridApproximation {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ)
    (S : Finset (J → Fin M)) : ℂ :=
  ((K : ℂ) / M) ^ J.card * ∑ k ∈ S,
    (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k) *
      (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

noncomputable def weightedAffineModeratePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    weightedAffineModerateGridApproximation c s u v K M rows offset shift z F

noncomputable def weightedAffinePlateauModeCoefficient (K M : ℕ) (rows : Finset (Finset I))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card *
    ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k

noncomputable def weightedAffinePlateauModeModel (p : PMF T) (H : ℝ) (K : ℕ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (shift : T → rows → ℤ) (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) : ℂ :=
  finiteResidueModeModel (fun k : F => D k) (fun k => a k)
    (fun k => weightedAffinePlateauModeCoefficient c s u v offset K M rows k)
    (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift) residue x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem fixed_weight_patch_function {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
    {d s N J : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    {M L δ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hΦ : ∀ a, ((Φ a).lip : ℝ) ≤ L)
    (hN : 8 ≤ N) (hkernel : 2 * L * (patchKernelGridRadius N : ℝ) ≤ δ / 2)
    (hJ : 0 < J) (hsmall : patchTopNetError d s J (M + 1 / 4) < 1 / 4)
    (hhomogeneous : ((2 * ((N + 1) ^ d : ℕ) + 1 : ℝ≥0) / patchKernelGridRadius N : ℝ≥0) *
      patchTopNetError d s J (M + 1 / 4) ≤ δ / (4 * ((N + 1 : ℕ) : ℝ) ^ d))
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
    (score : Ω → T → ℝ) (hscore : ∀ a t, |score a t| ≤ 1)
    (hpositive : ∀ a ∈ productive, δ ≤
      (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue (Φ a))) :
    ∃ (i : Fin d → Fin (N + 1)) (B : PolynomialSlots X d w)
      (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
      (∀ j, realPolynomialMass (B.center j) ≤ M + 1 / 4) ∧
      retained ⊆ productive ∧
      outer.mass productive /
        (((N + 1 : ℕ) : ℝ) ^ d * ((J + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, δ / (4 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
        (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (point a t))).patchValue
            (gridPatchKernel d N hN i)) := by
  let P : Ω → PolynomialPatch X s d := fun a =>
    ⟨w, hpos, hs, hw, A a, Φ a⟩
  have hk (a) : 2 * ((Φ a).lip : ℝ) * (patchKernelGridRadius N : ℝ) ≤ δ / 2 :=
    (mul_le_mul (mul_le_mul_of_nonneg_left (hΦ a) (by norm_num))
      le_rfl (patchKernelGridRadius N).coe_nonneg
      (mul_nonneg (by norm_num) hL)).trans hkernel
  have hchoose (a : Ω) : ∃ i : Fin d → Fin (N + 1), a ∈ productive →
      δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤ (localLaw a).mean (fun t => score a t *
        ((P a).gridKernelReplacement hN i).value (point a t)) := by
    by_cases ha : a ∈ productive
    · obtain ⟨i, hi⟩ := (P a).exists_gridKernelReplacement_score hN (localLaw a) (point a)
        (score a) (hscore a) hδ (hpositive a ha) (hk a)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨fun _ => 0, fun h => (ha h).elim⟩
  choose code hcode using hchoose
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass productive code
  let Q := productive.filter (fun a => code a = i)
  let A' : Ω → PolynomialSlots X d w := fun a => ((P a).gridKernelReplacement hN i).form
  have hA' (a) (j) : realPolynomialMass ((A' a).center j) ≤ M + 1 / 4 := by
    change realPolynomialMass ((A a).center j + MvPolynomial.C (uniformBoxGrid (1 / 4) N i j)) ≤ _
    apply (realPolynomialMass_add_le _ _).trans
    rw [realPolynomialMass_C]
    exact add_le_add (hA a j) (uniformBoxGrid_mem (by norm_num) (by omega : 0 < N) i j)
  have hδ' : 0 < δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hpositive' (a) (ha : a ∈ Q) : δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
      (localLaw a).mean (fun t => score a t * ((A' a).slots (point a t)).patchValue
        (gridPatchKernel d N hN i)) := by
    obtain ⟨ha, hai⟩ := Finset.mem_filter.mp ha
    have h := hcode a ha
    rw [hai] at h
    exact h
  have he : (gridPatchKernel d N hN i).lip * patchTopNetError d s J (M + 1 / 4) ≤
      (δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d)) / 2 := by
    simp only [gridPatchKernel]
    convert hhomogeneous using 1; ring
  obtain ⟨B, retained, hB, hretained, hmass, hlocal⟩ :=
    PolynomialSlots.exists_fixed_kernel_patch_function A' hw hpos hs (gridPatchKernel d N hN i)
      (by linarith : 0 ≤ M + 1 / 4) hA' hJ hsmall outer Q localLaw point score hscore hδ' hpositive' he
  refine ⟨i, B, A', retained, hB, fun a ha => (Finset.mem_filter.mp (hretained ha)).1, ?_, ?_⟩
  · have hi' : outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ d ≤ outer.mass Q := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hi
      convert hi using 1; try rfl
      congr 1
      ext a
      simp only [Q, Finset.mem_filter]
    apply le_trans _ hmass
    rw [← div_div]
    exact div_le_div_of_nonneg_right hi' (by positivity)
  · intro a ha
    convert hlocal a ha using 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubePlateauSite
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [DecidableEq B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)
variable (u : B → Fin (n + 1) → Option α → ℤ) (v : B → Fin (n + 1) → Option α → ℕ)

noncomputable def affineCubePlateauCoefficient (K M : ℕ) (rows : Finset (Finset α))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card * ∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem uniformProductAccuracyLog_eval₂ (D T E : Polynomial ℕ) (x : ℝ) :
    (uniformProductAccuracyLog D T E).eval₂ (Nat.castRingHom ℝ) x =
      uniformProductAccuracyLog (D.eval₂ (Nat.castRingHom ℝ) x)
        (T.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [uniformProductAccuracyLog]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointExceptionalPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem exists_spatialMatrixBlock_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P E : ℝ} {n : ℕ}, 0 ≤ P →
      (n : ℝ) ≤ P → 0 ≤ E → E ≤ P →
      smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E + ((n : ℝ)+1)^2+1 ≤
        (P+A)^A ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 E ≤ (P+A)^A := by
  let c : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊
  have hc : (probabilityProfileLipschitz : ℝ) ≤ (c : ℝ) := Nat.le_ceil _
  let p : Polynomial ℕ :=
    2 * Polynomial.X ^ 3 + 2 +
      2 * Polynomial.X ^ 3 * (11 * Polynomial.X ^ 2 + 11 * Polynomial.X + 5) +
      3 * Polynomial.X ^ 2 + 2 * Polynomial.X + 10 + Polynomial.C c
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget p
  refine ⟨A, hA, ?_⟩
  intro P E n hP hn hE hEP
  have hthreshold : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E ≤
      2*P^3+2+2*P^3*(11*P^2+11*P+5) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hstep : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E =
        2*(n : ℝ)^3+2+2*(n : ℝ)^3*(11*(n : ℝ)^2+10*n+E+5) := by
      unfold smoothMatrixBlockThresholdLogBudget smoothMatrixBlockConstantLogBudget
      push_cast
      ring
    rw [hstep]
    calc
      _ ≤ 2*P^3+2+2*P^3*(11*P^2+10*P+P+5) := by gcongr
      _ = _ := by ring
  have hev : Polynomial.eval₂ (Nat.castRingHom ℝ) P p =
      2*P^3+2+2*P^3*(11*P^2+11*P+5)+3*P^2+2*P+10+c := by
    simp [p, Polynomial.eval₂_pow]
  have hbudget := hbound P hP
  rw [hev] at hbudget
  constructor
  · apply le_trans _ hbudget
    have hsq : ((n : ℝ)+1)^2 ≤ (P+1)^2 := by gcongr
    nlinarith [Nat.cast_nonneg (α := ℝ) c, sq_nonneg P]
  · apply le_trans _ hbudget
    have heq : smoothMatrixBlockWidthLogBudget (2*n*n) n 2 E =
        smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E +
          3*(n : ℝ)^2+2*n+9+probabilityProfileLipschitz := by
      unfold smoothMatrixBlockWidthLogBudget smoothMatrixBlockMeshLogBudget
      push_cast
      ring
    rw [heq]
    have hsq : (n : ℝ)^2 ≤ P^2 := by gcongr
    nlinarith

end Erdos3

end

section

namespace Erdos3

theorem exists_jointExceptional_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P₀ g₀ : ℝ} {n : ℕ}, 0 ≤ P₀ →
      (n : ℝ) ≤ P₀ → 0 ≤ g₀ → g₀ ≤ P₀ →
      smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 (g₀+8) +
          ((n : ℝ)+1)^2+1 ≤ (P₀+A)^A ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 (g₀+8) ≤ (P₀+A)^A := by
  obtain ⟨a, ha, hbudget⟩ := exists_spatialMatrixBlock_polynomial_budget
  refine ⟨a + 8, by omega, ?_⟩
  intro P₀ g₀ n hP hn hg hgP
  obtain ⟨hthreshold, hwidth⟩ := hbudget (P := P₀ + 8) (E := g₀ + 8)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : (P₀ + 8 + a : ℝ) = P₀ + (a + 8 : ℕ) := by push_cast; ring
  have hpow : (P₀ + 8 + a : ℝ)^a ≤ (P₀ + (a + 8 : ℕ))^(a + 8) := by
    rw [hbase]
    apply pow_le_pow_right₀
    · push_cast
      linarith
    · omega
  exact ⟨hthreshold.trans hpow, hwidth.trans hpow⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointExceptionalGainBudget
namespace OAI

section

namespace Erdos3

theorem exists_jointSpatialError_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P₀ gainLog : ℝ} {n : ℕ}, 0 ≤ P₀ →
      0 < n → (n : ℝ) ≤ P₀ → 0 ≤ gainLog → gainLog ≤ P₀ →
      (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
          Real.exp ((P₀ + A)^A) ∧
      (2 / spatialMatrixBlockThreshold n (jointSpatialError gainLog)) *
          ((n * n.factorial : ℕ) : ℝ) ≤ Real.exp ((P₀ + A)^A) ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 (gainLog+8) ≤ (P₀+A)^A := by
  obtain ⟨A, hA, hbudget⟩ := exists_jointExceptional_polynomial_budget
  refine ⟨A, hA, ?_⟩
  intro P₀ gainLog n hP hn hnP hg hgP
  obtain ⟨hthreshold, hwidth⟩ := hbudget hP hnP hg hgP
  have hη := jointSpatialError_pos gainLog
  have hηb := jointSpatialError_inverse_le_exp gainLog
  have hE : 0 ≤ gainLog + 8 := by linarith
  have hthreshold' : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2
      (gainLog+8) ≤ (P₀+A)^A := by nlinarith [sq_nonneg ((n : ℝ)+1)]
  exact ⟨(spatialMatrixBlockThreshold_inverse_le_exp hn hη hE hηb).trans
      (Real.exp_le_exp.mpr hthreshold'),
    (spatialMatrixBlockCutoff_lip_exp_budget hn hη hE hηb).trans
      (Real.exp_le_exp.mpr hthreshold), hwidth⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastPathLogEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedCenteredForecastThresholdExponent : ℕ :=
  Classical.choose exists_jointSpatialError_polynomial_budget

theorem preparedCenteredForecast_threshold_inverse {P g : ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hn : 0 < n) (hnP : (n : ℝ) ≤ P) (hg : 0 ≤ g) (hgP : g ≤ P) :
    (spatialMatrixBlockThreshold n (jointSpatialError g))⁻¹ ≤
      Real.exp ((P + preparedCenteredForecastThresholdExponent) ^
        preparedCenteredForecastThresholdExponent) :=
  ((Classical.choose_spec exists_jointSpatialError_polynomial_budget).2 hP hn hnP hg hgP).1

noncomputable def preparedCenteredForecastSpatialLog (P : ℝ) : ℝ :=
  P * (P + 1) + ((P + preparedCenteredForecastThresholdExponent) ^
    preparedCenteredForecastThresholdExponent + 2) + P ^ 2 + P

theorem exists_preparedCenteredForecastSpatialLog_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P →
      preparedCenteredForecastSpatialLog P ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := preparedCenteredForecastThresholdExponent
  let Q : Polynomial ℕ := X * (X + 1) + ((X + Polynomial.C A) ^ A + 2) + X ^ 2 + X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro P hP
  simpa [Q, X, A, preparedCenteredForecastSpatialLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastSpatialBudget (m M nX Jalloc : ℕ)
    (Pdim cost : ℝ) : ℝ :=
  max (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + nX + 8)
    (max (preparedCenteredForecastSpatialLog Pdim) (cost + 1))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteComparisonGridBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastGridLog (m M nX Jalloc : ℕ)
    (Pdim cost gainLog Qstride Ptest : ℝ) : ℝ :=
  max (preparedSlicedForecastSourceLog m M Jalloc Ptest)
    (max (forecastOriginalSmoothBudget m
      (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost + (nX + 1) * (cost + 1)))
      ((preparedSlicedForecastBadLog m nX Qstride gainLog + (cost + 1)) *
        ((nX + m * M + 2 : ℕ) : ℝ) * modularRankChargeFactor m))

noncomputable def preparedSlicedForecastComparisonFloorLog (m M nX Jalloc d : ℕ)
    (Pdim cost pRadius gainLog Qstride Ptest V E : ℝ) : ℝ :=
  allocatedFixedPathSlicedAmbientFloorLog d
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
    (preparedSlicedForecastSourceLog m M Jalloc Ptest) V cost E
    (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest) pRadius

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastScalarEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedSlicedForecastScalarEnvelope (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → Pchart ∈ Set.Icc 0 t →
      PF ∈ Set.Icc 0 t → childCost ∈ Set.Icc 0 t →
      let cap := (t + C) ^ C
      preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 cap ∧
      cost + 1 ∈ Set.Icc 0 cap ∧
      gainLog + nX + 8 ∈ Set.Icc 0 cap ∧
      pRadius ∈ Set.Icc 0 cap ∧
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 cap ∧
      (m : ℝ) ≤ cap ∧ ((nX + m * M : ℕ) : ℝ) ≤ cap ∧ (nX : ℝ) ≤ cap ∧
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 cap ∧
      PF ∈ Set.Icc 0 cap ∧ childCost + 1 ∈ Set.Icc 0 cap := by
  obtain ⟨Cs, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let Sp := 3 * X + 9 + (X + Polynomial.C Cs) ^ Cs
  let Bad := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Jac := (X + Polynomial.C m) * (4 * X + 11)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    (Sp + Bad + Jac + 4 * X + 20 + Polynomial.C Cprim + Polynomial.C m)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride Pchart PF childCost
    ht hDbase hDmod hPdim hcost hRadius hGain hStride hChart hPF hChild cap
  let spatial := 3 * t + 9 + (t + Cs) ^ Cs
  let bad := 2 * t ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + t + 11
  let jac := (t + m) * (4 * t + 11)
  let total := spatial + bad + jac + 4 * t + 20 + Cprim + m
  have hs0 : 0 ≤ spatial := by dsimp [spatial]; positivity
  have hb0 : 0 ≤ bad := by dsimp [bad]; positivity
  have hj0 : 0 ≤ jac := by dsimp [jac]; positivity
  have hprim0 : (0 : ℝ) ≤ Cprim := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have htotal : total ≤ cap := by
    simpa [Sp, Bad, Jac, X, total, spatial, bad, jac, cap, Polynomial.eval₂_pow] using hpoly t ht
  have hsCap : spatial ≤ cap := (by dsimp [total]; linarith : spatial ≤ total).trans htotal
  have hbCap : bad ≤ cap := (by dsimp [total]; linarith : bad ≤ total).trans htotal
  have hjCap : jac ≤ cap := (by dsimp [total]; linarith : jac ≤ total).trans htotal
  have hlinear : 4 * t + 20 ≤ cap := (by dsimp [total]; linarith : 4 * t + 20 ≤ total).trans htotal
  have hprimCap : (Cprim : ℝ) ≤ cap := (by dsimp [total]; linarith : (Cprim : ℝ) ≤ total).trans htotal
  have hmCap : (m : ℝ) ≤ cap := (by dsimp [total]; linarith : (m : ℝ) ≤ total).trans htotal
  have htCap : t ≤ cap := by linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ t :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (t + Cs) ^ Cs :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Cs))
      (add_le_add hPdim.2 le_rfl) Cs)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    have hpow : 0 ≤ (t + Cs) ^ Cs := by positivity
    dsimp only [spatial]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith only [hDbase, hnX, hcenter, hcost.2, ht, hpow]
  have hBad0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hBad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ bad := by
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * t * t :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1 (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hJac0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hJac : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ jac := by
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ t + m := by
      have hdim : (nX : ℝ) + m * M ≤ t := by simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * t + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  exact ⟨⟨hP0, hP.trans hsCap⟩, ⟨hBad0, hBad.trans hbCap⟩,
    ⟨by linarith [hcost.1], by linarith [hcost.2]⟩,
    ⟨by linarith [hGain.1], by linarith [hGain.2]⟩,
    ⟨hRadius.1, hRadius.2.trans htCap⟩, ⟨hDbase0, hDbase.trans htCap⟩,
    ⟨zero_le_one.trans preparedSlicedForecastPrimitiveCap_one_le,
      (Nat.le_ceil _).trans hprimCap⟩,
    hmCap, hDmod.trans htCap, hnX.trans htCap,
    ⟨by linarith [hRadius.1], by linarith [hRadius.2]⟩,
    ⟨hJac0, hJac.trans hjCap⟩, ⟨hPF.1, hPF.2.trans htCap⟩,
    ⟨by linarith [hChild.1], by linarith [hChild.2]⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointPrimitiveExponent (m : ℕ) : ℕ :=
  (exists_preparedSlicedForecastScalarEnvelope m).choose

noncomputable def preparedRelativeEndpointInputScale (m earlyPower : ℕ) (B : ℝ) : ℝ :=
  let a := preparedRelativeEndpointInputBase earlyPower B
  a + (a + preparedRelativeEndpointPrimitiveExponent m) ^
    preparedRelativeEndpointPrimitiveExponent m + 1

theorem preparedRelativeEndpointInputScale_bounds (m earlyPower : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ preparedRelativeEndpointInputScale m earlyPower B ∧
    preparedRelativeEndpointInputBase earlyPower B ≤ preparedRelativeEndpointInputScale m earlyPower B ∧
    (preparedRelativeEndpointInputBase earlyPower B + preparedRelativeEndpointPrimitiveExponent m) ^
      preparedRelativeEndpointPrimitiveExponent m ≤ preparedRelativeEndpointInputScale m earlyPower B := by
  have ha := preparedRelativeEndpointInputBase_bounds earlyPower hB
  have ha0 : 0 ≤ preparedRelativeEndpointInputBase earlyPower B := zero_le_one.trans ha.1
  have hw : 0 ≤ (preparedRelativeEndpointInputBase earlyPower B + preparedRelativeEndpointPrimitiveExponent m) ^
      preparedRelativeEndpointPrimitiveExponent m := by positivity
  unfold preparedRelativeEndpointInputScale
  exact ⟨by linarith only [ha.1, hw], by linarith only [hw], by linarith only [ha.1]⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledConditionedComparison
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productAtomTruncatedPairing (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) : ℝ :=
  productCouplingPairing c (productANOVATruncation μ D (fun z => productFiberIndicator I x z * w z))
    (productANOVATruncation ν D (fun z => productFiberIndicator I y z * f z))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productTruncatedPairing (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) : ℝ :=
  productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedCommonRadiusDensityCapNested
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_commonRadius_densityCap_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
      ∀ a n : Fin m → ℕ, (∀ j, (a j : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j) ≤ Real.exp ((p + A) ^ A) := by
  let rad : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  let env : Polynomial ℕ := Polynomial.X + rad + 4
  let cap : Polynomial ℕ := 3 * env ^ 3 + 17 * env ^ 2 + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget cap
  refine ⟨A, hA, ?_⟩
  intro p hp hm a n ha hn V hV hprofile
  let E := p + allocatedCommonProductRadiusLog m p p + 4
  obtain ⟨hrad, hR, _, hRinv, _⟩ := allocatedCommonProductRadius_bounds m hp hp
  have hpE : p ≤ E := by dsimp only [E]; linarith
  have hradE : allocatedCommonProductRadiusLog m p p ≤ E := by dsimp only [E]; linarith
  have hE : 0 ≤ E := hp.trans hpE
  have heval : env.eval₂ (Nat.castRingHom ℝ) p = E := by
    simp [env, rad, E, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
      allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
      allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
      allocatedComparisonDimension, Polynomial.eval₂_pow]
  have hcap : earlyFiberCapLog E + 4 ≤ (p + A) ^ A := by
    simpa only [cap, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_ofNat, heval, earlyFiberCapLog] using hbound p hp
  have hprod := earlyFiberCap_exp_bound a n (fun _ => allocatedCommonProductRadius m p p)
    (fun j => (V j : ℝ)) hE (hm.trans hpE) (fun _ => hR)
    (fun j => (V j).coe_nonneg) (fun j => (ha j).trans hpE)
    (fun j => (hn j).trans hpE) (hprofile.trans (Real.exp_le_exp.mpr hpE))
    (fun _ => hRinv.le.trans (Real.exp_le_exp.mpr hradE))
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hpE))
  calc
    4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j)
      ≤ Real.exp 4 * Real.exp (earlyFiberCapLog E) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)]) hprod
          (Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ hR (V j).coe_nonneg))
          (Real.exp_nonneg _)
    _ = Real.exp (earlyFiberCapLog E + 4) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr hcap

theorem exists_commonRadius_densityCap_uniform_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ m : ℕ, m ≤ maxLayers → ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
      ∀ a n : Fin m → ℕ, (∀ j, (a j : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j) ≤ Real.exp ((p + A) ^ A) := by
  classical
  choose ex hex hb using fun j : Fin (maxLayers + 1) => exists_commonRadius_densityCap_bound j.val
  let A₀ := 2 + ∑ j, ex j
  refine ⟨A₀, by dsimp only [A₀]; omega, ?_⟩
  intro A hA m hm p hp hmp a n ha hn V hV hprofile
  let j : Fin (maxLayers + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hEA : ex j ≤ A := by dsimp only [A₀] at hA; omega
  have hAtwo : (2 : ℝ) ≤ A := by exact_mod_cast (hex j).trans hEA
  have hpow : (p + ex j) ^ ex j ≤ (p + A) ^ A :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hEA)) _).trans
      (pow_le_pow_right₀ (by linarith) hEA)
  exact (hb j p hp hmp a n ha hn V hV hprofile).trans (Real.exp_le_exp.mpr hpow)

end Erdos3.VectorPolynomial

end

end OAI
end


