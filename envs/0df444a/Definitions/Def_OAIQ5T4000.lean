-- Prove2me | Definitions.Def_OAIQ5T4000
-- name    : OAIQ5T4000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T12:42:45.778997+00:00
-- url     : https://prove2.me/theorems/595d0194-39ec-47e6-8f92-e5448397d3a3
-- title:
--   Definitions bundle OAIQ5T4000 of the split of OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 614 declarations of OpenAI's Lean: 283 definitions, 10 inductive types or structures, 33 instances and 288 theorems. The definitions and types are `OAI.EuclideanFiveColor.AlgebraicCayley.asN`, `OAI.EuclideanFiveColor.AlgebraicCayley.generatedField`, `OAI.EuclideanFiveColor.AlgebraicCayley.generatingSet`, `OAI.EuclideanFiveColor.AlgebraicCayley.iN`, `OAI.EuclideanFiveColor.AlgebraicCayley.polyLinear`, `OAI.EuclideanFiveColor.AlgebraicCayley.realCayley`, `OAI.EuclideanFiveColor.AlgebraicCayley.realLine`, `OAI.EuclideanFiveColor.AlgebraicCayley.realSlice`, `OAI.EuclideanFiveColor.Amenable.Koopman.action`, `OAI.EuclideanFiveColor.Amenable.Koopman.linear`, `OAI.EuclideanFiveColor.Amenable.Mean`, `OAI.EuclideanFiveColor.Amenable.Mean.correlation`, `OAI.EuclideanFiveColor.Amenable.Mean.cross`, `OAI.EuclideanFiveColor.Amenable.Mean.normFn`, `OAI.EuclideanFiveColor.Amenable.Mean.orbit`, `OAI.EuclideanFiveColor.Amenable.Mean.pairing`, `OAI.EuclideanFiveColor.Amenable.Mean.pairingMap`, `OAI.EuclideanFiveColor.Amenable.Mean.squareNorm`, `OAI.EuclideanFiveColor.Amenable.Mean.vector`, `OAI.EuclideanFiveColor.Amenable.shift`, `OAI.EuclideanFiveColor.Angles`, `OAI.EuclideanFiveColor.ApproachingContinuum`, `OAI.EuclideanFiveColor.AverageErrors.goodFraction`, `OAI.EuclideanFiveColor.BinaryCenter`, `OAI.EuclideanFiveColor.BoundedMeasurable.Admissible`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.avg`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.bound`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.conditional`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.const`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.energy`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.l2Linear`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.meanNorm`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.orbit`, `OAI.EuclideanFiveColor.BoundedMeasurable.Family.toL2`, `OAI.EuclideanFiveColor.BoundedMeasurable.FiniteTensor`, `OAI.EuclideanFiveColor.BoundedMeasurable.Func`, `OAI.EuclideanFiveColor.BoundedMeasurable.PairVanishing`, `OAI.EuclideanFiveColor.BoundedMeasurable.act`, `OAI.EuclideanFiveColor.BoundedMeasurable.algebra` and 253 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/PlaneColoring, in whole or in part: `CompactFactors_AlgebraModels`, `CompactFactors_Amenability`, `CompactFactors_Approximation`, `CompactFactors_BoundedFunctions`, `CompactFactors_Centers`, `CompactFactors_ConditionalLimits`, `CompactFactors_ConditionalSelection`, `CompactFactors_Factors`, `CompactFactors_Functions`, `CompactFactors_Kernels`, `CompactFactors_RelativeCenters`, `CompactFactors_RelativeProducts`, `CompactFactors_Separability`, `CompactFactors_Stationary`, `PlaneColoring_Accumulation`, `PlaneColoring_AngularBoundary`, `PlaneColoring_BinaryPalettes`, `PlaneColoring_CircleMaps`, `PlaneColoring_Coloring`, `PlaneColoring_Compactness`, `PlaneColoring_ContinuumLimits`, `PlaneColoring_CyclicCore`, `PlaneColoring_DiskAverages`, `PlaneColoring_DiskExtension`, `PlaneColoring_Exclusion`, `PlaneColoring_FiveSupport`, `PlaneColoring_FullApproximation`, `PlaneColoring_GraphCuts`, `PlaneColoring_GraphPatches`, `PlaneColoring_GraphRealization`, `PlaneColoring_HoleApproximation`, `PlaneColoring_Interfaces`, `PlaneColoring_PaletteDensity`, `PlaneColoring_Palettes`, `PlaneColoring_States`, `PlaneColoring_Transitions`, `PlaneColoring_WeakColoring`, `PlaneSpectrum_Basic`, `PlaneSpectrum_Characters`, `PlaneSpectrum_ConditionalSpectrum`, `PlaneSpectrum_Energy`, `PlaneSpectrum_Ergodicity`, `PlaneSpectrum_Fourier`, `PlaneSpectrum_FourierTests`, `PlaneSpectrum_InvariantMean`, `PlaneSpectrum_Multipliers`, `PlaneSpectrum_NumberFields`, `PlaneSpectrum_PhaseCollision`, `PlaneSpectrum_PhaseEncoding`, `PlaneSpectrum_Representations`, `PlaneSpectrum_Selections`, `PlaneSpectrum_SmallArcs`, `PlaneSpectrum_SpectralMeasure`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5T4002`; the statement `OAI_EuclideanFiveColor_fullApprox_exists_of_finite_core`; the proof of `OAI_EuclideanFiveColor_fullApprox_exists_of_finite_core`.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/PlaneColoring at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ5_T4.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Amenability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

open scoped RealInnerProductSpace BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable
variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

def shift {E : Type*} [PseudoMetricSpace E] (g : G) (f : G →ᵇ E) : G →ᵇ E :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply {E : Type*} [PseudoMetricSpace E] (g x : G) (f : G →ᵇ E) :
    shift G g f x = f (x+g) := rfl

/-- A normalized positive translation-invariant real functional. -/
structure Mean where
  map : (G →ᵇ ℝ) →L[ℝ] ℝ
  map_const : ∀ c, map (BoundedContinuousFunction.const G c) = c
  positive : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ map f
  invariant : ∀ g f, map (shift G g f) = map f

variable {G}
namespace Mean
variable (M : Mean G)
lemma mono (f h : G →ᵇ ℝ) (hf : ∀ x, f x ≤ h x) : M.map f ≤ M.map h := by
  have hm := M.positive (h-f) (fun x => sub_nonneg.mpr (hf x))
  simpa only [map_sub, sub_nonneg] using hm

lemma abs_le (f h : G →ᵇ ℝ) (hf : ∀ x, |f x| ≤ h x) : |M.map f| ≤ M.map h := by
  rw [_root_.abs_le]
  constructor
  · have := M.mono (-h) f (fun x => (_root_.abs_le.mp (hf x)).1)
    simpa only [map_neg] using this
  · exact M.mono f h fun x => (_root_.abs_le.mp (hf x)).2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def normFn (V : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖V x‖)
    (continuous_norm.comp V.continuous) ‖V‖ (fun x => by simpa using V.norm_coe_le_norm x)
omit [AddCommGroup G] [DiscreteTopology G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma normFn_apply (V : G →ᵇ H) (x : G) : normFn V x = ‖V x‖ := rfl

def pairing (V : G →ᵇ H) (v : H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => inner ℝ (V x) v)
    (V.continuous.inner continuous_const) (‖V‖ * ‖v‖)
    (fun x => (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (V.norm_coe_le_norm x) (norm_nonneg v)))
omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma pairing_apply (V : G →ᵇ H) (v : H) (x : G) : pairing V v x = inner ℝ (V x) v := rfl

omit [CompleteSpace H] in
lemma pairing_bound (V : G →ᵇ H) (v : H) :
    |M.map (pairing V v)| ≤ M.map (normFn V) * ‖v‖ := by
  have he : M.map (‖v‖ • normFn V) = M.map (normFn V) * ‖v‖ := by
    rw [map_smul]; simp [mul_comm]
  rw [← he]
  apply M.abs_le
  intro x
  simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) (V x) v)

def pairingMap (V : G →ᵇ H) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => M.map (pairing V v)
      map_add' := by
        intro v w
        have he : pairing V (v+w) = pairing V v + pairing V w := by ext; simp [inner_add_right]
        rw [he, map_add]
      map_smul' := by
        intro c v
        have he : pairing V (c • v) = c • pairing V v := by ext; simp [inner_smul_right]
        rw [he, map_smul]; rfl }
    (M.map (normFn V)) (fun v => M.pairing_bound V v)

def vector (V : G →ᵇ H) : H := (InnerProductSpace.toDual ℝ H).symm (M.pairingMap V)

lemma vector_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (M.vector V) v = M.map (pairing V v) := InnerProductSpace.toDual_symm_apply

lemma vector_add (V W : G →ᵇ H) : M.vector (V+W) = M.vector V + M.vector W := by
  apply ext_inner_right ℝ; intro v
  rw [inner_add_left, M.vector_pair, M.vector_pair, M.vector_pair]
  have he : pairing (V+W) v = pairing V v + pairing W v := by ext; simp [inner_add_left]
  rw [he, map_add]

lemma vector_smul (c : ℝ) (V : G →ᵇ H) : M.vector (c • V) = c • M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [real_inner_smul_left, M.vector_pair, M.vector_pair]
  have he : pairing (c • V) v = c • pairing V v := by ext; simp [real_inner_smul_left]
  rw [he, map_smul]; rfl

def squareNorm (V : G →ᵇ H) : G →ᵇ ℝ := normFn V * normFn V
omit [AddCommGroup G] [DiscreteTopology G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma squareNorm_apply (V : G →ᵇ H) (x : G) : squareNorm V x = ‖V x‖^2 := by
  simp [squareNorm, pow_two]

end Mean
end EuclideanFiveColor.Amenable

namespace EuclideanFiveColor.Amenable.Mean

section
open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def cross (V W : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => inner ℝ (V x) (W x))
    (V.continuous.inner W.continuous) (‖V‖ * ‖W‖) (fun x => by
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (V.norm_coe_le_norm x) (W.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma cross_apply (V W : G →ᵇ H) (x : G) : cross V W x = inner ℝ (V x) (W x) := rfl

def correlation (V W : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => M.map (cross (shift G g V) W)) continuous_of_discreteTopology
    (‖V‖ * ‖W‖) (fun g => by
      rw [Real.norm_eq_abs, ← M.map_const (‖V‖ * ‖W‖)]
      apply M.abs_le
      intro x
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (V.norm_coe_le_norm (x+g)) (W.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

omit [CompleteSpace H] in
@[simp] lemma correlation_apply (V W : G →ᵇ H) (g : G) :
    M.correlation V W g = M.map (cross (shift G g V) W) := rfl

end

open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def orbit (U : G → H ≃ₗᵢ[ℝ] H) (v : H) : G →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => U g v)
    continuous_of_discreteTopology ‖v‖ (fun g => le_of_eq ((U g).norm_map v))

omit [AddCommGroup G] [CompleteSpace H] in
@[simp] lemma orbit_apply (U : G → H ≃ₗᵢ[ℝ] H) (v : H) (g : G) : orbit U v g = U g v := rfl

end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.Amenable.Koopman
open MeasureTheory Filter
section Action
variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [VAddInvariantMeasure G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linear (g : G) : Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => g +ᵥ x) (measurePreserving_vadd g μ)

lemma linear_add (g h : G) (f : Lp E 2 μ) :
    linear μ (g+h) f = linear μ g (linear μ h f) := by
  change Lp.compMeasurePreserving (fun x => (g+h) +ᵥ x) _ f =
    Lp.compMeasurePreserving (fun x => g +ᵥ x) _
      (Lp.compMeasurePreserving (fun x => h +ᵥ x) _ f)
  have he : (fun x : X => (g+h) +ᵥ x) =
      (fun x => h +ᵥ x) ∘ (fun x => g +ᵥ x) := by
    funext x
    simp only [Function.comp_apply, ← add_vadd, add_comm]
  simpa only [he] using Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_vadd h μ) (measurePreserving_vadd g μ)

@[simp] lemma linear_zero (f : Lp E 2 μ) : linear μ (0 : G) f = f := by
  change Lp.compMeasurePreserving (fun x => (0 : G) +ᵥ x) _ f = f
  have he : (fun x : X => (0 : G) +ᵥ x) = id := funext (fun x => zero_vadd G x)
  simpa only [he] using Lp.compMeasurePreserving_id_apply f

def action (g : G) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (linear μ g) (fun f =>
    ⟨linear μ (-g) f, by rw [← linear_add, add_neg_cancel, linear_zero]⟩)

@[simp] lemma action_apply (g : G) (f : Lp E 2 μ) : action μ g f = linear μ g f := rfl

end Action

end EuclideanFiveColor.Amenable.Koopman

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Centers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace EuclideanFiveColor.Location

abbrev Ambient := WithLp 2 (ℝ × ℂ)

def lift (z : ℂ) : Ambient := WithLp.toLp 2 (1, z)

@[simp] theorem lift_fst (z : ℂ) : (lift z).fst = 1 := rfl
@[simp] theorem lift_snd (z : ℂ) : (lift z).snd = z := rfl

theorem lift_ne_zero (z : ℂ) : lift z ≠ 0 := by
  intro h
  have := congrArg WithLp.fst h
  simp at this

theorem norm_lift (z : ℂ) : ‖lift z‖ = Real.sqrt (1 + ‖z‖ ^ 2) := by
  simp [WithLp.prod_norm_eq_of_L2]

theorem lift_sub (z w : ℂ) : lift z - lift w = WithLp.toLp 2 (0, z - w) := by
  apply WithLp.ofLp_injective 2
  simp [lift]

theorem norm_lift_sub (z w : ℂ) : ‖lift z - lift w‖ = ‖z - w‖ := by
  rw [lift_sub, WithLp.norm_toLp_snd]

theorem lift_affine (z w : ℂ) (a b : ℝ) (hab : a + b = 1) :
    lift (a • z + b • w) = a • lift z + b • lift w := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simpa using hab.symm
  · rfl

theorem not_sameRay_smul_lift {z w : ℂ} (hzw : z ≠ w)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ SameRay ℝ (a • lift z) (b • lift w) := by
  intro h
  have haz : a • lift z ≠ 0 := smul_ne_zero ha.ne' (lift_ne_zero z)
  have hbw : b • lift w ≠ 0 := smul_ne_zero hb.ne' (lift_ne_zero w)
  obtain ⟨r, hr, he⟩ := h.exists_pos_left haz hbw
  have hfst := congrArg WithLp.fst he
  have hsnd := congrArg WithLp.snd he
  simp only [WithLp.smul_fst, lift_fst, smul_eq_mul, mul_one] at hfst
  simp only [WithLp.smul_snd, lift_snd, smul_smul, hfst] at hsnd
  exact hzw ((smul_right_injective ℂ hb.ne') hsnd)

theorem strictConvex_norm_lift : StrictConvexOn ℝ Set.univ (fun z : ℂ => ‖lift z‖) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ hzw a b ha hb hab
  change ‖lift (a • z + b • w)‖ < a • ‖lift z‖ + b • ‖lift w‖
  rw [lift_affine z w a b hab]
  have := norm_add_lt_of_not_sameRay (not_sameRay_smul_lift hzw ha hb)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb,
    smul_eq_mul] using this

noncomputable def kernel (s t : ℂ) : ℝ := ‖lift (s - t)‖ - ‖lift (-t)‖

noncomputable def objective (μ : Measure ℂ) (s : ℂ) : ℝ := ∫ t, kernel s t ∂μ

theorem kernel_formula (s t : ℂ) : kernel s t =
    Real.sqrt (1 + ‖s - t‖ ^ 2) - Real.sqrt (1 + ‖t‖ ^ 2) := by
  simp [kernel, norm_lift]

theorem continuous_kernel (s : ℂ) : Continuous (kernel s) := by
  simp only [funext (kernel_formula s)]
  fun_prop

theorem kernel_bound (s t : ℂ) : |kernel s t| ≤ ‖s‖ := by
  have h := abs_norm_sub_norm_le (lift (s - t)) (lift (-t))
  simpa [kernel, norm_lift_sub] using h

theorem kernel_diff_bound (s s' t : ℂ) : |kernel s t - kernel s' t| ≤ ‖s - s'‖ := by
  have h := abs_norm_sub_norm_le (lift (s - t)) (lift (s' - t))
  simpa [kernel, norm_lift_sub, sub_sub_sub_cancel_right] using h

theorem integrable_kernel (μ : Measure ℂ) [IsFiniteMeasure μ] (s : ℂ) :
    Integrable (kernel s) μ := by
  apply (integrable_const ‖s‖).mono' (continuous_kernel s).aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa using kernel_bound s t

theorem objective_lipschitz (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (objective μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s s'
  rw [Real.dist_eq, objective, objective, ← integral_sub (integrable_kernel μ s)
    (integrable_kernel μ s')]
  calc
    |∫ t, kernel s t - kernel s' t ∂μ| ≤ ∫ t, |kernel s t - kernel s' t| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℂ, ‖s - s'‖ ∂μ := by
      apply integral_mono ((integrable_kernel μ s).sub (integrable_kernel μ s')).abs
        (integrable_const _)
      exact fun t => kernel_diff_bound s s' t
    _ = (1 : ℝ≥0) * dist s s' := by simp [dist_eq_norm]

theorem continuous_objective (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Continuous (objective μ) := (objective_lipschitz μ).continuous

theorem kernel_strict_convex (t : ℂ) : StrictConvexOn ℝ Set.univ (fun s => kernel s t) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ hzw a b ha hb hab
  have hn : z - t ≠ w - t := sub_left_injective.ne hzw
  have h := strictConvex_norm_lift.2 (Set.mem_univ (z - t))
    (Set.mem_univ (w - t)) hn ha hb hab
  have ht : a • t + b • t = t := by rw [← add_smul, hab, one_smul]
  have he : a • (z - t) + b • (w - t) = a • z + b • w - t := by
    calc
      _ = a • z + b • w - (a • t + b • t) := by
        simp only [smul_sub]
        abel
      _ = _ := by rw [ht]
  dsimp only at h
  rw [he] at h
  dsimp only [kernel]
  simp only [smul_eq_mul] at h ⊢
  have hc : a * ‖lift (-t)‖ + b * ‖lift (-t)‖ = ‖lift (-t)‖ := by
    rw [← add_mul, hab, one_mul]
  nlinarith only [h, hc]

theorem objective_strict_convex (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    StrictConvexOn ℝ Set.univ (objective μ) := by
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw hzw a b ha hb hab
  have hk (t : ℂ) := (kernel_strict_convex t).2 hz hw hzw ha hb hab
  have hf := integrable_kernel μ (a • z + b • w)
  have hg := ((integrable_kernel μ z).smul a).add ((integrable_kernel μ w).smul b)
  change (∫ t, kernel (a • z + b • w) t ∂μ) <
    a • (∫ t, kernel z t ∂μ) + b • (∫ t, kernel w t ∂μ)
  rw [← integral_smul, ← integral_smul, ← integral_add]
  · refine lt_of_le_of_ne (integral_mono hf hg fun t => (hk t).le) ?_
    intro he
    have heq := (integral_eq_iff_of_ae_le hf hg
      (Eventually.of_forall fun t => (hk t).le)).mp he
    obtain ⟨t, ht⟩ := heq.exists
    exact (hk t).ne ht
  · exact (integrable_kernel μ z).smul a
  · exact (integrable_kernel μ w).smul b

theorem norm_lift_le (z : ℂ) : ‖lift z‖ ≤ ‖z‖ + 1 := by
  calc
    ‖lift z‖ ≤ ‖lift z - lift 0‖ + ‖lift 0‖ := norm_le_norm_sub_add _ _
    _ = ‖z‖ + 1 := by simp [norm_lift_sub, norm_lift]

theorem kernel_lower (s t : ℂ) : ‖s‖ - 2 * ‖t‖ - 1 ≤ kernel s t := by
  have hst : ‖s - t‖ ≤ ‖lift (s - t)‖ := WithLp.norm_snd_le ℝ (lift (s - t))
  have hs : ‖s‖ ≤ ‖s - t‖ + ‖t‖ := norm_le_norm_sub_add _ _
  have ht := norm_lift_le (-t)
  simp only [norm_neg] at ht
  dsimp only [kernel]
  linarith

theorem exists_ball_mass (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∃ n : ℕ, (1 / 2 : ℝ) < μ.real (Metric.closedBall 0 (n : ℝ)) := by
  by_contra! h
  have hm (n : ℕ) : μ (Metric.closedBall 0 (n : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
    simpa [measureReal_def] using h n
  have hc : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact Set.mem_iUnion.mpr ⟨n, by simpa [Metric.mem_closedBall] using hn.le⟩
  have hmono : Monotone (fun n : ℕ => Metric.closedBall (0 : ℂ) (n : ℝ)) := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij)
  have he : μ (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    rw [hmono.measure_iUnion]
    exact iSup_le hm
  rw [hc, measure_univ] at he
  norm_num at he

theorem objective_lower (μ : Measure ℂ) [IsProbabilityMeasure μ] (R : ℝ) (s : ℂ) :
    (2 * μ.real (Metric.closedBall 0 R) - 1) * ‖s‖ -
        μ.real (Metric.closedBall 0 R) * (2 * R + 1) ≤ objective μ s := by
  classical
  let B := Metric.closedBall (0 : ℂ) R
  let v := 2 * ‖s‖ - (2 * R + 1)
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hi : Integrable (B.indicator (fun _ : ℂ => v)) μ :=
    (integrable_const v).indicator hB
  have hp (t : ℂ) : -‖s‖ + B.indicator (fun _ : ℂ => v) t ≤ kernel s t := by
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
      have ht' : ‖t‖ ≤ R := by simpa [B, Metric.mem_closedBall] using ht
      have hlo := kernel_lower s t
      dsimp only [v]
      linarith
    · rw [Set.indicator_of_notMem ht, add_zero]
      exact (abs_le.mp (kernel_bound s t)).1
  calc
    _ = ∫ t : ℂ, -‖s‖ + B.indicator (fun _ : ℂ => v) t ∂μ := by
      rw [integral_add (integrable_const _) hi, integral_const,
        integral_indicator_const v hB]
      simp only [probReal_univ, smul_eq_mul]
      dsimp only [v, B]
      ring
    _ ≤ _ := integral_mono ((integrable_const _).add hi) (integrable_kernel μ s) hp

theorem linear_norm_coercive (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun z : ℂ => a * ‖z‖ + b) (cocompact ℂ) atTop := by
  have ht : Tendsto (fun z : ℂ => a * ‖z‖) (cocompact ℂ) atTop :=
    Filter.Tendsto.const_mul_atTop ha (tendsto_norm_cocompact_atTop (E := ℂ))
  exact tendsto_atTop_add_const_right (cocompact ℂ) b ht

theorem objective_coercive (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Tendsto (objective μ) (cocompact ℂ) atTop := by
  obtain ⟨n, hn⟩ := exists_ball_mass μ
  have hp : 0 < 2 * μ.real (Metric.closedBall 0 (n : ℝ)) - 1 := by linarith
  have ht := linear_norm_coercive (2 * μ.real (Metric.closedBall 0 (n : ℝ)) - 1)
    (-(μ.real (Metric.closedBall 0 (n : ℝ)) * (2 * (n : ℝ) + 1))) hp
  apply tendsto_atTop_mono (objective_lower μ (n : ℝ))
  simpa only [sub_eq_add_neg] using ht

theorem exists_unique_minimizer (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∃! s, ∀ t, objective μ s ≤ objective μ t := by
  obtain ⟨s, hs⟩ := (continuous_objective μ).exists_forall_le (objective_coercive μ)
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact (objective_strict_convex μ).eq_of_isMinOn (fun x _ => ht x)
    (fun x _ => hs x) (Set.mem_univ t) (Set.mem_univ s)

noncomputable def center (μ : ProbabilityMeasure ℂ) : ℂ :=
  (exists_unique_minimizer (μ : Measure ℂ)).choose

noncomputable def universalKernel : ProbabilityTheory.Kernel (ProbabilityMeasure ℂ) ℂ :=
  ⟨fun μ => (μ : Measure ℂ), measurable_subtype_coe⟩

noncomputable def minValue (μ : ProbabilityMeasure ℂ) : ℝ :=
  ⨅ n, objective (μ : Measure ℂ) (TopologicalSpace.denseSeq ℂ n)

end EuclideanFiveColor.Location

namespace EuclideanFiveColor.CosetCenter
open ProbabilityTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

structure Embedding (G : Type*) [CommGroup G] [MeasurableSpace G] where
  hom : Multiplicative ℂ →* G
  measurableEmbedding : MeasurableEmbedding (fun z : ℂ => hom (Multiplicative.ofAdd z))

namespace Embedding

variable (e : Embedding G)

def j (z : ℂ) : G := e.hom (Multiplicative.ofAdd z)

@[simp] theorem j_zero : e.j 0 = 1 := e.hom.map_one
@[simp] theorem j_add (z w : ℂ) : e.j (z + w) = e.j z * e.j w := e.hom.map_mul _ _
@[simp] theorem j_neg (z : ℂ) : e.j (-z) = (e.j z)⁻¹ := e.hom.map_inv _
@[simp] theorem j_sub (z w : ℂ) : e.j (z - w) = e.j z / e.j w := e.hom.map_div _ _

def ordinary : Subgroup G := e.hom.range

noncomputable def coordinate : G → ℂ := Function.extend e.j id (fun _ => 0)

theorem measurable_coordinate : Measurable e.coordinate :=
  e.measurableEmbedding.measurable_extend measurable_id measurable_const

variable [MeasurableMul₂ G] [MeasurableInv G]

def coset (z : G) : Set G := {d | d / z ∈ e.ordinary}

noncomputable def frequencyMeasure (μ : Measure G) (z : G) : Measure ℂ :=
  (μ.restrict (e.coset z)).map (fun d => e.coordinate (d / z))

noncomputable def parameterKernel : Kernel (ProbabilityMeasure G × G) G :=
  ⟨fun p => (p.1 : Measure G), measurable_subtype_coe.comp measurable_fst⟩

instance parameterKernel_markov : IsMarkovKernel (parameterKernel (G := G)) :=
  ⟨fun p => by change IsProbabilityMeasure (p.1 : Measure G); infer_instance⟩

noncomputable def frequencyLaw (μ : ProbabilityMeasure G) (z : G) : ProbabilityMeasure ℂ :=
  if h : (μ : Measure G) (e.coset z) = 0 then ⟨Measure.dirac 0, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  else
    letI : IsProbabilityMeasure ((μ : Measure G)[|e.coset z]) :=
      cond_isProbabilityMeasure h
    ⟨((μ : Measure G)[|e.coset z]).map (fun d => e.coordinate (d / z)),
      by first | infer_instance | exact Measure.isProbabilityMeasure_map (e.measurable_coordinate.comp (measurable_id.div_const z)).aemeasurable⟩

noncomputable def center (μ : ProbabilityMeasure G) (z : G) : G :=
  z * e.j (Location.center (e.frequencyLaw μ z))

end Embedding
end EuclideanFiveColor.CosetCenter

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

abbrev E := algebraicClosure ℚ ℂ

def K : Subgroup Circle where
  carrier := {u | IsAlgebraic ℚ (u : ℂ)}
  one_mem' := by simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  mul_mem' := by intro a b ha hb; exact ha.mul hb
  inv_mem' := by intro a ha; exact ha.inv

/-- A separate synonym ensures that the dual uses the discrete topology,
not the Euclidean topology inherited by the embedded algebraic field. -/
def DiscreteE := Multiplicative E deriving CommGroup
instance instTopologicalSpaceDiscreteE : TopologicalSpace DiscreteE := ⊥
instance instDiscreteTopologyDiscreteE : DiscreteTopology DiscreteE := ⟨rfl⟩
abbrev D := PontryaginDual DiscreteE

/-- The inclusion into the usual complex plane, with no continuity assertion
needed on its discrete domain. -/
def embed (z : DiscreteE) : ℂ := ((Multiplicative.toAdd z : E) : ℂ)

@[simp] theorem embed_one : embed 1 = 0 := rfl
@[simp] theorem embed_mul (z w : DiscreteE) : embed (z * w) = embed z + embed w := rfl

/-- The manuscript's ordinary character parametrization. -/
def j (ξ : ℂ) : D where
  toFun z := Circle.exp (inner ℝ ξ (embed z))
  map_one' := by simp
  map_mul' z w := by simp only [embed_mul, inner_add_right, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem j_apply (ξ : ℂ) (z : DiscreteE) :
    j ξ z = Circle.exp (inner ℝ ξ (embed z)) := rfl

@[simp] theorem j_zero : j 0 = 1 := by
  apply PontryaginDual.ext
  intro z
  simp

@[simp] theorem j_add (ξ η : ℂ) : j (ξ + η) = j ξ * j η := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ (ξ + η) (embed z)) =
    Circle.exp (inner ℝ ξ (embed z)) * Circle.exp (inner ℝ η (embed z))
  rw [inner_add_left, Circle.exp_add]

def jHom : Multiplicative ℂ →* D where
  toFun ξ := j (Multiplicative.toAdd ξ)
  map_one' := j_zero
  map_mul' ξ η := j_add (Multiplicative.toAdd ξ) (Multiplicative.toAdd η)

/-- The subgroup C is not replaced by its closure. -/
def C : Subgroup D := jHom.range

theorem continuous_j : Continuous j := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.inner continuous_const)

instance instMeasurableSpaceD : MeasurableSpace D := borel D
instance instBorelSpaceD : BorelSpace D := ⟨rfl⟩

/-- Multiplication of the argument of a character. -/
def scaleE (a : E) : DiscreteE →ₜ* DiscreteE where
  toFun z := Multiplicative.ofAdd (a * Multiplicative.toAdd z)
  map_one' := by change Multiplicative.ofAdd (a * 0) = 1; simp
  map_mul' z w := by
    change Multiplicative.ofAdd (a * (_ + _)) = _
    rw [mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

def scalar (a : E) (d : D) : D := d.comp (scaleE a)

@[simp] theorem scalar_apply (a : E) (d : D) (z : DiscreteE) :
    scalar a d z = d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)) := rfl

@[simp] theorem scalar_one (d : D) : scalar 1 d = d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (1 * Multiplicative.toAdd z)) = d z
  rw [one_mul]
  rfl

@[simp] theorem scalar_mul (a b : E) (d : D) :
    scalar a (scalar b d) = scalar (a * b) d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (b * (a * Multiplicative.toAdd z))) =
    d (Multiplicative.ofAdd ((a * b) * Multiplicative.toAdd z))
  rw [mul_left_comm, ← mul_assoc]

@[simp] theorem scalar_add (a b : E) (d : D) :
    scalar (a + b) d = scalar a d * scalar b d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((a + b) * Multiplicative.toAdd z)) = _
  rw [add_mul]
  exact map_mul d _ _

@[simp] theorem scalar_j (a : E) (ξ : ℂ) :
    scalar a (j ξ) = j (conj (a : ℂ) * ξ) := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ ξ ((a : ℂ) * embed z)) = _
  rw [j_apply]
  congr 1
  simp only [Complex.inner, map_mul, starRingEnd_self_apply]
  congr 1
  ring

theorem scalar_mem_C (a : E) {d : D} (hd : d ∈ C) : scalar a d ∈ C := by
  obtain ⟨ξ, rfl⟩ := hd
  exact ⟨Multiplicative.ofAdd (conj (a : ℂ) * Multiplicative.toAdd ξ), scalar_j a _ |>.symm⟩

def kCoeff (u : K) : E := ⟨(u.val : ℂ), mem_algebraicClosure_iff.mpr u.property⟩

@[simp] theorem kCoeff_one : kCoeff 1 = 1 := rfl
@[simp] theorem kCoeff_mul (u v : K) : kCoeff (u * v) = kCoeff u * kCoeff v := rfl

def scalarHom (a : E) : D →* D where
  toFun := scalar a
  map_one' := by apply PontryaginDual.ext; intro z; rfl
  map_mul' d e := by apply PontryaginDual.ext; intro z; rfl

instance instMulActionSubtypeCircleMemSubgroupKD : MulAction K D where
  smul u d := scalar (kCoeff u) d
  one_smul d := scalar_one d
  mul_smul u v d := (scalar_mul (kCoeff u) (kCoeff v) d).symm

abbrev Cosets := D ⧸ C

def cosetScalar (u : K) : Cosets →* Cosets :=
  QuotientGroup.map C C (scalarHom (kCoeff u)) (fun _ h => scalar_mem_C _ h)

instance instMulActionSubtypeCircleMemSubgroupKCosets : MulAction K Cosets where
  smul u q := cosetScalar u q
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H d =>
      change QuotientGroup.mk (scalar 1 d) = QuotientGroup.mk d
      rw [scalar_one]
  mul_smul u v q := by
    induction q using QuotientGroup.induction_on with
    | H d =>
      change QuotientGroup.mk (scalar (kCoeff (u * v)) d) =
        QuotientGroup.mk (scalar (kCoeff u) (scalar (kCoeff v) d))
      rw [scalar_mul, kCoeff_mul]

@[simp] theorem quotient_equivariant (u : K) (d : D) :
    QuotientGroup.mk (u • d) = u • (QuotientGroup.mk d : Cosets) := rfl

@[simp] theorem scalar_neg (a : E) (d : D) : scalar (-a) d = (scalar a d)⁻¹ := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((-a) * Multiplicative.toAdd z)) =
    (d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)))⁻¹
  rw [neg_mul]
  exact map_inv d _

@[simp] theorem scalar_sub (a b : E) (d : D) :
    scalar (a - b) d = scalar a d / scalar b d := by
  rw [sub_eq_add_neg, scalar_add, scalar_neg, div_eq_mul_inv]

def minusOne : K := ⟨-1, by
  change IsAlgebraic ℚ (-1 : ℂ)
  exact isAlgebraic_one.neg⟩

@[simp] theorem kCoeff_minusOne : kCoeff minusOne = -1 := rfl

/-- Rational tests identify the frequency of a real continuous character. -/
theorem frequency_zero_of_rational_tests (a : ℝ)
    (h : ∀ q : ℚ, Circle.exp (a * (q : ℝ)) = 1) : a = 0 := by
  have heq : (fun t : ℝ => Circle.exp (a * t)) = fun _ => 1 :=
    Rat.denseRange_cast.equalizer
      (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
      continuous_const (funext h)
  have hpi : Circle.exp Real.pi ≠ 1 := by
    intro hone
    have ha := congrArg (fun u : Circle => (u : ℂ).arg) hone
    rw [Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl] at ha
    simp at ha
  by_contra ha
  have ht := congrFun heq (Real.pi / a)
  have hmul : a * (Real.pi / a) = Real.pi := by field_simp
  rw [hmul] at ht
  exact hpi ht

def imagUnit : E := ⟨Complex.I, mem_algebraicClosure_iff.mpr
  (IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]
    exact isAlgebraic_one.neg))⟩

@[simp] theorem coe_imagUnit : (imagUnit : ℂ) = Complex.I := rfl

theorem j_eq_one_iff (ξ : ℂ) : j ξ = 1 ↔ ξ = 0 := by
  constructor
  · intro h
    have hre : ξ.re = 0 := frequency_zero_of_rational_tests ξ.re (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd (q : E))) h
      change Circle.exp (inner ℝ ξ ((q : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    have him : ξ.im = 0 := frequency_zero_of_rational_tests ξ.im (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd ((q : E) * imagUnit))) h
      change Circle.exp (inner ℝ ξ (((q : E) * imagUnit : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    exact Complex.ext hre him
  · rintro rfl
    exact j_zero

@[simp] theorem j_neg (ξ : ℂ) : j (-ξ) = (j ξ)⁻¹ :=
  map_inv jHom (Multiplicative.ofAdd ξ)

@[simp] theorem j_sub (ξ η : ℂ) : j (ξ - η) = j ξ / j η := by
  rw [sub_eq_add_neg, j_add, j_neg, div_eq_mul_inv]

theorem j_injective : Function.Injective j := by
  intro ξ η h
  apply sub_eq_zero.mp
  apply (j_eq_one_iff _).mp
  rw [j_sub, h, div_self']

theorem j_measurableEmbedding : MeasurableEmbedding j :=
  continuous_j.measurableEmbedding j_injective

/-- The complex algebraic closure used above is precisely F(i) from the source,
not a different countable plane. -/
theorem algebraic_complex_iff_coordinates (z : ℂ) :
    IsAlgebraic ℚ z ↔ IsAlgebraic ℚ z.re ∧ IsAlgebraic ℚ z.im := by
  have hi : IsAlgebraic ℚ Complex.I := mem_algebraicClosure_iff.mp imagUnit.property
  have hhalf : IsAlgebraic ℚ ((2 : ℂ)⁻¹) := (isAlgebraic_natCast 2).inv
  constructor
  · intro hz
    have hc : IsAlgebraic ℚ (conj z) :=
      IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom hz
    constructor
    · apply (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
        Complex.ofReal_injective).mp
      have h := (hz.add hc).mul hhalf
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (apply Complex.ext <;> simp; ring)
    · apply (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
        Complex.ofReal_injective).mp
      have h := ((hz.sub hc).mul hhalf).mul hi.inv
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (apply Complex.ext <;> simp; ring)
  · rintro ⟨hr, hi'⟩
    have hr' : IsAlgebraic ℚ (z.re : ℂ) := hr.algebraMap
    have hi'' : IsAlgebraic ℚ (z.im : ℂ) := hi'.algebraMap
    simpa only [Complex.re_add_im] using hr'.add (hi''.mul hi)

abbrev F := algebraicClosure ℚ ℝ

/-- The real-algebraic inclusion into the algebraic plane. -/
def ofF : F →+* E where
  toFun t := ⟨(t : ℝ), mem_algebraicClosure_iff.mpr
    ((mem_algebraicClosure_iff.mp t.property).algebraMap (A := ℂ))⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp] theorem coe_ofF (t : F) : (ofF t : ℂ) = (t : ℝ) := rfl

def DiscreteF := Multiplicative F deriving CommGroup
instance instTopologicalSpaceDiscreteF : TopologicalSpace DiscreteF := ⊥
instance instDiscreteTopologyDiscreteF : DiscreteTopology DiscreteF := ⟨rfl⟩
abbrev DF := PontryaginDual DiscreteF

def embedF (t : DiscreteF) : ℝ := (Multiplicative.toAdd t : F)
@[simp] theorem embedF_one : embedF 1 = 0 := rfl
@[simp] theorem embedF_mul (t s : DiscreteF) : embedF (t * s) = embedF t + embedF s := rfl

/-- Standard frequencies for the real algebraic line; again use the actual image. -/
def jF (l : ℝ) : DF where
  toFun t := Circle.exp (l * embedF t)
  map_one' := by simp
  map_mul' t s := by simp only [embedF_mul, mul_add, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem jF_apply (l : ℝ) (t : DiscreteF) :
    jF l t = Circle.exp (l * (Multiplicative.toAdd t : F)) := rfl

/-- The dual restriction to the line aF. -/
def lineHom (a : E) : DiscreteF →ₜ* DiscreteE where
  toFun t := Multiplicative.ofAdd (a * ofF (Multiplicative.toAdd t))
  map_one' := by change Multiplicative.ofAdd (a * ofF 0) = 1; simp
  map_mul' t s := by
    change Multiplicative.ofAdd (a * ofF (_ + _)) = _
    rw [map_add, mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

def restrictLine (a : E) (d : D) : DF := d.comp (lineHom a)

def L (a : E) : Set D := {d | Continuous (fun t : F =>
  d (Multiplicative.ofAdd (a * ofF t)))}

def reF (z : E) : F := ⟨(z : ℂ).re, mem_algebraicClosure_iff.mpr
  ((algebraic_complex_iff_coordinates _).mp (mem_algebraicClosure_iff.mp z.property)).1⟩
def imF (z : E) : F := ⟨(z : ℂ).im, mem_algebraicClosure_iff.mpr
  ((algebraic_complex_iff_coordinates _).mp (mem_algebraicClosure_iff.mp z.property)).2⟩

@[simp] theorem coe_reF (z : E) : (reF z : ℝ) = (z : ℂ).re := rfl
@[simp] theorem coe_imF (z : E) : (imF z : ℝ) = (z : ℂ).im := rfl

@[simp] theorem scalar_line (a b : E) (d : D) : scalar a d ∈ L b ↔ d ∈ L (a * b) := by
  change Continuous (fun t : F => d (Multiplicative.ofAdd (a * (b * ofF t)))) ↔ _
  simp only [← mul_assoc]
  rfl

@[simp] theorem kCoeff_inv (u : K) : kCoeff u⁻¹ = (kCoeff u)⁻¹ := by
  apply Subtype.ext
  change ((u.val)⁻¹ : Circle).val = (u.val : ℂ)⁻¹
  exact Circle.coe_inv u.val

@[simp] theorem kCoeff_ne_zero (u : K) : kCoeff u ≠ 0 := by
  intro h
  have hz : (u.val : ℂ) = 0 := congrArg (fun x : E => (x : ℂ)) h
  exact u.val.coe_ne_zero hz

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.RelativeCenters
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Y G : Type*} [MeasurableSpace Y] [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (e : CosetCenter.Embedding G)

noncomputable def probabilityKernel (κ : Kernel Y G) [IsMarkovKernel κ]
    (y : Y) : ProbabilityMeasure G := ⟨κ y, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

noncomputable def cosetMass (κ : Kernel Y G) [IsMarkovKernel κ] (p : Y × G) : ℝ≥0∞ :=
  κ p.1 (e.coset p.2)

/-- The relative difference law uses two independent samples of the same
conditional probability law; it is not an independent marginal difference. -/
noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measure G := ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

variable {X : Type*} [MeasurableSpace X]

noncomputable def centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ] (d : X → G) (p : X → Y) (x : X) : G :=
  e.center (probabilityKernel (condDistrib d p μ) (p x)) (d x)

section ConditionalLaw
variable {H : Type*} [MeasurableSpace H]

noncomputable def centerKernel (κ : Kernel Y G) [IsMarkovKernel κ] : Kernel Y G :=
  (Kernel.id ×ₖ κ).map (fun q : Y × G => e.center (probabilityKernel κ q.1) q.2)

end ConditionalLaw

end EuclideanFiveColor.RelativeCenters

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor.RelativeCenters

noncomputable def ordinaryEmbedding : EuclideanFiveColor.CosetCenter.Embedding D :=
  ⟨jHom, j_measurableEmbedding⟩

@[simp] theorem ordinaryEmbedding_j (t : ℂ) : ordinaryEmbedding.j t = j t := rfl
@[simp] theorem ordinaryEmbedding_ordinary : ordinaryEmbedding.ordinary = C := rfl

noncomputable def frequencyIsometry (u : K) : ℂ →ₗᵢ[ℝ] ℂ where
  toFun z := conj (u.val : ℂ) * z
  map_add' _ _ := mul_add _ _ _
  map_smul' a z := by simp only [RingHom.id_apply, mul_smul_comm]
  norm_map' z := by
    change ‖conj (u.val : ℂ) * z‖ = ‖z‖
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]

noncomputable def frequencyRotation (u : K) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  (frequencyIsometry u).toLinearIsometryEquiv rfl

@[simp] theorem frequencyRotation_apply (u : K) (z : ℂ) :
    frequencyRotation u z = conj (u.val : ℂ) * z := rfl

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_PhaseEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators

open scoped BigOperators
open Polynomial
namespace EuclideanFiveColor.PhaseEncoding

section

def phases {m : ℕ} (z : Fin m → Circle) : Multiset ℂ :=
  Finset.univ.val.map (fun i => (z i : ℂ))

def elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) : ℂ := (phases z).esymm n

/-- Exactly the elementary symmetric functions of degrees 1,…,m. -/
def encoding {m : ℕ} (z : Fin m → Circle) : Fin m → ℂ :=
  fun i => elem z (i.val + 1)

def phasePolynomial {m : ℕ} (z : Fin m → Circle) : ℂ[X] :=
  ∏ i : Fin m, (X - C (z i : ℂ))

@[simp] theorem card_phases {m : ℕ} (z : Fin m → Circle) : (phases z).card = m := by
  simp [phases]

@[simp] theorem elem_zero {m : ℕ} (z : Fin m → Circle) : elem z 0 = 1 := by
  simp [elem, Multiset.esymm]

@[simp] theorem eval_at_phase {m : ℕ} (z : Fin m → Circle) (i : Fin m) :
    (phasePolynomial z).eval (z i : ℂ) = 0 := by
  rw [phasePolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

open scoped BigOperators

/-- Newton reconstruction from the entire sequence of power sums. -/
def fromPowers (p : ℕ → ℂ) (n : ℕ) : ℂ :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1 : ℂ)⁻¹ * (-1) ^ (k + 2) *
      ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) * fromPowers p i * p (k + 1 - i)
termination_by n
decreasing_by
  exact i.isLt

end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]

/-- The measurable phase encoding, defined without a measurable enumeration. -/
def kernelEncoding (β : Kernel Y G) (χ : G → ℂ) (m : ℕ) (y : Y) : Fin m → ℂ :=
  fun i => fromPowers (fun n => (m : ℂ) * ∫ d, χ d ^ n ∂β y) (i.val + 1)

end

end EuclideanFiveColor.PhaseEncoding

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_PhaseCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

open scoped BigOperators
namespace EuclideanFiveColor.PhaseCollision

section

variable {ι κ V : Type*} [Fintype ι] [Fintype κ]
local instance instDecidableEq_solutions_1 : DecidableEq κ := Classical.decEq κ

/-- Ordered distinct pairs in one assigned bin. -/
def repeatedPairs (s : Finset ι) (f : ι → κ) : Finset (ι × ι) := by
  classical
  exact (s ×ˢ s).filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)

variable [PseudoMetricSpace V]

/-- Ordered distinct phase pairs within a fixed distance. -/
def closePairs (v : ι → V) (r : ℝ) : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ dist (v p.1) (v p.2) ≤ r)

end

open MeasureTheory
open scoped BigOperators

end EuclideanFiveColor.PhaseCollision

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial

open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.AverageErrors
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

/-- The fraction of indices whose nonnegative error is below a threshold. -/
def goodFraction (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun i => e i x < t)).card : ℝ) / Fintype.card ι

end EuclideanFiveColor.AverageErrors

namespace EuclideanFiveColor.EncodedCollision
local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := borel Circle
open MeasureTheory
open scoped BigOperators
open PhaseEncoding AverageErrors PhaseCollision

end EuclideanFiveColor.EncodedCollision

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators

open MeasureTheory

open MeasureTheory ProbabilityTheory

namespace EuclideanFiveColor.FiniteModule
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := borel Circle

end EuclideanFiveColor.FiniteModule

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators

namespace PlaneFiveColor.Spectral
open MeasureTheory

/-- The actual character on the algebraic parameter line, forgetting only
its discrete-domain continuity proof. -/
def lineCharacter (a : E) (d : D) : Multiplicative F →* Circle :=
  (restrictLine a d).toMonoidHom

end PlaneFiveColor.Spectral

end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_InvariantMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
/-! A discrete abelian invariant mean, constructed from weighted cube
averages. Repeated group elements keep their multiplicities. -/
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

local instance instDecidableEq_solutions (α : Type*) : DecidableEq α := Classical.decEq α

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- Translation acts on all bounded functions because the domain is discrete. -/
def shift (g : G) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply (g x : G) (f : G →ᵇ ℝ) : shift g f x = f (x+g) := rfl

@[simp] lemma shift_add (g : G) (f h : G →ᵇ ℝ) : shift g (f+h) = shift g f + shift g h := by
  ext x
  rfl

@[simp] lemma shift_sub (g : G) (f h : G →ᵇ ℝ) : shift g (f-h) = shift g f - shift g h := by
  ext x
  rfl

@[simp] lemma shift_smul (g : G) (c : ℝ) (f : G →ᵇ ℝ) : shift g (c • f) = c • shift g f := by
  ext x
  rfl

lemma shift_norm_le (g : G) (f : G →ᵇ ℝ) : ‖shift g f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

/-- A single cyclic Cesàro average, always with a positive denominator. -/
def single (g : G) (n : ℕ) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (n+1), shift (k • g) f

@[simp] lemma single_apply (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n f x = ((n+1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n+1), f (x+k • g) := by
  simp [single]

lemma single_norm_le (g : G) (n : ℕ) (f : G →ᵇ ℝ) : ‖single g n f‖ ≤ ‖f‖ := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  calc
    ‖single g n f‖ = ((n+1 : ℕ) : ℝ)⁻¹ * ‖∑ k ∈ Finset.range (n+1), shift (k • g) f‖ := by
      rw [single, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (∑ _k ∈ Finset.range (n+1), ‖f‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => shift_norm_le _ _)
    _ = ‖f‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

@[simp] lemma single_add (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f+h) = single g n f + single g n h := by
  simp only [single, shift_add, Finset.sum_add_distrib, smul_add]

@[simp] lemma single_sub (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f-h) = single g n f - single g n h := by
  simp only [single, shift_sub, Finset.sum_sub_distrib, smul_sub]

@[simp] lemma single_smul (g : G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    single g n (c • f) = c • single g n f := by
  simp only [single, shift_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

lemma single_shift (g h : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift h f) = shift h (single g n f) := by
  ext x
  simp only [single_apply, shift_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  abel

lemma single_const (g : G) (n : ℕ) (c : ℝ) :
    single g n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  ext x
  simp only [single_apply, BoundedContinuousFunction.const_apply, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]

lemma single_nonneg (g : G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ single g n f x := by
  intro x
  rw [single_apply]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun k hk => hf _

lemma single_telescope (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift g f - f) x =
      ((n+1 : ℕ) : ℝ)⁻¹ * (f (x+(n+1) • g) - f x) := by
  rw [single_apply]
  congr 1
  have he (k : ℕ) : (shift g f - f) (x+k • g) =
      f (x+(k+1) • g) - f (x+k • g) := by
    simp only [BoundedContinuousFunction.sub_apply, shift_apply, add_nsmul, one_nsmul, add_assoc]
  simp_rw [he]
  simpa only [zero_nsmul, add_zero] using Finset.sum_range_sub (fun k => f (x+k • g)) (n+1)

lemma single_coboundary_norm (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖single g n (shift g f - f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [single_telescope, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ)⁻¹)]
  have hb : |f (x+(n+1) • g) - f x| ≤ 2 * ‖f‖ := by
    calc
      _ ≤ |f (x+(n+1) • g)| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = _ := by ring
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Multiplicities in the cube are explicitly retained through composition. -/
def cube : List G → ℕ → (G →ᵇ ℝ) → (G →ᵇ ℝ)
  | [], _, f => f
  | g::L, n, f => single g n (cube L n f)

lemma cube_norm_le (L : List G) (n : ℕ) (f : G →ᵇ ℝ) : ‖cube L n f‖ ≤ ‖f‖ := by
  induction L with
  | nil => exact le_rfl
  | cons g L ih => exact (single_norm_le g n _).trans ih

lemma cube_shift (L : List G) (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    cube L n (shift g f) = shift g (cube L n f) := by
  induction L with
  | nil => rfl
  | cons h L ih => simp only [cube, ih, single_shift]

@[simp] lemma cube_add (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f+h) = cube L n f + cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_add]

@[simp] lemma cube_sub (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f-h) = cube L n f - cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_sub]

@[simp] lemma cube_smul (L : List G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    cube L n (c • f) = c • cube L n f := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_smul]

lemma cube_const (L : List G) (n : ℕ) (c : ℝ) :
    cube L n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_const]

lemma cube_nonneg (L : List G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ cube L n f x := by
  induction L with
  | nil => exact hf
  | cons g L ih => exact single_nonneg g n _ ih

/-- Each listed generator has the same boundary bound, independently of the
length of the list and without an injective image assumption. -/
lemma cube_coboundary_norm (L : List G) (g : G) (hg : g ∈ L) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖cube L n (shift g f-f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  induction L with
  | nil => simp at hg
  | cons h L ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [cube, cube_sub, cube_shift]
      apply (single_coboundary_norm g n _).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cube_norm_le L n f) (by norm_num)) (by positivity)
    · exact (single_norm_le h n _).trans (ih hg)

/-- The directed weighted-cube averages. -/
def approx (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ℝ :=
  cube i.1.toList i.2 f 0

lemma approx_norm_le (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ‖approx i f‖ ≤ ‖f‖ :=
  ((cube i.1.toList i.2 f).norm_coe_le_norm 0).trans (cube_norm_le _ _ _)

/-- One fixed ultrafilter is used for all functions. -/
def averagingUF (G : Type*) [AddCommGroup G] : Ultrafilter (Finset G × ℕ) :=
  Ultrafilter.of atTop

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma averagingUF_le : (averagingUF G : Filter (Finset G × ℕ)) ≤ atTop :=
  Ultrafilter.of_le _

lemma approx_has_limit (f : G →ᵇ ℝ) :
    ∃ r : ℝ, Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 r) := by
  have hb : (Ultrafilter.map (fun i => approx i f) (averagingUF G) : Filter ℝ) ≤
      𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro i
    exact abs_le.mp (approx_norm_le i f)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (fun i => approx i f) (averagingUF G)) hb
  exact ⟨r, hr⟩

/-- The invariant mean, as the limit of the multiplicity-preserving averages. -/
def mean (f : G →ᵇ ℝ) : ℝ :=
  (averagingUF G : Filter _).limUnder (fun i => approx i f)

lemma tendsto_approx (f : G →ᵇ ℝ) :
    Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 (mean f)) :=
  tendsto_nhds_limUnder (approx_has_limit f)

lemma mean_add (f h : G →ᵇ ℝ) : mean (f+h) = mean f + mean h := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).add (tendsto_approx h) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [approx, cube_add, BoundedContinuousFunction.add_apply]

lemma mean_smul (c : ℝ) (f : G →ᵇ ℝ) : mean (c • f) = c * mean f := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).const_mul c using 1
  all_goals try with_reducible_and_instances rfl
  simp only [approx, cube_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]

lemma mean_const (c : ℝ) : mean (BoundedContinuousFunction.const G c) = c := by
  apply Tendsto.limUnder_eq
  convert (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
    (averagingUF G : Filter _) (𝓝 c)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [approx, cube_const, BoundedContinuousFunction.const_apply]

lemma mean_nonneg (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  exact ge_of_tendsto (tendsto_approx f) (Filter.Eventually.of_forall fun i =>
    cube_nonneg i.1.toList i.2 f hf 0)

lemma mean_norm_le (f : G →ᵇ ℝ) : ‖mean f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_approx f).norm
    (Filter.Eventually.of_forall fun i => approx_norm_le i f)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma eventually_mem (g : G) : ∀ᶠ i : Finset G × ℕ in (averagingUF G : Filter _), g ∈ i.1 := by
  classical
  apply Filter.Eventually.filter_mono averagingUF_le
  apply Filter.eventually_atTop.mpr
  refine ⟨({g}, 0), fun i hi => ?_⟩
  exact hi.1 (Finset.mem_singleton_self g)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma tendsto_index : Tendsto (fun i : Finset G × ℕ => i.2)
    (averagingUF G : Filter _) atTop := by
  apply Tendsto.mono_left _ averagingUF_le
  apply tendsto_atTop.mpr
  intro n
  apply Filter.eventually_atTop.mpr
  exact ⟨(∅, n), fun i hi => hi.2⟩

omit [DiscreteTopology G] in
lemma tendsto_boundary (f : G →ᵇ ℝ) :
    Tendsto (fun i : Finset G × ℕ => 2 * ‖f‖ / (i.2+1 : ℕ))
      (averagingUF G : Filter _) (𝓝 0) := by
  have hn : Tendsto (fun i : Finset G × ℕ => ((i.2+1 : ℕ) : ℝ))
      (averagingUF G : Filter _) atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp tendsto_index)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hn).const_mul (2 * ‖f‖)

lemma mean_shift (g : G) (f : G →ᵇ ℝ) : mean (shift g f) = mean f := by
  have hz : Tendsto (fun i : Finset G × ℕ => approx i (shift g f) - approx i f)
      (averagingUF G : Filter _) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_boundary f)
    filter_upwards [eventually_mem g] with i hi
    have h := ((cube i.1.toList i.2 (shift g f-f)).norm_coe_le_norm 0).trans
      (cube_coboundary_norm i.1.toList g (Finset.mem_toList.mpr hi) i.2 f)
    simpa only [cube_sub, BoundedContinuousFunction.sub_apply, approx] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique ((tendsto_approx _).sub (tendsto_approx _)) hz)

/-- A normalized positive shift-invariant continuous real linear functional. -/
def meanCLM : (G →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := mean, map_add' := mean_add, map_smul' := mean_smul }
    1 (by intro f; change ‖mean f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using mean_norm_le f)

@[simp] lemma meanCLM_apply (f : G →ᵇ ℝ) : meanCLM f = mean f := rfl

open MeasureTheory AddCircle

end PlaneFiveColor.InvariantMean
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Multipliers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

def lineFourier (ν : Measure D) (a : E) (t : F) : ℂ :=
  ∫ d, (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) ∂ν

end PlaneFiveColor.Spectral
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_FourierTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped BigOperators
open InvariantMean

@[simp] lemma lineFourier_zero (ν : Measure D) [IsProbabilityMeasure ν] (a : E) :
    lineFourier ν a 0 = 1 := by
  simp [lineFourier]

end PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.DifferenceFourier

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
  [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G]

noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measure G := ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

instance differenceLaw_probability (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] : IsProbabilityMeasure (differenceLaw ν κ) := by
  unfold differenceLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

end EuclideanFiveColor.DifferenceFourier

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SmallArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace EuclideanFiveColor.SmallArc
noncomputable section

def phaseSum (z : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, z ^ n

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (z : X → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖ = 1)

include hz hu

local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := borel Circle

end
end EuclideanFiveColor.SmallArc

/-! Fiberwise (possibly nonmeasurable) enumerations cause no measurability gap:
actual conditional samples lie in them by the measurable positive-atom event. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

/-- Evaluation at the exact algebraic argument. -/
def eval (a : E) : D →* Circle where
  toFun d := d (Multiplicative.ofAdd a)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma continuous_eval (a : E) : Continuous (eval a) :=
  (continuous_apply (Multiplicative.ofAdd a)).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

lemma measurable_eval_coe (a : E) : Measurable (fun d => (eval a d : ℂ)) :=
  ((show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).comp
    (continuous_eval a)).measurable

@[simp] lemma eval_zero (d : D) : eval 0 d = 1 := map_one d

end

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.DifferenceInvariant
variable {G Y : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace Y]

noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] : Measure G :=
  ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

end EuclideanFiveColor.DifferenceInvariant

/-! The scalar finite bounded-module approximation in (source-4), and its
finite-vector consequence. All functions are measurable bounded representatives. -/
namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y W : Type*} [SMul K Y] [MeasurableSpace Y] [MeasurableSpace W]

def Scalar (ν : Measure Y) (q : Y → W) : Prop :=
  ∀ H : Y → ℂ, Measurable H → (∃ C : ℝ, ∀ y, ‖H y‖ ≤ C) →
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i * Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i * Hf i y)^2 ∂ν) < ε^2

def Vector (ν : Measure Y) (q : Y → W) : Prop :=
  ∀ (m : ℕ) (H : Y → Fin m → ℂ), Measurable H →
  (∃ C : ℝ, ∀ y, ‖H y‖ ≤ C) → ∀ ε : ℝ, 0 < ε →
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2 ∂ν) < ε^2

end EuclideanFiveColor.CompactApproximation

namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y Z W : Type*} [SMul K Y] [SMul K Z]
  [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

def At (ν : Measure Y) (q : Y → W) (m : ℕ) (H : Y → Fin m → ℂ) (ε : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2 ∂ν) < ε^2

end EuclideanFiveColor.CompactApproximation

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/
namespace EuclideanFiveColor.LimitDensity
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Y : Type*} [mY : MeasurableSpace Y]

def clip (C t : ℝ) : ℝ := max (-C) (min C t)

end EuclideanFiveColor.LimitDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def fiberMean (κ : Kernel X Y) (F : X × Y → ℂ) (x : X) : ℂ :=
  ∫ y, F (x,y) ∂κ x

end EuclideanFiveColor.KernelCompact

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/

namespace EuclideanFiveColor.RectangleDensity
open MeasureTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]

abbrev Code (n : ℕ) := Fin n → Bool

def code (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (n : ℕ) (x : X) : Code n := by
  classical
  exact fun i => if x ∈ MeasurableSpace.natGeneratingSequence X i then true else false

lemma measurable_code (n : ℕ) : Measurable (code X n) := by
  classical
  apply Measurable.of_eval
  intro i
  exact measurable_const.piecewise (MeasurableSpace.measurableSet_natGeneratingSequence (α := X) i) measurable_const

def pairCode (n : ℕ) (z : X × Y) : Code n × Code n := (code X n z.1, code Y n z.2)

end EuclideanFiveColor.RectangleDensity

namespace EuclideanFiveColor.KernelCompact

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

def applyKernel (κ : Kernel Y X) (q : X → Y) (L : X × X → ℂ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ x', L (x,x') * f x' ∂κ (q x)

end
open MeasureTheory ProbabilityTheory Filter

end EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

def law (μ : Measure X) [IsFiniteMeasure μ] (q : X → Y) (hq : Measurable q) : Measure (X × X) :=
  μ ⊗ₘ (condDistrib id q μ).comap q hq

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

instance law_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) : IsProbabilityMeasure (law μ q hq) := by
  dsimp [law]; infer_instance

end EuclideanFiveColor.RelativeProduct

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_BoundedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable (X : Type*) [MeasurableSpace X]

def algebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C}
  zero_mem' := ⟨measurable_const, ⟨0, by simp⟩⟩
  one_mem' := ⟨measurable_const, ⟨1, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    exact ⟨hf.add hg, C+D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  mul_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    refine ⟨hf.mul hg, C*D, fun x => ?_⟩
    simpa only [Pi.mul_apply, norm_mul, NNReal.coe_mul] using
      mul_le_mul (hC x) (hD x) (norm_nonneg _) C.coe_nonneg
  algebraMap_mem' c := ⟨measurable_const, ‖c‖₊, fun _ => le_rfl⟩

abbrev Func := ↥(algebra X)
variable {X}
instance instCoeFunFuncForallComplex : CoeFun (Func X) (fun _ => X → ℂ) := ⟨Subtype.val⟩

lemma measurable (f : Func X) : Measurable (f : X → ℂ) := f.property.1

def bound (f : Func X) : ℝ≥0 := f.property.2.choose
lemma norm_le_bound (f : Func X) (x : X) : ‖f x‖ ≤ bound f := f.property.2.choose_spec x

@[ext] lemma ext {f g : Func X} (h : ∀ x, f x = g x) : f = g := Subtype.ext (funext h)
@[simp] lemma add_apply (f g : Func X) (x : X) : (f+g) x = f x + g x := rfl
@[simp] lemma mul_apply (f g : Func X) (x : X) : (f*g) x = f x * g x := rfl
@[simp] lemma sub_apply (f g : Func X) (x : X) : (f-g) x = f x - g x := rfl
@[simp] lemma zero_apply (x : X) : (0 : Func X) x = 0 := rfl
@[simp] lemma one_apply (x : X) : (1 : Func X) x = 1 := rfl
@[simp] lemma smul_apply (c : ℂ) (f : Func X) (x : X) : (c • f) x = c * f x := rfl
@[simp] lemma real_smul_apply (c : ℝ) (f : Func X) (x : X) : (c • f) x = c • f x := rfl

def bmConj (f : Func X) : Func X :=
  ⟨fun x => star (f x), continuous_star.measurable.comp (measurable f), bound f, fun x => by simpa using norm_le_bound f x⟩
@[simp] lemma conj_apply (f : Func X) (x : X) : bmConj f x = star (f x) := rfl

def comp {Y : Type*} [MeasurableSpace Y] (f : Func Y) (q : X → Y) (hq : Measurable q) : Func X :=
  ⟨fun x => f (q x), (measurable f).comp hq, bound f, fun x => norm_le_bound f (q x)⟩
@[simp] lemma comp_apply {Y : Type*} [MeasurableSpace Y]
    (f : Func Y) (q : X → Y) (hq : Measurable q) (x : X) : comp f q hq x = f (q x) := rfl

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma memLp (f : Func X) (p : ℝ≥0∞) : MemLp (f : X → ℂ) p μ :=
  MemLp.of_bound (measurable f).aestronglyMeasurable (bound f) (.of_forall (norm_le_bound f))

def lp (p : ℝ≥0∞) (f : Func X) : Lp ℂ p μ := (memLp μ f p).toLp f
lemma coe_lp (p : ℝ≥0∞) (f : Func X) : lp μ p f =ᵐ[μ] f := MemLp.coeFn_toLp _

lemma lp_add (p : ℝ≥0∞) (f g : Func X) : lp μ p (f+g) = lp μ p f + lp μ p g :=
  (MemLp.toLp_add (memLp μ f p) (memLp μ g p)).symm

lemma lp_smul (p : ℝ≥0∞) (c : ℝ) (f : Func X) : lp μ p (c • f) = c • lp μ p f := rfl

@[simps] def l2 : Func X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun := lp μ 2
  map_add' := lp_add μ 2
  map_smul' := lp_smul μ 2

lemma l2_ae (f : Func X) : l2 μ f =ᵐ[μ] f := coe_lp μ 2 f

lemma l2_norm_le [IsProbabilityMeasure μ] (f : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖l2 μ f‖ ≤ C := by
  have hn : ∀ᵐ x ∂μ, ‖l2 μ f x‖ ≤ C := (l2_ae μ f).mono (fun x hx => by rw [hx]; exact hf x)
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hn.exists
    exact (norm_nonneg _).trans hx
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hn

end
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma integrable (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) : Integrable (f : X → ℂ) μ :=
  (memLp μ f 1).integrable le_rfl

def expect (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) : Func Y :=
  ⟨fun y => ∫ x, f x ∂κ y, (measurable f).stronglyMeasurable.integral_kernel.measurable,
    bound f, fun y => by
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := κ y) (.of_forall (norm_le_bound f))⟩

@[simp] lemma expect_apply (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) (y : Y) :
    expect κ f y = ∫ x, f x ∂κ y := rfl

lemma expect_bound (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X)
    {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖expect κ f y‖ ≤ C := by
  simpa only [expect_apply, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ y) (.of_forall hf)

lemma expect_add (κ : Kernel Y X) [IsMarkovKernel κ] (f g : Func X) :
    expect κ (f+g) = expect κ f + expect κ g := by
  ext y; exact integral_add (integrable (κ y) f) (integrable (κ y) g)

lemma expect_smul (κ : Kernel Y X) [IsMarkovKernel κ] (c : ℝ) (f : Func X) :
    expect κ (c • f) = c • expect κ f := by
  ext y; exact integral_smul c f

@[simps] def expectLinear (κ : Kernel Y X) [IsMarkovKernel κ] : Func X →ₗ[ℝ] Func Y where
  toFun := expect κ
  map_add' := expect_add κ
  map_smul' := expect_smul κ

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

abbrev conditional (f : Func X) : Func Y := expect (condDistrib id q μ) f

def project (f : Func X) : Func X := comp (conditional μ q f) q hq

omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma project_apply (f : Func X) (x : X) :
    project μ q hq f x = conditional μ q f (q x) := rfl

end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [AddGroup K] [AddAction K X] [AddAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstVAdd K X] [MeasurableConstVAdd K Y]

instance law_probability_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) : IsProbabilityMeasure (law μ q hq) := by
  dsimp [law]; infer_instance

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

def act (g : G) (f : Func X) : Func X := comp f (fun x => g +ᵥ x) (measurable_const_vadd g)
@[simp] lemma act_apply (g : G) (f : Func X) (x : X) : act g f x = f (g +ᵥ x) := rfl

end

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable (G X : Type*) [MeasurableSpace X]
def familyAlgebra : Subalgebra ℂ (G → Func X) where
  carrier := {F | ∃ C : ℝ≥0, ∀ g x, ‖F g x‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro F H ⟨C,hC⟩ ⟨D,hD⟩
    exact ⟨C+D, fun g x => (norm_add_le _ _).trans (add_le_add (hC g x) (hD g x))⟩
  mul_mem' := by
    rintro F H ⟨C,hC⟩ ⟨D,hD⟩
    refine ⟨C*D, fun g x => ?_⟩
    change ‖F g x * H g x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hC g x) (hD g x) (norm_nonneg _) C.coe_nonneg
  algebraMap_mem' c := ⟨‖c‖₊, fun _ _ => le_rfl⟩
abbrev Family := ↥(familyAlgebra G X)
variable {G X}
instance instCoeFunFamilyForallFunc : CoeFun (Family G X) (fun _ => G → Func X) := ⟨Subtype.val⟩
instance familyRealModule : Module ℝ (Family G X) := Module.complexToReal (Family G X)

namespace Family
def bound (F : Family G X) : ℝ≥0 := F.property.choose
lemma norm_le_bound (F : Family G X) (g : G) (x : X) : ‖F g x‖ ≤ F.bound := F.property.choose_spec g x
@[ext] lemma ext {F H : Family G X} (h : ∀ g, F g = H g) : F = H := Subtype.ext (funext h)
@[simp] lemma add_apply (F H : Family G X) (g : G) : (F+H) g = F g + H g := rfl
@[simp] lemma mul_apply (F H : Family G X) (g : G) : (F*H) g = F g * H g := rfl
@[simp] lemma sub_apply (F H : Family G X) (g : G) : (F-H) g = F g - H g := rfl
@[simp] lemma zero_apply (g : G) : (0 : Family G X) g = 0 := rfl
@[simp] lemma one_apply (g : G) : (1 : Family G X) g = 1 := rfl
@[simp] lemma real_smul_apply (c : ℝ) (F : Family G X) (g : G) : (c • F) g = c • F g := rfl
@[simp] lemma complex_smul_apply (c : ℂ) (F : Family G X) (g : G) : (c • F) g = c • F g := rfl
@[simp] lemma prod_apply {ι : Type*} (s : Finset ι) (F : ι → Family G X) (g : G) :
    (∏ i ∈ s, F i) g = ∏ i ∈ s, F i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

def const (f : Func X) : Family G X := ⟨fun _ => f, BoundedMeasurable.bound f,
  fun _ => BoundedMeasurable.norm_le_bound f⟩
@[simp] lemma const_apply (f : Func X) (g : G) : const f g = f := rfl

variable [TopologicalSpace G] [DiscreteTopology G]
variable (μ : Measure X) [IsProbabilityMeasure μ]

def toL2 (F : Family G X) : G →ᵇ Lp ℂ 2 μ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => l2 μ (F g))
    continuous_of_discreteTopology F.bound (fun g => l2_norm_le μ (F g) (F.norm_le_bound g))
@[simp] lemma toL2_apply (F : Family G X) (g : G) : toL2 μ F g = l2 μ (F g) := rfl

@[simps] def l2Linear : Family G X →ₗ[ℝ] (G →ᵇ Lp ℂ 2 μ) where
  toFun := toL2 μ
  map_add' F H := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (l2 μ).map_add (F g) (H g)
  map_smul' c F := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (l2 μ).map_smul c (F g)

variable [AddCommGroup G] (M : Amenable.Mean G)
def avg : Family G X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun F := M.vector (toL2 μ F)
  map_add' F H := by rw [← l2Linear_apply, map_add]; exact M.vector_add _ _
  map_smul' c F := by rw [← l2Linear_apply, map_smul]; exact M.vector_smul _ _

omit [TopologicalSpace G] [DiscreteTopology G]
variable [AddAction G X] [MeasurableConstVAdd G X]
def orbit (φ : G →+ G) (f : Func X) : Family G X :=
  ⟨fun g => act (φ g) f, BoundedMeasurable.bound f,
    fun g x => BoundedMeasurable.norm_le_bound f (φ g +ᵥ x)⟩
@[simp] lemma orbit_apply (φ : G →+ G) (f : Func X) (g : G) : orbit φ f g = act (φ g) f := rfl

end Family
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def tensor (f : Func X) (g : Func Y) : Func (X×Y) :=
  comp f Prod.fst measurable_fst * comp g Prod.snd measurable_snd
@[simp] lemma tensor_apply (f : Func X) (g : Func Y) (z : X×Y) : tensor f g z = f z.1 * g z.2 := rfl

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
instance product_measurable_vadd : MeasurableConstVAdd G (X×X) where
  measurable_const_vadd g := (measurable_const_vadd (α := X) g).prodMap (measurable_const_vadd g)
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

def pairSequence (φ : G →+ G) (v w : Func X) : G →ᵇ Lp ℂ 2 (μ.map q) :=
  letI : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => l2 (μ.map q) (conditional μ q (v * act (φ g) w)))
    continuous_of_discreteTopology (bound v * bound w) (fun g => by
      apply l2_norm_le
      intro y
      apply expect_bound
      intro x
      dsimp only [mul_apply, act_apply]
      rw [norm_mul]
      exact mul_le_mul (norm_le_bound v x) (norm_le_bound w _) (norm_nonneg _) (bound v).coe_nonneg)

omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma pairSequence_apply (φ : G →+ G) (v w : Func X) (g : G) :
    pairSequence μ q hq φ v w g = l2 (μ.map q) (conditional μ q (v*act (φ g) w)) := rfl

end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Separability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {ι G X : Type*} [DecidableEq ι] [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

@[simp] lemma func_prod_apply (s : Finset ι) (f : ι → Func X) (x : X) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[simp] lemma conj_conj (f : Func X) : bmConj (bmConj f) = f := by ext x; simp

end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)

def PairVanishing (M : Amenable.Mean G) : Prop :=
  ∀ (φ : G →+ G), Function.Surjective φ → ∀ v w : Func X,
    l2 μ (project μ q hq w) = 0 →
    M.map (Amenable.Mean.normFn (pairSequence μ q hq φ v w)) = 0

variable {ι : Type*} [DecidableEq ι]
def Admissible (s : Finset ι) (φ : ι → G →+ G) : Prop :=
  (∀ i∈s, Function.Surjective (φ i)) ∧
  ∀ i∈s, ∀ j∈s, i≠j → Function.Surjective (φ i - φ j)

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable.Family
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (M : Amenable.Mean G)
def meanNorm (F : Family G X) : ℝ := M.map (Amenable.Mean.normFn (toL2 μ F))
end EuclideanFiveColor.BoundedMeasurable.Family

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
namespace Family
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
def conditional (F : Family G X) : Family G Y :=
  ⟨fun g => BoundedMeasurable.conditional μ q (F g), F.bound,
    fun g y => expect_bound _ _ (F.norm_le_bound g) y⟩
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma conditional_apply (F : Family G X) (g : G) :
    conditional μ q F g = BoundedMeasurable.conditional μ q (F g) := rfl
end Family
variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]

def covariance (φ : G →+ G) (v w : Func X) : Family G Y :=
  Family.conditional μ q (Family.const v * Family.orbit φ w) -
    Family.const (conditional μ q v) * Family.orbit φ (conditional μ q w)
omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma covariance_apply (φ : G →+ G) (v w : Func X) (g : G) :
    covariance μ q φ v w g = conditional μ q (v*act (φ g) w) -
      conditional μ q v * act (φ g) (conditional μ q w) := rfl

end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_AlgebraModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
inductive FiniteTensor : Func (X×Y) → Prop
  | tensor (f : Func X) (g : Func Y) : FiniteTensor (tensor f g)
  | add {f g : Func (X×Y)} : FiniteTensor f → FiniteTensor g → FiniteTensor (f+g)

variable [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]
open RectangleDensity

def codeCell (n : ℕ) (c : Code n) : Func X := by
  classical
  refine ⟨fun x => if code X n x = c then (1:ℂ) else 0, ?_, 1, ?_⟩
  · exact measurable_const.piecewise ((measurable_code n) (measurableSet_singleton c)) measurable_const
  · intro x; dsimp only; split_ifs <;> simp

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G : Type*} [AddCommGroup G]
def scaleHom (n : ℤ) : G →+ G := n • AddMonoidHom.id G
@[simp] lemma scaleHom_apply (n : ℤ) (g : G) : scaleHom n g = n • g := rfl
end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Functions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.CompactFunctions
open MeasureTheory
open scoped BigOperators
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

def At (μ : Measure X) (q : X → Y) (H : X → ℂ) (ε : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → X → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ x, ∑ i, ‖Hf i x‖ ≤ C) ∧
    ∀ k : K, ∃ a : Y → Fin r → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
      Integrable (fun x => dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2) μ ∧
      (∫ x, dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2

def Compact (μ : Measure X) (q : X → Y) (H : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → At (K := K) μ q H ε

lemma at_of_finite {μ : Measure X} {q : X → Y} {H : X → ℂ} {ε : ℝ}
    {I : Type*} [Fintype I] (B C : ℝ) (Hf : I → X → ℂ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : ∀ i, Measurable (Hf i))
    (hb : ∀ x, ∑ i, ‖Hf i x‖ ≤ C)
    (ha : ∀ k : K, ∃ a : Y → I → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
      Integrable (fun x => dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2) μ ∧
      (∫ x, dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2) :
    At (K := K) μ q H ε := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨_, B, C, fun i => Hf (e i), hB, hC, fun i => hm (e i), ?_, ?_⟩
  · intro x
    rw [e.sum_comp (fun i => ‖Hf i x‖)]
    exact hb x
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    have hs (x : X) : (∑ i, a (q x) (e i) * Hf (e i) x) = ∑ i, a (q x) i * Hf i x := e.sum_comp (fun i => a (q x) i * Hf i x)
    refine ⟨fun y i => a y (e i), Measurable.of_eval (fun i => (measurable_pi_iff.mp ham) (e i)), ?_, ?_, ?_⟩
    · intro y
      rw [pi_norm_le_iff_of_nonneg hB]
      exact fun i => (norm_le_pi_norm (a y) (e i)).trans (hab y)
    · simpa only [hs] using hai
    · simpa only [hs] using hae

lemma module_bound {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℂ)
    {B C : ℝ} (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) (hH : ∑ i, ‖H i‖ ≤ C) :
    ‖∑ i, a i * H i‖ ≤ B*C := by
  calc
    ‖∑ i, a i * H i‖ ≤ ∑ i, ‖a i * H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, B*‖H i‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm a i).trans ha) (norm_nonneg _)
    _ = B * ∑ i, ‖H i‖ := by rw [Finset.mul_sum]
    _ ≤ B*C := mul_le_mul_of_nonneg_left hH hB

lemma dist_sq_add (a b c d : ℂ) :
    dist (a+b) (c+d)^2 ≤ 2*(dist a c^2 + dist b d^2) := by
  have h := dist_add_add_le a b c d
  nlinarith [dist_nonneg (x := a+b) (y := c+d), dist_nonneg (x := a) (y := c),
    dist_nonneg (x := b) (y := d), sq_nonneg (dist a c - dist b d)]

lemma dist_sq_chain (a b c : ℂ) :
    dist a c^2 ≤ 2*(dist a b^2 + dist b c^2) := by
  have h := dist_triangle a b c
  nlinarith [dist_nonneg (x := a) (y := c), dist_nonneg (x := a) (y := b),
    dist_nonneg (x := b) (y := c), sq_nonneg (dist a b - dist b c)]

lemma compact_const (μ : Measure X) (q : X → Y) (c : ℂ) :
    Compact (K := K) μ q (fun _ => c) := by
  intro ε hε
  apply at_of_finite (I := Unit) 1 ‖c‖ (fun _ _ => c) (by norm_num) (norm_nonneg _) (fun _ => measurable_const)
  · intro x; simp
  · intro k
    refine ⟨fun _ _ => 1, measurable_const, fun _ => by simp, ?_, ?_⟩
    · simp
    · simpa using sq_pos_of_pos hε

lemma compact_add {μ : Measure X} {q : X → Y} {H G : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H) (hGm : Measurable G)
    (hH : Compact (K := K) μ q H) (hG : Compact (K := K) μ q G) :
    Compact (K := K) μ q (fun x => H x + G x) := by
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH (ε/2) (by positivity)
  obtain ⟨s, D, E, J, hD, hE, hjm, hjb, hd⟩ := hG (ε/2) (by positivity)
  classical
  apply at_of_finite (I := Fin r ⊕ Fin s) (max B D) (C+E) (Sum.elim F J)
    (hB.trans (le_max_left _ _)) (add_nonneg hC hE)
  · intro i; cases i with
    | inl i => exact hm i
    | inr i => exact hjm i
  · intro x
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using add_le_add (hb x) (hjb x)
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbb, hbi, hbe⟩ := hd k
    let A : Y → Fin r ⊕ Fin s → ℂ := fun y => Sum.elim (a y) (b y)
    have hAm : Measurable A := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (measurable_pi_iff.mp ham) i
      | inr i => exact (measurable_pi_iff.mp hbm) i
    have hAb (y : Y) : ‖A y‖ ≤ max B D := by
      rw [pi_norm_le_iff_of_nonneg (hB.trans (le_max_left _ _))]
      intro i
      cases i with
      | inl i => exact ((norm_le_pi_norm (a y) i).trans (hab y)).trans (le_max_left _ _)
      | inr i => exact ((norm_le_pi_norm (b y) i).trans (hbb y)).trans (le_max_right _ _)
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let G₀ : X → ℂ := fun x => ∑ i, b (q x) i * J i x
    have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
    have hGm₀ : Measurable G₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp hbm) i).comp hq).mul (hjm i))
    have hiM : Integrable (fun x => 2*(dist (H (k • x)) (F₀ x)^2 +
        dist (G (k • x)) (G₀ x)^2)) μ := (hai.add hbi).const_mul 2
    have hmajor (x : X) := dist_sq_add (H (k • x)) (G (k • x)) (F₀ x) (G₀ x)
    have hi : Integrable (fun x => dist (H (k • x)+G (k • x)) (F₀ x+G₀ x)^2) μ :=
      hiM.mono' ((((hHm.comp (measurable_const_smul k)).add (hGm.comp (measurable_const_smul k))).dist
        (hFm.add hGm₀)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have he : (∫ x, dist (H (k • x)+G (k • x)) (F₀ x+G₀ x)^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(dist (H (k • x)) (F₀ x)^2 + dist (G (k • x)) (G₀ x)^2) ∂μ :=
          integral_mono hi hiM hmajor
        _ = 2*((∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ) + ∫ x, dist (G (k • x)) (G₀ x)^2 ∂μ) := by
          rw [integral_const_mul, integral_add hai hbi]
        _ < ε^2 := by dsimp [F₀, G₀]; nlinarith
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] using hi
    · simpa only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] using he

lemma compact_mul {μ : Measure X} {q : X → Y} {H G : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H) (hGm : Measurable G)
    (RG : ℝ) (hRG : 0 ≤ RG) (hGb : ∀ x, ‖G x‖ ≤ RG)
    (hH : Compact (K := K) μ q H) (hG : Compact (K := K) μ q G) :
    Compact (K := K) μ q (fun x => H x * G x) := by
  intro ε hε
  let δ := ε/(2*(RG+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH δ hδ
  let γ := ε/(2*(B*C+1))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨s, D, E, J, hD, hE, hjm, hjb, hd⟩ := hG γ hγ
  classical
  apply at_of_finite (I := Fin r × Fin s) (B*D) (C*E) (fun i x => F i.1 x * J i.2 x)
    (mul_nonneg hB hD) (mul_nonneg hC hE) (fun i => (hm i.1).mul (hjm i.2))
  · intro x
    calc
      (∑ i : Fin r × Fin s, ‖F i.1 x * J i.2 x‖) = (∑ i, ‖F i x‖) * ∑ j, ‖J j x‖ := by
        simp only [Fintype.sum_prod_type, norm_mul, Finset.sum_mul_sum]
      _ ≤ C*E := mul_le_mul (hb x) (hjb x) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbb, hbi, hbe⟩ := hd k
    let A : Y → Fin r × Fin s → ℂ := fun y i => a y i.1 * b y i.2
    have hAm : Measurable A := Measurable.of_eval (fun i =>
      ((measurable_pi_iff.mp ham) i.1).mul ((measurable_pi_iff.mp hbm) i.2))
    have hAb (y : Y) : ‖A y‖ ≤ B*D := by
      rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB hD)]
      intro i
      change ‖a y i.1 * b y i.2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (a y) i.1).trans (hab y))
        ((norm_le_pi_norm (b y) i.2).trans (hbb y)) (norm_nonneg _) hB
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let G₀ : X → ℂ := fun x => ∑ i, b (q x) i * J i x
    have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
    have hGm₀ : Measurable G₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp hbm) i).comp hq).mul (hjm i))
    have hFbound (x : X) : ‖F₀ x‖ ≤ B*C := module_bound _ _ hB (hab _) (hb _)
    have hmajor (x : X) : dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2 ≤
        2*(RG^2*dist (H (k • x)) (F₀ x)^2 + (B*C)^2*dist (G (k • x)) (G₀ x)^2) := by
      have heq : H (k • x)*G (k • x)-F₀ x*G₀ x =
          (H (k • x)-F₀ x)*G (k • x)+F₀ x*(G (k • x)-G₀ x) := by ring
      have hn : dist (H (k • x)*G (k • x)) (F₀ x*G₀ x) ≤
          RG*dist (H (k • x)) (F₀ x) + (B*C)*dist (G (k • x)) (G₀ x) := by
        rw [dist_eq_norm, heq]
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, ← dist_eq_norm]
        exact add_le_add (by nlinarith [hGb (k • x), dist_nonneg (x := H (k • x)) (y := F₀ x)])
          (mul_le_mul_of_nonneg_right (hFbound x) dist_nonneg)
      have h₁ : 0 ≤ RG*dist (H (k • x)) (F₀ x) := mul_nonneg hRG dist_nonneg
      have h₂ : 0 ≤ (B*C)*dist (G (k • x)) (G₀ x) := mul_nonneg (mul_nonneg hB hC) dist_nonneg
      nlinarith [dist_nonneg (x := H (k • x)*G (k • x)) (y := F₀ x*G₀ x),
        sq_nonneg (RG*dist (H (k • x)) (F₀ x) - (B*C)*dist (G (k • x)) (G₀ x))]
    have hiM : Integrable (fun x => 2*(RG^2*dist (H (k • x)) (F₀ x)^2 +
        (B*C)^2*dist (G (k • x)) (G₀ x)^2)) μ :=
      ((hai.const_mul (RG^2)).add (hbi.const_mul ((B*C)^2))).const_mul 2
    have hi : Integrable (fun x => dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2) μ :=
      hiM.mono' ((((hHm.comp (measurable_const_smul k)).mul (hGm.comp (measurable_const_smul k))).dist
        (hFm.mul hGm₀)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have hδB : RG*δ < ε/2 := by
      dsimp [δ]
      have hh : 0 < 2*(RG+1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith
    have hγB : (B*C)*γ < ε/2 := by
      dsimp [γ]
      have hh : 0 < 2*(B*C+1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith
    have he : (∫ x, dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(RG^2*dist (H (k • x)) (F₀ x)^2 +
            (B*C)^2*dist (G (k • x)) (G₀ x)^2) ∂μ := integral_mono hi hiM hmajor
        _ = 2*(RG^2*(∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ) +
            (B*C)^2*∫ x, dist (G (k • x)) (G₀ x)^2 ∂μ) := by
          rw [integral_const_mul, integral_add (hai.const_mul _) (hbi.const_mul _),
            integral_const_mul, integral_const_mul]
        _ ≤ 2*((RG*δ)^2 + ((B*C)*γ)^2) := by
          have h₁ := mul_le_mul_of_nonneg_left hae.le (sq_nonneg RG)
          have h₂ := mul_le_mul_of_nonneg_left hbe.le (sq_nonneg (B*C))
          dsimp [F₀, G₀]
          nlinarith
        _ < ε^2 := by
          have h₁ := sq_lt_sq₀ (mul_nonneg hRG hδ.le) (by positivity : 0 ≤ ε/2) |>.mpr hδB
          have h₂ := sq_lt_sq₀ (mul_nonneg (mul_nonneg hB hC) hγ.le) (by positivity : 0 ≤ ε/2) |>.mpr hγB
          nlinarith
    have hs (x : X) : (∑ i : Fin r × Fin s, A (q x) i * (F i.1 x * J i.2 x)) = F₀ x*G₀ x := by
      simp only [Fintype.sum_prod_type, A, F₀, G₀, Finset.sum_mul_sum]
      congr 1
      funext i
      congr 1
      funext j
      ring
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [hs] using hi
    · simpa only [hs] using he

lemma compact_of_l2_approximation {μ : Measure X} {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (happ : ∀ δ : ℝ, 0 < δ → ∃ G : X → ℂ, Measurable G ∧ Compact (K := K) μ q G ∧
      Integrable (fun x => dist (H x) (G x)^2) μ ∧ (∫ x, dist (H x) (G x)^2 ∂μ) < δ^2) :
    Compact (K := K) μ q H := by
  intro ε hε
  obtain ⟨G, hGm, hG, hi₀, he₀⟩ := happ (ε/2) (by positivity)
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hG (ε/2) (by positivity)
  refine ⟨r, B, C, F, hB, hC, hm, hb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
  have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
    (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
  have hi₁ : Integrable (fun x => dist (H (k • x)) (G (k • x))^2) μ :=
    (hpres k).integrable_comp hi₀.aestronglyMeasurable |>.mpr hi₀
  have he₁ : (∫ x, dist (H (k • x)) (G (k • x))^2 ∂μ) < (ε/2)^2 := by
    have hm₀ : AEStronglyMeasurable (fun x => dist (H x) (G x)^2) (μ.map (fun x : X => k • x)) := by
      rw [(hpres k).map_eq]
      exact hi₀.aestronglyMeasurable
    rw [← integral_map (hpres k).measurable.aemeasurable hm₀, (hpres k).map_eq]
    exact he₀
  have hiM : Integrable (fun x => 2*(dist (H (k • x)) (G (k • x))^2 +
      dist (G (k • x)) (F₀ x)^2)) μ := (hi₁.add hai).const_mul 2
  have hmajor (x : X) := dist_sq_chain (H (k • x)) (G (k • x)) (F₀ x)
  have hi : Integrable (fun x => dist (H (k • x)) (F₀ x)^2) μ :=
    hiM.mono' (((hHm.comp (measurable_const_smul k)).dist hFm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
  refine ⟨a, ham, hab, hi, ?_⟩
  calc
    _ ≤ ∫ x, 2*(dist (H (k • x)) (G (k • x))^2 + dist (G (k • x)) (F₀ x)^2) ∂μ :=
      integral_mono hi hiM hmajor
    _ = 2*((∫ x, dist (H (k • x)) (G (k • x))^2 ∂μ) + ∫ x, dist (G (k • x)) (F₀ x)^2 ∂μ) := by
      rw [integral_const_mul, integral_add hi₁ hai]
    _ < ε^2 := by dsimp [F₀]; nlinarith

end EuclideanFiveColor.CompactFunctions

namespace EuclideanFiveColor.Quantize
open MeasureTheory
variable {A Y : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [MeasurableSpace Y]

lemma finite_measurable_choice {n : ℕ} (P : Y → Fin n → Prop)
    (hm : ∀ i, MeasurableSet {y | P y i}) (he : ∀ y, ∃ i, P y i) :
    ∃ f : Y → Fin n, Measurable f ∧ ∀ y, P y (f y) := by
  classical
  let Q : Y → ℕ → Prop := fun y k => ∃ i : Fin n, i.val = k ∧ P y i
  have hQ (y : Y) : ∃ k, Q y k := by
    obtain ⟨i, hi⟩ := he y
    exact ⟨i.val, i, rfl, hi⟩
  have hmQ (k : ℕ) : MeasurableSet {y | Q y k} := by
    have heq : {y | Q y k} = ⋃ i : Fin n, {y | i.val = k} ∩ {y | P y i} := by
      ext y
      simp only [Q, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    exact (MeasurableSet.const _).inter (hm i)
  let f₀ : Y → ℕ := fun y => Nat.find (hQ y)
  have hf₀ : Measurable f₀ := measurable_find hQ hmQ
  have hf₀B (y : Y) : f₀ y < n := by
    obtain ⟨i, hi, _⟩ := Nat.find_spec (hQ y)
    change Nat.find (hQ y) < n
    rw [← hi]
    exact i.isLt
  have hmF : Measurable (fun y => (⟨f₀ y, hf₀B y⟩ : Fin n)) := by
    apply measurable_to_countable'
    intro i
    convert hf₀ (measurableSet_singleton i.val) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
  refine ⟨fun y => ⟨f₀ y, hf₀B y⟩, hmF, ?_⟩
  intro y
  obtain ⟨i, hi, hp⟩ := Nat.find_spec (hQ y)
  have heq : i = ⟨f₀ y, hf₀B y⟩ := Fin.ext hi
  simpa only [heq] using hp

/-- A common finite net allows measurable nearest-bin selection for every
measurable map into the compact set. -/
lemma compact_quantization {s : Set A} (hs : IsCompact s) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (n : ℕ) (c : Fin n → A), (∀ i, c i ∈ s) ∧
      ∀ a : Y → A, Measurable a → (∀ y, a y ∈ s) →
        ∃ f : Y → Fin n, Measurable f ∧ ∀ y, dist (a y) (c (f y)) < ρ := by
  classical
  obtain ⟨u, hus, hu, hcover⟩ := hs.finite_cover_balls hρ
  let t := hu.toFinset
  let e : Fin t.card ≃ t := t.equivFin.symm
  let c : Fin t.card → A := fun i => (e i).val
  have hc (i : Fin t.card) : c i ∈ s := hus (by simpa only [t, hu.mem_toFinset] using (e i).property)
  refine ⟨t.card, c, hc, ?_⟩
  intro a ham has
  have he (y : Y) : ∃ i, dist (a y) (c i) < ρ := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover (has y))
    obtain ⟨hvu, hv⟩ := Set.mem_iUnion.mp hv
    have hvt : v ∈ t := by simpa only [t, hu.mem_toFinset] using hvu
    refine ⟨e.symm ⟨v, hvt⟩, ?_⟩
    simpa only [c, Equiv.apply_symm_apply, Metric.mem_ball] using hv
  exact finite_measurable_choice (fun y i => dist (a y) (c i) < ρ)
    (fun _ => measurableSet_lt (ham.dist measurable_const) measurable_const) he
end EuclideanFiveColor.Quantize

namespace EuclideanFiveColor.CompactFunctions

section
open MeasureTheory
open scoped BigOperators
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma combination_dist {r : ℕ} (F : Fin r → ℂ) (a b : Fin r → ℂ) :
    dist (∑ i, a i * F i) (∑ i, b i * F i) ≤ dist a b * ∑ i, ‖F i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖a i * F i - b i * F i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist a b * ‖F i‖ := Finset.sum_le_sum fun i _ => by
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using dist_le_pi_dist a b i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- Functional calculus for an individual compact function. Quantizing the
bounded coefficient arrays proves this directly, without a spectral theorem. -/
lemma compact_lipschitz {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H)
    (hH : Compact (K := K) μ q H) (f : ℂ → ℂ) (L : NNReal) (hLip : LipschitzWith L f) :
    Compact (K := K) μ q (fun x => f (H x)) := by
  intro ε hε
  let τ := ε/(4*((L : ℝ)+1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH τ hτ
  let η := τ/(C+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η*C ≤ τ := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < C+1)]
    nlinarith
  have hs : IsCompact {a : Fin r → ℂ | ‖a‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Fin r → ℂ) B
  obtain ⟨n, c, hc, hquant⟩ := Quantize.compact_quantization (Y := Y) hs hη
  let J : Fin n → X → ℂ := fun i x => f (∑ j, c i j * F j x)
  have hjm (i : Fin n) : Measurable (J i) := hLip.continuous.measurable.comp
    (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hm j)))
  let R := ‖f 0‖ + (L : ℝ)*(B*C)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hJb (i : Fin n) (x : X) : ‖J i x‖ ≤ R := by
    have hnorm : ‖∑ j, c i j * F j x‖ ≤ B*C := module_bound _ _ hB (hc i) (hb x)
    have hl := hLip.dist_le_mul (∑ j, c i j * F j x) 0
    rw [dist_zero_right] at hl
    have ht : ‖J i x‖ ≤ dist (J i x) (f 0) + ‖f 0‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (J i x - f 0) (f 0)
    dsimp [J, R] at *
    nlinarith [mul_le_mul_of_nonneg_left hnorm L.coe_nonneg]
  refine ⟨n, 1, n*R, J, by norm_num, mul_nonneg (Nat.cast_nonneg _) hR, hjm, ?_, ?_⟩
  · intro x
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ => hJb i x)
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbd⟩ := hquant a ham hab
    let A : Y → Fin n → ℂ := fun y i => if b y = i then 1 else 0
    have hAm : Measurable A := Measurable.of_eval (fun i =>
      measurable_const.piecewise (hbm (measurableSet_singleton i)) measurable_const)
    have hAb (y : Y) : ‖A y‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      dsimp [A]
      split_ifs <;> norm_num
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let F₁ : X → ℂ := fun x => ∑ i, c (b (q x)) i * F i x
    have hF₁ : Measurable F₁ := Finset.measurable_sum _ (fun i _ =>
      ((measurable_of_countable (fun j => c j i)).comp (hbm.comp hq)).mul (hm i))
    have hsel (x : X) : (∑ i, A (q x) i * J i x) = f (F₁ x) := by
      rw [Finset.sum_eq_single (b (q x))]
      · simp [A, J, F₁]
      · intro i _ hi
        simp [A, Ne.symm hi]
      · simp
    have hdist (x : X) : dist (F₀ x) (F₁ x) ≤ τ := by
      calc
        _ ≤ dist (a (q x)) (c (b (q x))) * ∑ i, ‖F i x‖ := combination_dist _ _ _
        _ ≤ η*C := mul_le_mul (hbd (q x)).le (hb x) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hη.le
        _ ≤ τ := hηC
    have hmajor (x : X) : dist (f (H (k • x))) (f (F₁ x))^2 ≤
        2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2 + τ^2) := by
      have ht := (dist_triangle (H (k • x)) (F₀ x) (F₁ x)).trans
        (add_le_add le_rfl (hdist x))
      have hl := (hLip.dist_le_mul (H (k • x)) (F₁ x)).trans
        (mul_le_mul_of_nonneg_left ht L.coe_nonneg)
      have hs₀ : dist (f (H (k • x))) (f (F₁ x))^2 ≤
          ((L : ℝ)*(dist (H (k • x)) (F₀ x)+τ))^2 :=
        pow_le_pow_left₀ dist_nonneg hl 2
      have hsq : (dist (H (k • x)) (F₀ x)+τ)^2 ≤ 2*(dist (H (k • x)) (F₀ x)^2+τ^2) := by
        nlinarith [sq_nonneg (dist (H (k • x)) (F₀ x)-τ)]
      have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (L : ℝ))
      nlinarith
    have hiM : Integrable (fun x => 2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2+τ^2)) μ :=
      (hai.add (integrable_const _)).const_mul _
    have hi : Integrable (fun x => dist (f (H (k • x))) (f (F₁ x))^2) μ :=
      hiM.mono' (((hLip.continuous.measurable.comp (hHm.comp (measurable_const_smul k))).dist
        (hLip.continuous.measurable.comp hF₁)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have hLτ : (L : ℝ)*τ < ε/4 := by
      dsimp [τ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 4*((L : ℝ)+1))]
      nlinarith
    have he : (∫ x, dist (f (H (k • x))) (f (F₁ x))^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2+τ^2) ∂μ := integral_mono hi hiM hmajor
        _ = 2*(L : ℝ)^2*((∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ)+τ^2) := by
          rw [integral_const_mul, integral_add hai (integrable_const _), integral_const,
            probReal_univ, smul_eq_mul, one_mul]
        _ ≤ 4*((L : ℝ)*τ)^2 := by
          have htt := mul_le_mul_of_nonneg_left hae.le (by positivity : 0 ≤ 2*(L : ℝ)^2)
          dsimp [F₀]
          nlinarith
        _ < ε^2 := by
          have hsq := (sq_lt_sq₀ (mul_nonneg L.coe_nonneg hτ.le) (by positivity : 0 ≤ ε/4)).mpr hLτ
          nlinarith [sq_pos_of_pos hε]
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [hsel] using hi
    · simpa only [hsel] using he
end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_of_bounded_pointwise_limit {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → Y} {H : X → ℂ} {Hn : ℕ → X → ℂ} [MeasurableConstSMul K X]
    (hq : Measurable q) (hHm : Measurable H) (hHnm : ∀ n, Measurable (Hn n))
    (hHnc : ∀ n, Compact (K := K) μ q (Hn n))
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (C : ℝ) (hC : 0 ≤ C) (hHb : ∀ x, ‖H x‖ ≤ C) (hHnb : ∀ n x, ‖Hn n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Hn n x) atTop (𝓝 (H x))) :
    Compact (K := K) μ q H := by
  have hdist (n : ℕ) (x : X) : dist (H x) (Hn n x)^2 ≤ (2*C)^2 :=
    (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num) hC)).mpr
      ((dist_le_norm_add_norm _ _).trans (by linarith [hHb x, hHnb n x]))
  have hi (n : ℕ) : Integrable (fun x => dist (H x) (Hn n x)^2) μ :=
    Integrable.of_bound ((hHm.dist (hHnm n)).pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n x)
  have hl : Tendsto (fun n => ∫ x, dist (H x) (Hn n x)^2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (f := fun _ : X => (0 : ℝ)) (fun _ : X => (2*C)^2)
      (fun n => (hi n).aestronglyMeasurable) (integrable_const _) (fun n =>
        Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n x)
      (hlim.mono fun x hx => by
        have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H x) atTop (𝓝 (H x))).dist hx).pow 2
        simpa only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht)
  apply compact_of_l2_approximation hq hHm hpres
  intro δ hδ
  obtain ⟨n, hn⟩ := (hl.eventually (gt_mem_nhds (sq_pos_of_pos hδ))).exists
  exact ⟨Hn n, hHnm n, hHnc n, hi n, hn⟩

lemma compact_neg {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X]
    (hq : Measurable q) (hm : Measurable H) (hc : Compact (K := K) μ q H) :
    Compact (K := K) μ q (fun x => -H x) := by
  have h := compact_lipschitz hq hm hc (fun z : ℂ => -z) 1 isometry_neg.lipschitz
  exact h

omit [MeasurableSpace X] in
lemma indicator_one_bound (s : Set X) (x : X) : ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ s <;> simp [hx]

lemma compact_compl {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} [MeasurableConstSMul K X]
    (hq : Measurable q) {s : Set X} (hm : MeasurableSet s)
    (hc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q (sᶜ.indicator (fun _ => (1 : ℂ))) := by
  have hn := compact_neg hq (measurable_const.indicator hm) hc
  have ha := compact_add hq measurable_const (measurable_const.indicator hm).neg
    (compact_const (K := K) μ q 1) hn
  have he : (fun x => (1 : ℂ) + -(s.indicator (fun _ => 1) x)) = sᶜ.indicator (fun _ => 1) := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  simpa only [Pi.neg_apply, he] using ha

lemma compact_union {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} [MeasurableConstSMul K X]
    (hq : Measurable q) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ))))
    (htc : Compact (K := K) μ q (t.indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q ((s ∪ t).indicator (fun _ => (1 : ℂ))) := by
  have hsm : Measurable (s.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hs
  have htm : Measurable (t.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator ht
  have ha := compact_add hq hsm htm hsc htc
  have hp := compact_mul hq hsm htm 1 (by norm_num) (indicator_one_bound t) hsc htc
  have hn := compact_neg hq (hsm.mul htm) hp
  have hh := compact_add hq (hsm.add htm) (hsm.mul htm).neg ha hn
  have he : (fun x => s.indicator (fun _ => (1 : ℂ)) x + t.indicator (fun _ => 1) x +
      -(s.indicator (fun _ => 1) x * t.indicator (fun _ => 1) x)) =
      (s ∪ t).indicator (fun _ => 1) := by
    funext x; by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]
  simpa only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply, he] using hh

lemma compact_iUnion {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (s : ℕ → Set X) (hm : ∀ n, MeasurableSet (s n))
    (hc : ∀ n, Compact (K := K) μ q ((s n).indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q ((⋃ n, s n).indicator (fun _ => (1 : ℂ))) := by
  let D : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, s i
  have hDm (n : ℕ) : MeasurableSet (D n) := MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hm i))
  have hDc (n : ℕ) : Compact (K := K) μ q ((D n).indicator (fun _ => (1 : ℂ))) := by
    induction n with
    | zero => simpa [D] using compact_const (K := K) μ q 0
    | succ n ih =>
      have he : D (n+1) = s n ∪ D n := by simp only [D, Finset.range_add_one, Finset.set_biUnion_insert]
      rw [he]
      exact compact_union hq (hm n) (hDm n) (hc n) ih
  apply compact_of_bounded_pointwise_limit hq (measurable_const.indicator (MeasurableSet.iUnion hm))
    (fun n => measurable_const.indicator (hDm n)) hDc hpres 1 (by norm_num)
    (indicator_one_bound _) (fun n => indicator_one_bound (D n))
  exact Filter.Eventually.of_forall fun x => by
    apply tendsto_const_nhds.congr'
    by_cases hx : x ∈ ⋃ n, s n
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (i+1)] with n hn
      have hix : x ∈ D n := Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simpa using hn, hi⟩⟩
      simp [hx, hix]
    · have hnx (n : ℕ) : x ∉ D n := by
        intro hh
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        obtain ⟨_, hi⟩ := Set.mem_iUnion.mp hi
        exact hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
      exact Filter.Eventually.of_forall fun n => by simp [hx, hnx n]

@[instance_reducible] def compactSigma (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y)
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) : MeasurableSpace X where
  MeasurableSet' s := MeasurableSet s ∧ Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ)))
  measurableSet_empty := ⟨MeasurableSet.empty, by simpa using compact_const (K := K) μ q 0⟩
  measurableSet_compl s hs := ⟨hs.1.compl, compact_compl hq hs.1 hs.2⟩
  measurableSet_iUnion s hs := ⟨MeasurableSet.iUnion (fun n => (hs n).1),
    compact_iUnion hq hpres s (fun n => (hs n).1) (fun n => (hs n).2)⟩

end

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

end EuclideanFiveColor.CompactFunctions

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Factors
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EuclideanFiveColor
open MeasureTheory
structure OrbitSpace (K : Type*) where
  val : K → ℂ

namespace OrbitSpace
variable {K : Type*}
def equiv (K : Type*) : OrbitSpace K ≃ (K → ℂ) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instInhabited : Inhabited (OrbitSpace K) := ⟨⟨fun _ => 0⟩⟩
instance instTopologicalSpace : TopologicalSpace (OrbitSpace K) := (equiv K).topologicalSpace
instance instMeasurableSpace : MeasurableSpace (OrbitSpace K) := borel _
instance instBorelSpace : BorelSpace (OrbitSpace K) := ⟨rfl⟩
instance instPolishSpaceOfCountable [Countable K] : PolishSpace (OrbitSpace K) := (equiv K).polishSpace_induced

@[ext] lemma ext {a b : OrbitSpace K} (h : ∀ k, a.val k = b.val k) : a = b := by
  cases a; cases b; congr; funext k; exact h k

instance instMulAction [Monoid K] : MulAction K (OrbitSpace K) where
  smul k f := ⟨fun l => f.val (l*k)⟩
  one_smul f := by ext l; exact congrArg f.val (mul_one l)
  mul_smul a b f := by ext l; exact congrArg f.val (mul_assoc l a b).symm

@[simp] lemma smul_val [Monoid K] (k : K) (f : OrbitSpace K) (l : K) :
    (k • f).val l = f.val (l*k) := rfl

end OrbitSpace

namespace OrbitFactor
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

def orbit (H : X → ℂ) (x : X) : OrbitSpace K := ⟨fun k => H (k • x)⟩

def extend (q : X → Y) (H : X → ℂ) (x : X) : Y × OrbitSpace K := (q x, orbit H x)

omit [MeasurableSpace X] in
@[simp] lemma orbit_one (H : X → ℂ) (x : X) : (orbit (K := K) H x).val 1 = H x := by
  simp only [orbit, one_smul]

end OrbitFactor
end EuclideanFiveColor

namespace EuclideanFiveColor.FactorCode
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MulAction K X] [MeasurableConstSMul K X]

def scalar (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y] (y : Y) : ℂ :=
  Real.arctan (embeddingReal Y y)

lemma scalar_measurable : Measurable (scalar Y) :=
  Complex.measurable_ofReal.comp (Real.continuous_arctan.measurable.comp (measurable_embeddingReal Y))

lemma scalar_injective : Function.Injective (scalar Y) := by
  intro x y h
  apply (measurableEmbedding_embeddingReal Y).injective
  apply Real.arctan_injective
  exact_mod_cast (show (Real.arctan (embeddingReal Y x) : ℂ) = Real.arctan (embeddingReal Y y) from h)

lemma scalar_embedding : MeasurableEmbedding (scalar Y) :=
  scalar_measurable.measurableEmbedding scalar_injective

def encode (p : X → Y) : X → OrbitSpace K := OrbitFactor.orbit (scalar Y ∘ p)

variable [Nonempty Y]
def decode : OrbitSpace K → Y := fun z => scalar_embedding.invFun (z.val 1)

end EuclideanFiveColor.FactorCode
namespace EuclideanFiveColor.FactorLp
open MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [Nonempty Y]

def space (μ : Measure X) (p : X → Y) : Submodule ℂ (Lp ℂ 2 μ) :=
  lpMeas ℂ ℂ (MeasurableSpace.comap p inferInstance) 2 μ

end EuclideanFiveColor.FactorLp
namespace EuclideanFiveColor.CountableApprox
open MeasureTheory
variable {Y : Type*} [MeasurableSpace Y]

def truncate (n : ℕ) (y : ℕ → Y) : Fin n → Y := fun i => y i

end EuclideanFiveColor.CountableApprox
namespace EuclideanFiveColor.ChainJoin
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

def joint (q : ℕ → X → Y) (x : X) : ℕ → Y := fun n => q n x

def code (q : ℕ → X → Y) : X → OrbitSpace K := FactorCode.encode (joint q)

end EuclideanFiveColor.ChainJoin
namespace EuclideanFiveColor.CodedMax
open MeasureTheory
variable {K X : Type*} [Group K] [Countable K] [MeasurableSpace X]
  [MulAction K X] [MeasurableConstSMul K X]

structure Model (μ : Measure X) (Good : (X → OrbitSpace K) → Prop) where
  map : X → OrbitSpace K
  measurable : Measurable map
  equivariant : ∀ k : K, ∀ᵐ x ∂μ, map (k • x) = k • map x
  good : Good map

instance instPreorderModel (μ : Measure X) (Good : (X → OrbitSpace K) → Prop) : Preorder (Model μ Good) where
  le a b := FactorLp.space μ a.map ≤ FactorLp.space μ b.map
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

end EuclideanFiveColor.CodedMax

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Stationary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory
open scoped BoundedContinuousFunction
open PlaneFiveColor.InvariantMean
namespace EuclideanFiveColor.StationaryMean
variable {A B X : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace X] [CompactSpace X]
  (t : A → X → X) (r : B → X → X) (x₀ : X)
def inner (f : C(X,ℝ)) (b : B) : A →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => f (r b (t a x₀)))
    continuous_of_discreteTopology ‖f‖ (fun _ => f.norm_coe_le_norm _)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_norm (f : C(X,ℝ)) (b : B) : ‖inner t r x₀ f b‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun _ => f.norm_coe_le_norm _
def outer (f : C(X,ℝ)) : B →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun b => mean (inner t r x₀ f b))
    continuous_of_discreteTopology ‖f‖ (fun b => (mean_norm_le _).trans (inner_norm t r x₀ f b))
def average (f : C(X,ℝ)) : ℝ := mean (outer t r x₀ f)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_add (f g : C(X,ℝ)) (b : B) : inner t r x₀ (f+g) b = inner t r x₀ f b + inner t r x₀ g b := by ext; rfl
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_smul (c : ℝ) (f : C(X,ℝ)) (b : B) : inner t r x₀ (c • f) b = c • inner t r x₀ f b := by ext; rfl
omit [AddCommGroup B] in
lemma outer_add (f g : C(X,ℝ)) : outer t r x₀ (f+g) = outer t r x₀ f + outer t r x₀ g := by
  ext b
  exact (congrArg mean (inner_add t r x₀ f g b)).trans (mean_add _ _)
omit [AddCommGroup B] in
lemma outer_smul (c : ℝ) (f : C(X,ℝ)) : outer t r x₀ (c • f) = c • outer t r x₀ f := by
  ext b
  exact (congrArg mean (inner_smul t r x₀ c f b)).trans (mean_smul _ _)
lemma average_add (f g : C(X,ℝ)) : average t r x₀ (f+g) = average t r x₀ f + average t r x₀ g := by
  simp only [average,outer_add,mean_add]
lemma average_smul (c : ℝ) (f : C(X,ℝ)) : average t r x₀ (c • f) = c * average t r x₀ f := by
  simp only [average,outer_smul,mean_smul]
lemma average_mono {f g : C(X,ℝ)} (h : f ≤ g) : average t r x₀ f ≤ average t r x₀ g := by
  have hp : 0 ≤ average t r x₀ (g-f) := mean_nonneg _ fun b => mean_nonneg _ fun a => sub_nonneg.mpr (h _)
  have he : average t r x₀ (g-f) = average t r x₀ g - average t r x₀ f := by
    rw [sub_eq_add_neg,average_add,← neg_one_smul ℝ f,average_smul]; ring
  linarith
lemma average_const (c : ℝ) : average t r x₀ (ContinuousMap.const X c) = c := by
  have hi (b : B) : inner t r x₀ (ContinuousMap.const X c) b = BoundedContinuousFunction.const A c := by ext; rfl
  have ho : outer t r x₀ (ContinuousMap.const X c) = BoundedContinuousFunction.const B c := by
    ext b
    change mean (inner t r x₀ _ b) = c
    rw [hi,mean_const]
  rw [average,ho,mean_const]
lemma average_translation (ht : ∀ a b x, t a (t b x) = t (a+b) x)
    (φ : B → A → A) (hc : ∀ a b x, t a (r b x) = r b (t (φ b a) x))
    (a : A) (f : C(X,ℝ)) (ha : Continuous (t a)) :
    average t r x₀ (f.comp ⟨t a,ha⟩) = average t r x₀ f := by
  unfold average
  congr 1
  ext b
  change mean (inner t r x₀ (f.comp _) b) = mean (inner t r x₀ f b)
  have he : inner t r x₀ (f.comp ⟨t a,ha⟩) b = shift (φ b a) (inner t r x₀ f b) := by
    ext z
    change f (t a (r b (t z x₀))) = f (r b (t (z+φ b a) x₀))
    rw [hc,ht,add_comm]
  rw [he,mean_shift]
lemma average_rotation (hr : ∀ a b x, r a (r b x) = r (a+b) x)
    (b : B) (f : C(X,ℝ)) (hb : Continuous (r b)) :
    average t r x₀ (f.comp ⟨r b,hb⟩) = average t r x₀ f := by
  unfold average
  have he : outer t r x₀ (f.comp ⟨r b,hb⟩) = shift b (outer t r x₀ f) := by
    ext c
    change mean (inner t r x₀ (f.comp _) c) = mean (inner t r x₀ f (c+b))
    congr 1
    ext z
    change f (r b (r c (t z x₀))) = f (r (c+b) (t z x₀))
    rw [hr,add_comm]
  rw [he,mean_shift]
variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := average t r x₀ f.toContinuousMap
  map_add' := fun f g => average_add t r x₀ f.toContinuousMap g.toContinuousMap
  map_smul' := fun c f => average_smul t r x₀ c f.toContinuousMap
  monotone' := fun _ _ h => average_mono t r x₀ h
def measure : Measure X := RealRMK.rieszMeasure (functional t r x₀)
instance instIsFiniteMeasureMeasure : IsFiniteMeasure (measure t r x₀) := by dsimp [measure]; infer_instance
instance instRegularMeasure : (measure t r x₀).Regular := by dsimp [measure]; infer_instance
lemma integral (f : C(X,ℝ)) : ∫ x, f x ∂measure t r x₀ = average t r x₀ f :=
  RealRMK.integral_rieszMeasure (functional t r x₀) (CompactlySupportedContinuousMap.continuousMapEquiv f)
end EuclideanFiveColor.StationaryMean
end

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Coloring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
instance anglePeriodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
abbrev Angles := AddCircle (2*Real.pi)
def angularMeasure : Measure Angles := AddCircle.haarAddCircle
def direction (t : Angles) : ℂ := AddCircle.toCircle t
instance instIsProbabilityMeasureAnglesAngularMeasure : IsProbabilityMeasure angularMeasure := inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 2*Real.pi)))
lemma direction_continuous : Continuous direction := continuous_subtype_val.comp AddCircle.continuous_toCircle
@[simp] lemma direction_norm (t : Angles) : ‖direction t‖ = 1 := Circle.norm_coe _
@[simp] lemma direction_real (t : ℝ) : direction (t : Angles) = (Circle.exp t : ℂ) := by
  simp [direction,AddCircle.toCircle_apply_mk,Real.pi_ne_zero]

end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleMaps
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
abbrev RealPlane := ℝ × ℝ
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
abbrev CircleParameter := RealPlane × ℝ
abbrev CircleJet := CircleParameter × ℝ
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
abbrev PlaneL2 := Lp ℝ 2 (volume : Measure ℂ)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
def DensityOne (A : Set ℂ) (x : ℂ) : Prop :=
  Tendsto (fun r : ℝ => volume (A ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
    (𝓝[>] 0) (𝓝 (1 : ENNReal))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Compactness
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
def weakHilbert (v : E) : WeakDual ℝ E := StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E v)
omit [TopologicalSpace.SeparableSpace E] in
@[simp] lemma weakHilbert_apply (v w : E) : weakHilbert v w = ⟪v,w⟫ := rfl
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
abbrev RealL2 := Lp ℝ 2 μ
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
def Typical (z : ℂ) : Prop := DensityOne {w | c w=c z} z
def TypicalSampling (y : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ ∀ᵐ t ∂angularMeasure, Typical c (y+(r : ℂ)*direction t)
def sampleFn (y : ℂ) (r : ℝ) (i : Fin k) (t : Angles) : ℝ :=
  if c (y+(r : ℂ)*direction t)=i then 1 else 0
lemma sampleFn_measurable (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    Measurable (sampleFn c y r i) := by
  exact measurable_one.piecewise (measurableSet_eq_fun
    (hc.comp (measurable_const.add (measurable_const.mul direction_continuous.measurable))) measurable_const) measurable_zero
lemma sampleFn_nonneg (y : ℂ) (r : ℝ) (i : Fin k) (t : Angles) : 0 ≤ sampleFn c y r i t := by
  simp only [sampleFn]; split_ifs <;> norm_num
lemma sampleFn_le_one (y : ℂ) (r : ℝ) (i : Fin k) (t : Angles) : sampleFn c y r i t ≤ 1 := by
  simp only [sampleFn]; split_ifs <;> norm_num
lemma sampleFn_memLp (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    MemLp (sampleFn c y r i) 2 angularMeasure := by
  apply MemLp.of_bound (sampleFn_measurable c hc y r i).aestronglyMeasurable 1
  exact Eventually.of_forall fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c y r i t)]; exact sampleFn_le_one c y r i t
def sample (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) : RealL2 angularMeasure :=
  (sampleFn_memLp c hc y r i).toLp _
lemma sample_ae (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    sample c hc y r i =ᵐ[angularMeasure] sampleFn c y r i := MemLp.coeFn_toLp _
lemma sample_norm_le (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    ‖sample c hc y r i‖ ≤ 1 := by
  have hh : ∀ᵐ t ∂angularMeasure, ‖sample c hc y r i t‖ ≤ 1 := by
    filter_upwards [sample_ae c hc y r i] with t ht
    rw [ht,Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c y r i t)]
    exact sampleFn_le_one c y r i t
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0 : ℝ) ≤ 1) hh
end EuclideanFiveColor
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor.WeakBall
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
abbrev Space := {v : WeakDual ℝ E // WeakDual.toStrongDual v ∈ Metric.closedBall 0 1}
def value (a : Space E) : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a.1)
def ofNorm (v : E) (hv : ‖v‖ ≤ 1) : Space E := ⟨weakHilbert v,by
  simpa only [weakHilbert,StrongDual.toStrongDual_toWeakDual,Metric.mem_closedBall,dist_zero_right,
    LinearIsometryEquiv.norm_map] using hv⟩
omit [TopologicalSpace.SeparableSpace E] in
@[simp] lemma value_ofNorm (v : E) (hv : ‖v‖ ≤ 1) : value E (ofNorm E v hv) = v := by
  simp only [value,ofNorm,weakHilbert,StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.symm_apply_apply]
end EuclideanFiveColor.WeakBall
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
abbrev TraceVector (k : ℕ) := Fin k → WeakBall.Space (RealL2 angularMeasure)
def traceValue {k : ℕ} (b : TraceVector k) (i : Fin k) : RealL2 angularMeasure :=
  WeakBall.value _ (b i)
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def sampleCode (y : ℂ) (r : ℝ) : TraceVector k :=
  fun i => WeakBall.ofNorm _ (sample c hc y r i) (sample_norm_le c hc y r i)
@[simp] lemma traceValue_sampleCode (y : ℂ) (r : ℝ) (i : Fin k) :
    traceValue (sampleCode c hc y r) i = sample c hc y r i := WeakBall.value_ofNorm _ _ _
def sampleSet : Set (ℂ × ℝ × TraceVector k) :=
  {p | TypicalSampling c p.1 p.2.1 ∧ p.2.2=sampleCode c hc p.1 p.2.1}
def IsTrace (x : ℂ) (b : TraceVector k) : Prop := (x,1,b) ∈ closure (sampleSet c hc)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Topology Filter Set
namespace EuclideanFiveColor
variable {X I : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
/-- A finite-measure essential union is generated by countably many members of the original family. -/
lemma exists_countable_essential_union (A : I → Set X) (hm : ∀ i, MeasurableSet (A i)) :
    ∃ J : Set I, J.Countable ∧ ∀ i, A i ≤ᵐ[μ] (⋃ j ∈ J, A j) := by
  let S : Set ENNReal := {m | ∃ J : Set I, J.Countable ∧ μ (⋃ j ∈ J, A j)=m}
  have hs : S.Nonempty := ⟨0,∅,Set.countable_empty,by simp⟩
  obtain ⟨f,_,ht,hf⟩ := exists_seq_tendsto_sSup hs (OrderTop.bddAbove S)
  choose J hJ he using hf
  let K : Set I := ⋃ n, J n
  have hK : K.Countable := Set.countable_iUnion hJ
  let D : Set X := ⋃ j ∈ K, A j
  have hD : MeasurableSet D := MeasurableSet.biUnion hK (fun j _ => hm j)
  have hS : μ D ∈ S := ⟨K,hK,rfl⟩
  have hmax : μ D = sSup S := le_antisymm (le_sSup hS) (le_of_tendsto ht (Eventually.of_forall (fun n => by
    rw [← he n]
    apply measure_mono
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨j,hj,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨j,Set.mem_iUnion.mpr ⟨n,hj⟩,hx⟩)))
  refine ⟨K,hK,fun i => ?_⟩
  have hun : μ (D ∪ A i) ≤ μ D := by
    rw [hmax]
    apply le_sSup
    refine ⟨insert i K,hK.insert i,?_⟩
    congr 1
    ext x
    simp only [Set.mem_iUnion,Set.mem_insert_iff,Set.mem_union,D]
    aesop
  have heq : μ (D ∪ A i) = μ D := le_antisymm hun (measure_mono Set.subset_union_left)
  have hzero : μ ((D ∪ A i) \ D)=0 := by
    rw [measure_sdiff Set.subset_union_left hD.nullMeasurableSet (measure_ne_top μ D),heq,tsub_self]
  have hz : μ (A i \ D)=0 := measure_mono_null (by intro x hx; exact ⟨Or.inr hx.1,hx.2⟩) hzero
  simpa only [ae_le_set] using hz
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Fourier
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
namespace Multiplier
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
def apply (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (show MemLp (fun x => f x*g x) 2 μ by simpa only [mul_comm] using MemLp.mul' (show MemLp f ⊤ μ from memLp_top_of_bound hf C hbound) (Lp.memLp g)).toLp (fun x => f x*g x)
lemma apply_ae (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : apply μ f hf hbound g =ᵐ[μ] fun x => f x*g x := MemLp.coeFn_toLp _
def linear (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := apply μ f hf hbound
  map_add' g h := by
    apply Lp.ext
    filter_upwards [apply_ae μ f hf hbound (g+h),apply_ae μ f hf hbound g,apply_ae μ f hf hbound h,
      Lp.coeFn_add g h,Lp.coeFn_add (apply μ f hf hbound g) (apply μ f hf hbound h)] with x ha hb hc hd he
    simp only [ha,he,Pi.add_apply,hb,hc,hd,mul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [apply_ae μ f hf hbound (c • g),apply_ae μ f hf hbound g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (apply μ f hf hbound g)] with x ha hb hc hd
    simp only [RingHom.id_apply,ha,hd,Pi.smul_apply,hb,hc,smul_eq_mul]
    ring
lemma apply_norm_le (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : ‖apply μ f hf hbound g‖ ≤ C*‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [apply_ae μ f hf hbound g,hbound] with x hx hf
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg _)
def clm (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (linear μ f hf hbound).mkContinuous C (apply_norm_le μ f hf hbound)
end Multiplier
abbrev ComplexPlaneL2 := Lp (α := ℂ) ℂ 2 volume
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter
namespace EuclideanFiveColor.ProbabilityL2
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
lemma norm_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  let a := ∫ x, ‖f x‖ ∂μ
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hvar : 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - a^2 := by
    have h : (0 : ℝ) ≤ ∫ x, (‖f x‖-a)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (‖f x‖-a))
    have he : (fun x => (‖f x‖-a)^2) = fun x => ‖f x‖^2 - (2*a)*‖f x‖ + a^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => ‖f x‖^2 - (2*a)*‖f x‖) (g := fun _ => a^2) (hf₂.sub (hf.norm.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub (f := fun x => ‖f x‖^2) (g := fun x => (2*a)*‖f x‖) hf₂ (hf.norm.const_mul (2*a)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    change 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - (2*a)*a + a^2 at h
    nlinarith
  have hn : ‖∫ x, f x ∂μ‖ ≤ a := norm_integral_le_integral_norm f
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]

variable (μ : Measure X) [SFinite μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
def average (F : X × Ω → ℂ) (x : X) : ℂ := ∫ ω, F (x,ω) ∂ν
lemma average_measurable {F : X × Ω → ℂ} (hF : StronglyMeasurable F) :
    StronglyMeasurable (average ν F) := hF.integral_prod_right'
lemma fiber_memLp {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun ω => F (x,ω)) 2 ν := by
  filter_upwards [hF2.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hx
lemma average_memLp {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) : MemLp (average ν F) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (average_measurable ν hF).aestronglyMeasurable).mpr
  apply hF2.integral_prod_left.mono' ((average_measurable ν hF).norm.pow 2).aestronglyMeasurable
  filter_upwards [fiber_memLp μ ν hF hF2,hF2.prod_right_ae] with x hx hx2
  simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq,average] using
    norm_integral_sq ν (fun ω => F (x,ω)) (hx.integrable (by norm_num)) hx2
end EuclideanFiveColor.ProbabilityL2
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Transitions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
def transitionSet (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) : Set ℂ :=
  {q | q ∈ Metric.ball x R ∧ ((c q=i ∧ c (q+h)=j) ∨ (c q=j ∧ c (q+h)=i))}
def transitionRatio (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) : ENNReal :=
  volume (transitionSet c i j x R h) / ENNReal.ofReal ‖h‖
def TransitionEdge (i j : Fin k) (x : ℂ) : Prop :=
  i ≠ j ∧ ∀ R : ℝ, 0<R → 0 < limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Palettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
abbrev Traces (x : ℂ) := {b : TraceVector k // IsTrace c hc x b}
def tracePositive (x : ℂ) (i : Fin k) (b : Traces c hc x) : Set Angles :=
  {t | 0 < traceValue b.1 i t}
lemma tracePositive_measurable (x : ℂ) (i : Fin k) (b : Traces c hc x) :
    MeasurableSet (tracePositive c hc x i b) :=
  measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
def paletteGenerators (x : ℂ) (i : Fin k) : Set (Traces c hc x) :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose
def paletteSet (x : ℂ) (i : Fin k) : Set Angles :=
  ⋃ b ∈ paletteGenerators c hc x i, tracePositive c hc x i b
def palette (x : ℂ) (t : Angles) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i => t ∈ paletteSet c hc x i)
@[simp] lemma mem_palette (x : ℂ) (t : Angles) (i : Fin k) :
    i ∈ palette c hc x t ↔ t ∈ paletteSet c hc x i := by simp [palette]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteDensity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
def FlatDensityZero (A : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Prop :=
  Tendsto (fun r : ℝ => volume.real (A ∩ Metric.closedBall p r)/r^2) (𝓝[>] 0) (𝓝 0)
def LineDensityZero (D : Set ℝ) (t : ℝ) : Prop :=
  Tendsto (fun r : ℝ => volume.real (D ∩ Metric.closedBall t r)/r) (𝓝[>] 0) (𝓝 0)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def liftPalette (x : ℂ) (i : Fin k) : Set ℝ :=
  ((↑) : ℝ → Angles) ⁻¹' paletteSet c hc x i
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryPalettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def BinaryCenter (x : ℂ) (i j : Fin k) : Prop :=
  ∀ᵐ t ∂angularMeasure, t ∈ paletteSet c hc x i ∨ t ∈ paletteSet c hc x j
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_States
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def fourEdge (e : Fin 4) : Finset (Fin 5) :=
  if e=0 then {0,1} else if e=1 then {1,2} else if e=2 then {2,3} else {3,0}
def FourAdmissible (p : Finset (Fin 5)) : Prop :=
  p.Nonempty ∧ p.card≤2 ∧ ∀ e : Fin 4, ¬p⊆fourEdge e
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def DensityZero (A : Set ℂ) (x : ℂ) : Prop :=
  Tendsto (fun r : ℝ => volume (A∩Metric.closedBall x r)/volume (Metric.closedBall x r))
    (𝓝[>] 0) (𝓝 (0:ENNReal))
variable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
def RealState (x : ℂ) (A : Set ℝ) (J : Finset (Fin k)) : Prop :=
  MeasurableSet A ∧ ∀ i∈J, A≤ᵐ[volume] liftPalette c hc x i
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def FourCenter (x : ℂ) : Prop :=
  TransitionEdge c 0 1 x ∧ TransitionEdge c 1 2 x ∧ TransitionEdge c 2 3 x ∧ TransitionEdge c 3 0 x
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_AngularBoundary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor
/-- `0` is the outsider and `1,2` the two diagonal states. -/
def FourWordValid (w : Fin 6 → Fin 3) : Prop :=
  (∀j,w j≠w (j+1)) ∧ (∀j,w j≠0 → w (j+3)≠0 → w (j+3)=w j)
def FourWordMixed (w : Fin 6 → Fin 3) : Prop :=
  ∃i j,w i=0 ∧ w j=0 ∧ i.val%2≠j.val%2
def FourWordCross (w u : Fin 6 → Fin 3) : Prop :=
  ∀j,w j≠0 → u (j+1)≠w j ∧ u (j-1)≠w j
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
/-- The source's strict min/max straddling region, in equivalent witness form. -/
def Straddle (K : Set ℂ) : Set ℂ := {z | ∃p∈K,∃q∈K,dist z p<1 ∧ 1<dist z q}
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
/-- The approach data furnished by the manuscript interface proposition, with no
assumption of angular strip conclusions. -/
structure ApproachingContinuum (x : ℂ) (K : Set ℂ) (v : ℂ) where
  center_mem : x∈K
  r : ℕ → ℝ
  w : ℕ → ℂ
  r_pos : ∀n,0 < r n
  r_tendsto : Tendsto r atTop (𝓝 0)
  w_unit : ∀n,‖w n‖=1
  w_tendsto : Tendsto w atTop (𝓝 v)
  point_mem : ∀n,x+(r n : ℂ)*w n∈K
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
/-- The manuscript's essential spatial color support. -/
def spatialSupport (i : Fin k) : Set ℂ := (volume.restrict {z | c z=i}).support
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Exclusion
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def fiveEdge (i : Fin 5) : Finset (Fin 5) := {i,i+1}
def FiveAdmissible (p : Finset (Fin 5)) : Prop :=
  p.Nonempty ∧ p.card≤2 ∧ ∀ i : Fin 5, ¬p⊆fiveEdge i
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
/-- Labels allowed on the side selected by `b`; a label survives precisely when
both of its incident edges have the opposite sign. -/
def sideAllowed (s : Fin 5 → Bool) (b : Bool) : Finset (Fin 5) :=
  Finset.univ.filter fun i => s (i-1)≠b ∧ s i≠b
/-- Both actual one-sided strip restrictions on a palette. -/
def SideCompatible (s : Fin 5 → Bool) (p : Finset (Fin 5)) : Prop :=
  p.card≤2 ∧ (p∩sideAllowed s true).Nonempty ∧ (p∩sideAllowed s false).Nonempty
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Accumulation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (e : Equiv.Perm (Fin k))
lemma transitionEdge_symm {i j : Fin k} {x : ℂ} (h : TransitionEdge c i j x) :
    TransitionEdge c j i x := by
  have he : transitionRatio c j i x=transitionRatio c i j x := by
    funext R z
    have hs : transitionSet c j i x R z=transitionSet c i j x R z := by
      ext q
      simp only [transitionSet,Set.mem_ofPred_eq,or_comm]
    change volume _ / _ = volume _ / _
    rw [hs]
  exact ⟨h.1.symm,by simpa only [he] using h.2⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def ThreeCenter (x : ℂ) : Prop :=
  TransitionEdge c 0 1 x ∧ TransitionEdge c 0 2 x ∧ TransitionEdge c 1 2 x
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def FiveCenter (x : ℂ) : Prop := ∀i : Fin 5,TransitionEdge c i (i+1) x
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FiveSupport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor.FiveComb
-- Independent finite arithmetic facts; the source labels are Z/5Z, represented by Fin 5.
def Adj (i j : Fin 5) : Prop := i+1=j ∨ j+1=i
instance instDecidableAdj (i j : Fin 5) : Decidable (Adj i j) := inferInstanceAs (Decidable (_∨_))
end EuclideanFiveColor.FiveComb
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CyclicCore
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def transitionGraph (x : ℂ) : SimpleGraph (Fin 5) where
  Adj i j := TransitionEdge c i j x
  symm := ⟨fun _ _ h => transitionEdge_symm c h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def CyclicCore : Set ℂ := {x | ¬(transitionGraph c x).IsAcyclic}
def StandardCore (e : Equiv.Perm (Fin 5)) : Set ℂ :=
  {x | ThreeCenter (e.symm ∘ c) x ∨ FourCenter (e.symm ∘ c) x ∨ FiveCenter (e.symm ∘ c) x}
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskAverages
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
def diskLaw (ε : ℝ) : Measure ℂ :=
  (volume (Metric.ball (0:ℂ) ε))⁻¹ • volume.restrict (Metric.ball 0 ε)
def colorFn {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : ℝ := if c z=i then 1 else 0
def diskAverage {k : ℕ} (c : ℂ → Fin k) (ε : ℝ) (i : Fin k) (q : ℂ) : ℝ :=
  ∫ v, colorFn c i (q+v) ∂diskLaw ε
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphRealization
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
/-- Standard affine vertices. These are the manuscript's probability-simplex coordinates. -/
def graphVertex {V : Type u} (i : V) : V → ℝ := fun j => if j=i then 1 else 0
/-- Affine parameterization of an edge, including its two vertices. -/
def graphEdgePoint {V : Type u} (i j : V) (t : ℝ) : V → ℝ :=
  (1-t) • graphVertex i + t • graphVertex j
/-- The geometric realization of a simple graph in its probability simplex.
The equal-endpoint option includes isolated vertices. -/
def graphRealization {V : Type u} (G : SimpleGraph V) : Set (V → ℝ) :=
  {p | ∃ i j, (i=j ∨ G.Adj i j) ∧ ∃ t ∈ Icc (0:ℝ) 1, p=graphEdgePoint i j t}
abbrev GraphSpace {V : Type u} (G : SimpleGraph V) := ↥(graphRealization G)
@[simp] lemma graphEdgePoint_zero {V : Type u} (i j : V) : graphEdgePoint i j 0=graphVertex i := by
  simp [graphEdgePoint]
@[simp] lemma graphEdgePoint_one {V : Type u} (i j : V) : graphEdgePoint i j 1=graphVertex j := by
  simp [graphEdgePoint]
@[simp] lemma graphEdgePoint_self {V : Type u} (i : V) (t : ℝ) : graphEdgePoint i i t=graphVertex i := by
  rw [graphEdgePoint,←add_smul]; simp
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology MeasureTheory
namespace EuclideanFiveColor
/-- The manuscript's thresholded and renormalized disk average (equation 22). -/
def thresholdWeight (c : ℂ → Fin 5) (ε α : ℝ) (q : ℂ) (i : Fin 5) : ℝ :=
  max (diskAverage c ε i q-α) 0
def thresholdTotal (c : ℂ → Fin 5) (ε α : ℝ) (q : ℂ) : ℝ :=
  ∑i,thresholdWeight c ε α q i
def thresholdMap (c : ℂ → Fin 5) (ε α : ℝ) (q : ℂ) (i : Fin 5) : ℝ :=
  thresholdWeight c ε α q i / thresholdTotal c ε α q
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Interfaces
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
/-- The four cyclic edges, with outsider label `4`. This definition is local to
this interface argument and agrees extensionally with `fourEdge`. -/
def interfaceFourEdge (i : Fin 4) : Finset (Fin 5) :=
  if i=0 then {0,1} else if i=1 then {1,2} else if i=2 then {2,3} else {3,0}
def interfaceFourAllowed (s : Fin 4 → Bool) (b : Bool) : Finset (Fin 5) :=
  Finset.univ.filter fun j => ∀i, s i=b → j∉interfaceFourEdge i
def InterfaceFourCompatible (s : Fin 4 → Bool) (p : Finset (Fin 5)) : Prop :=
  p.Nonempty ∧ p.card≤2 ∧
    (p∩interfaceFourAllowed s true).Nonempty ∧ (p∩interfaceFourAllowed s false).Nonempty
def InterfaceFourSplit (s : Fin 4 → Bool) : Prop := s 0≠s 2 ∧ s 1≠s 3
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_ContinuumLimits
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- One interface excludes both labels from the same straddling set and approaches
its center in an actual unit direction. -/
def CommonInterface (c : ℂ → Fin 5) (x : ℂ) (i j : Fin 5) : Prop :=
  ∃K : Set ℂ, ∃v : ℂ, ‖v‖=1 ∧ Nonempty (ApproachingContinuum x K v) ∧
    Disjoint (spatialSupport c i) (Straddle K) ∧ Disjoint (spatialSupport c j) (Straddle K)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskExtension
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
structure MarkedDisk where
  center : ℂ
  radius : ℝ
  core : Bool
namespace MarkedDisk
def ball (d : MarkedDisk) : Set ℂ := Metric.ball d.center d.radius
def closedBall (d : MarkedDisk) : Set ℂ := Metric.closedBall d.center d.radius
def noncoreCost (d : MarkedDisk) : ℝ := if d.core then 0 else d.radius
def Valid (L : Set ℂ) (d : MarkedDisk) : Prop :=
  0<d.radius ∧ (d.core=true → ∃x∈L,x∈d.ball)

end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
def diskHoles (S : Finset MarkedDisk) : Set ℂ := ⋃d∈S,d.ball
def coreHoles (S : Finset MarkedDisk) : Set ℂ := ⋃d∈S,⋃(_ : d.core=true),d.ball
lemma mem_coreHoles {S : Finset MarkedDisk} {z : ℂ} : z∈coreHoles S ↔ ∃d∈S,d.core=true ∧ z∈d.ball := by
  simp only [coreHoles,mem_iUnion]
  aesop

end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphCuts
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor

def graphCutRealization {V : Type u} (T : SimpleGraph V) : Set (V → ℝ) :=
  {p | p∈graphRealization (⊤ : SimpleGraph V) ∧ ∀ i j, i≠j → ¬T.Adj i j →
    p≠graphEdgePoint i j (1/2)}
abbrev GraphCutSpace {V : Type u} (T : SimpleGraph V) := ↥(graphCutRealization T)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- A compact connected fiber joins both designated boundary sets. -/
def FiberCrosses {X : Type u} {Y : Type v} [TopologicalSpace X]
    (f : X → Y) (A B : Set X) (b : Y) : Prop :=
  ∃K : Set X, IsCompact K ∧ IsConnected K ∧ K⊆f ⁻¹' {b} ∧
    (K∩A).Nonempty ∧ (K∩B).Nonempty
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_HoleApproximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma radius_le_sum {S : Finset MarkedDisk} (hS : ∀d∈S,0≤d.radius) {d : MarkedDisk} (hd : d∈S) :
    d.radius≤∑e∈S,e.radius := Finset.single_le_sum hS hd
lemma closedBall_near_core {L : Set ℂ} {d : MarkedDisk} (hd : d.Valid L) (hc : d.core=true) :
    ∃x∈L,d.closedBall⊆Metric.ball x (2*d.radius) := by
  obtain ⟨x,hx,hxd⟩ := hd.2 hc
  refine ⟨x,hx,fun z hz => ?_⟩
  have hx' : dist d.center x<d.radius := by simpa only [ball,Metric.mem_ball,dist_comm] using hxd
  exact lt_of_le_of_lt (dist_triangle z d.center x) (by dsimp [closedBall] at hz; change dist z d.center≤d.radius at hz; linarith)
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
def initialDisks (L C : Finset ℂ) (δ u : ℝ) : Finset MarkedDisk :=
  L.image (fun x => ⟨x,δ,true⟩) ∪ C.image (fun x => ⟨x,u,false⟩)
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
/-- Data actually constructed by the small-hole lemma. -/
structure HoleApprox (c : ℂ → Fin 5) (α : ℝ) (L : Finset ℂ) (t : ℝ) where
  ε : ℝ
  ε_pos : 0<ε
  ε_lt : ε<t
  disks : Finset MarkedDisk
  valid : ∀d∈disks,d.Valid (L : Set ℂ)
  disjoint : (disks : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall)
  sum_lt : (∑d∈disks,d.radius)<t
  map : C(↥(Metric.closedBall (0:ℂ) 7 \ coreHoles disks),GraphSpace (⊤ : SimpleGraph (Fin 5)))
  agrees : ∀z : ↥(Metric.closedBall (0:ℂ) 7 \ coreHoles disks),z.val∉diskHoles disks →
    (map z).val=thresholdMap c ε α z.val
namespace HoleApprox
lemma cores_near {c : ℂ → Fin 5} {α t : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) : coreHoles a.disks⊆⋃x∈L,Metric.ball x (2*t) := by
  intro z hz
  obtain ⟨d,hd,hcd,hzd⟩ := mem_coreHoles.mp hz
  obtain ⟨x,hx,hsub⟩ := MarkedDisk.closedBall_near_core (a.valid d hd) hcd
  have hrad := MarkedDisk.radius_le_sum (fun e he => (a.valid e he).1.le) hd
  exact mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,
    Metric.ball_subset_ball (by linarith [a.sum_lt]) (hsub (Metric.ball_subset_closedBall hzd))⟩⟩
end HoleApprox
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphPatches
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
def planeAnnulus (x : ℂ) (r R : ℝ) : Set ℂ := Metric.closedBall x R \ Metric.ball x r
lemma mem_planeAnnulus {x z : ℂ} {r R : ℝ} : z∈planeAnnulus x r R ↔ dist z x≤R ∧ r≤dist z x := by
  simp [planeAnnulus,not_lt]
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
def activeCenters (L : Finset ℂ) : Finset ℂ := L.filter (fun x => dist x 0≤6)
namespace HoleApprox
lemma annulus_in_domain {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (hR : R<1) (htR : 2*t<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) {x : ℂ} (hx : x∈activeCenters L) :
    planeAnnulus x (2*t) R⊆Metric.closedBall (0:ℂ) 7 \ coreHoles a.disks := by
  have hx' := Finset.mem_filter.mp hx
  intro z hz
  have hz' := mem_planeAnnulus.mp hz
  constructor
  · change dist z 0≤7
    exact (dist_triangle z x 0).trans (by linarith [hx'.2])
  · intro hh
    obtain ⟨y,hy⟩ := mem_iUnion.mp (a.cores_near hh)
    obtain ⟨hyL,hzy⟩ := mem_iUnion.mp hy
    change dist z y<2*t at hzy
    by_cases he : x=y
    · subst y; linarith [hz'.2]
    · have hh' := hsep x hx'.1 y hyL he
      have htri := dist_triangle x z y
      rw [dist_comm x z] at htri
      linarith [hz'.1]
end HoleApprox
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FullApproximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
namespace HoleApprox
def annulusMap {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (hR : R<1) (htR : 2*t<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) {x : ℂ} (hx : x∈activeCenters L) :
    C(planeAnnulus x (2*t) R,GraphSpace (⊤ : SimpleGraph (Fin 5))) :=
  ⟨fun z => a.map ⟨z.val,a.annulus_in_domain hR htR hsep hx z.property⟩,
    a.map.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
end HoleApprox
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
/-- A global graph approximation, with actual small exceptional disks.
All fields will be constructed, not postulated as coloring hypotheses. -/
structure FullApprox (c : ℂ → Fin 5) (α t : ℝ) where
  ε : ℝ
  ε_pos : 0<ε
  ε_lt : ε<t
  disks : Finset MarkedDisk
  positive : ∀d∈disks,0<d.radius
  disjoint : (disks : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall)
  sum_lt : (∑d∈disks,d.radius)<t
  map : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5)))
  agrees : ∀z : Metric.closedBall (0:ℂ) 5,z.val∉diskHoles disks →
    (map z).val=thresholdMap c ε α z.val
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Representations
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
/-- Discrete additive notation for the actual multiplicative algebraic rotation group. -/
def Rot := Additive K deriving AddCommGroup
def rotMul (g : Rot) : K := Additive.toMul g
def mulRot (k : K) : Rot := Additive.ofMul k
@[simp] lemma rotMul_mulRot (k : K) : rotMul (mulRot k) = k := rfl
@[simp] lemma mulRot_rotMul (g : Rot) : mulRot (rotMul g) = g := rfl
instance rotAction (X : Type*) [MulAction K X] : AddAction Rot X where
  vadd g x := rotMul g • x
  zero_vadd x := one_smul K x
  add_vadd g h x := mul_smul (rotMul g) (rotMul h) x
@[simp] lemma rot_vadd {X : Type*} [MulAction K X] (g : Rot) (x : X) :
    g +ᵥ x = rotMul g • x := rfl
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
namespace PlaneFiveColor.LabelModel
open Spectral
variable (k : ℕ)
def Proper (ω : E → Fin k) : Prop := ∀ x y : E, ‖(x:ℂ)-(y:ℂ)‖ = 1 → ω x ≠ ω y
abbrev Space := {ω : E → Fin k // Proper k ω}
def trans (a : E) (ω : Space k) : Space k := ⟨fun x => ω.val (x+a),by
  intro x y h
  apply ω.property (x+a) (y+a)
  change ‖(x:ℂ)+(a:ℂ)-((y:ℂ)+(a:ℂ))‖ = 1
  simpa only [add_sub_add_right_eq_sub] using h⟩
def rotate (b : K) (ω : Space k) : Space k := ⟨fun x => ω.val (kCoeff b * x),by
  intro x y h
  apply ω.property (kCoeff b*x) (kCoeff b*y)
  change ‖(b.val:ℂ)*(x:ℂ)-(b.val:ℂ)*(y:ℂ)‖ = 1
  rw [← mul_sub,norm_mul,Circle.norm_coe,one_mul,h]⟩
@[simp] lemma trans_apply (a : E) (ω : Space k) (x : E) : (trans k a ω).val x = ω.val (x+a) := rfl
@[simp] lemma rotate_apply (b : K) (ω : Space k) (x : E) : (rotate k b ω).val x = ω.val (kCoeff b*x) := rfl
@[simp] lemma trans_zero (ω : Space k) : trans k 0 ω = ω := by apply Subtype.ext; funext x; simp
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.Koopman
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
def isometry (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ s hs
  invFun := Lp.compMeasurePreserving s.symm (hs.symm s)
  left_inv v := by
    change Lp.compMeasurePreserving s.symm (hs.symm s) (Lp.compMeasurePreserving s hs v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s : X → X) ∘ s.symm = id := funext s.apply_symm_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
  right_inv v := by
    change Lp.compMeasurePreserving s hs (Lp.compMeasurePreserving s.symm (hs.symm s) v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s.symm : X → X) ∘ s = id := funext s.symm_apply_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
def unitary (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm (isometry μ s hs)
end EuclideanFiveColor.Koopman
end

noncomputable section
open Filter Topology
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
def op (a : A) : H →L[ℂ] H := U (Multiplicative.ofAdd a)
@[simp] lemma op_zero (v : H) : op U 0 v = v := by simp [op]
lemma norm_op (a : A) (v : H) : ‖op U a v‖ = ‖v‖ := Unitary.norm_map _ _
lemma dist_op (a : A) (v w : H) : dist (op U a v) (op U a w) = dist v w := by
  simp only [dist_eq_norm,← map_sub,norm_op]
variable [TopologicalSpace A]
def space : Submodule ℂ H where
  carrier := {v | Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Tendsto (fun a => op U a (v+w)) (𝓝 0) (𝓝 (v+w))
    simpa only [map_add] using hv.add hw
  smul_mem' := by
    intro c v hv
    change Tendsto (fun a => op U a (c • v)) (𝓝 0) (𝓝 (c • v))
    simpa only [map_smul] using hv.const_smul c
lemma isClosed_space : IsClosed (space U : Set H) := by
  apply isClosed_of_closure_subset
  intro v hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hv (ε/4) (by positivity)
  have ht := Metric.tendsto_nhds.mp hw (ε/2) (by positivity)
  filter_upwards [ht] with a ha
  have he : dist (op U a v) v ≤ 2 * dist v w + dist (op U a w) w := by
    calc
      _ ≤ dist (op U a v) (op U a w) + dist (op U a w) v := dist_triangle _ _ _
      _ ≤ dist (op U a v) (op U a w) + (dist (op U a w) w + dist w v) :=
        by linarith [dist_triangle (op U a w) w v]
      _ = _ := by rw [dist_op,dist_comm w v]; ring
  linarith
instance instCompleteSpaceSubtypeMemSubmoduleComplexSpace : CompleteSpace (space U) := (isClosed_space U).completeSpace_coe
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace EuclideanFiveColor.ContinuousVectors
variable {A X : Type*} [AddCommGroup A] [TopologicalSpace A] [MeasurableSpace X]
  (μ : Measure X) (U : Multiplicative A →* unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
  (s : A → X → X) (hs : ∀ a, MeasurePreserving (s a) μ μ)
  (hU : ∀ a v, op U a v = Lp.compMeasurePreserving (s a) (hs a) v)
include hU
omit hU
def clamp (z : ℂ) : ℂ := (max 0 (min 1 z.re) : ℝ)
@[simp] lemma clamp_zero : clamp 0 = 0 := by simp [clamp]
end EuclideanFiveColor.ContinuousVectors
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Energy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BoundedContinuousFunction
open Filter Topology
namespace EuclideanFiveColor.MovingMean

section
open PlaneFiveColor.InvariantMean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (b : Finset G × ℕ → G)
def approxAt (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ℝ := cube i.1.toList i.2 f (b i)
lemma approx_norm_le (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ‖approxAt b i f‖ ≤ ‖f‖ :=
  ((cube i.1.toList i.2 f).norm_coe_le_norm (b i)).trans (cube_norm_le _ _ _)

lemma approx_has_limit (f : G →ᵇ ℝ) :
    ∃ r : ℝ, Tendsto (fun i => approxAt b i f) (averagingUF G : Filter _) (𝓝 r) := by
  have hb : (Ultrafilter.map (fun i => approxAt b i f) (averagingUF G) : Filter ℝ) ≤
      𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro i
    exact abs_le.mp (approx_norm_le b i f)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (fun i => approxAt b i f) (averagingUF G)) hb
  exact ⟨r, hr⟩

/-- The invariant meanAt b, as the limit of the multiplicity-preserving averages. -/
def meanAt (f : G →ᵇ ℝ) : ℝ :=
  (averagingUF G : Filter _).limUnder (fun i => approxAt b i f)

lemma tendsto_approx (f : G →ᵇ ℝ) :
    Tendsto (fun i => approxAt b i f) (averagingUF G : Filter _) (𝓝 (meanAt b f)) :=
  tendsto_nhds_limUnder (approx_has_limit b f)

lemma mean_add (f h : G →ᵇ ℝ) : meanAt b (f+h) = meanAt b f + meanAt b h := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx b f).add (tendsto_approx b h) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [approxAt, cube_add, BoundedContinuousFunction.add_apply]

lemma mean_smul (c : ℝ) (f : G →ᵇ ℝ) : meanAt b (c • f) = c * meanAt b f := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx b f).const_mul c using 1
  all_goals try with_reducible_and_instances rfl
  simp only [approxAt, cube_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]

lemma mean_const (c : ℝ) : meanAt b (BoundedContinuousFunction.const G c) = c := by
  apply Tendsto.limUnder_eq
  convert (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
    (averagingUF G : Filter _) (𝓝 c)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [approxAt, cube_const, BoundedContinuousFunction.const_apply]

lemma mean_nonneg (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ meanAt b f := by
  exact ge_of_tendsto (tendsto_approx b f) (Filter.Eventually.of_forall fun i =>
    cube_nonneg i.1.toList i.2 f hf (b i))

lemma mean_norm_le (f : G →ᵇ ℝ) : ‖meanAt b f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_approx b f).norm
    (Filter.Eventually.of_forall fun i => approx_norm_le b i f)

lemma mean_shift (g : G) (f : G →ᵇ ℝ) : meanAt b (shift g f) = meanAt b f := by
  have hz : Tendsto (fun i : Finset G × ℕ => approxAt b i (shift g f) - approxAt b i f)
      (averagingUF G : Filter _) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_boundary f)
    filter_upwards [eventually_mem g] with i hi
    have h := ((cube i.1.toList i.2 (shift g f-f)).norm_coe_le_norm (b i)).trans
      (cube_coboundary_norm i.1.toList g (Finset.mem_toList.mpr hi) i.2 f)
    simpa only [cube_sub, BoundedContinuousFunction.sub_apply, approxAt] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique ((tendsto_approx b _).sub (tendsto_approx b _)) hz)

/-- A normalized positive shift-invariant continuous real linear functional. -/
def meanCLM : (G →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := meanAt b, map_add' := mean_add b, map_smul' := mean_smul b }
    1 (by intro f; change ‖meanAt b f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using mean_norm_le b f)

@[simp] lemma meanCLM_apply (f : G →ᵇ ℝ) : meanCLM b f = meanAt b f := rfl

def toMean : Amenable.Mean G where
  map := meanCLM b
  map_const := mean_const b
  positive := mean_nonneg b
  invariant g f := mean_shift b g f
end

open PlaneFiveColor.InvariantMean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
local instance instDecidableEq_solutions : DecidableEq G := Classical.decEq _
def cubeSupport : List G → ℕ → Finset G
  | [], _ => {0}
  | g::L, n => (Finset.range (n+1)).biUnion (fun k => (cubeSupport L n).image (fun h => k • g+h))
end EuclideanFiveColor.MovingMean
end

section
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]
namespace Family
def energy (F : Family G X) : G →ᵇ ℝ := Amenable.Mean.squareNorm (toL2 μ F)
omit [AddCommGroup G] in
@[simp] lemma energy_apply (F : Family G X) (g : G) : energy μ F g = ‖l2 μ (F g)‖^2 :=
  Amenable.Mean.squareNorm_apply _ _
end Family

def normSquare (f : Func X) : Func X := f * bmConj f
@[simp] lemma normSquare_apply (f : Func X) (x : X) : normSquare f x = (‖f x‖^2 : ℝ) := by
  change f x * star (f x) = _
  rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
end

end EuclideanFiveColor.BoundedMeasurable
end

open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

/-- The exact evaluation character, as a bounded measurable function. -/
def char (z : E) : Func D := ⟨fun d => (eval z d : ℂ), measurable_eval_coe z,
  1, fun d => by simp only [Circle.norm_coe, NNReal.coe_one, le_refl]⟩
@[simp] lemma char_apply (z : E) (d : D) : char z d = (eval z d : ℂ) := rfl
@[simp] lemma norm_char (z : E) (d : D) : ‖char z d‖ = 1 := Circle.norm_coe _
@[simp] lemma char_zero : char 0 = 1 := by ext d; simp
end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_NumberFields
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Coefficientwise transport by a rational linear functional. -/
def polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) : ℚ[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange ℓ (map_zero ℓ)))
@[simp] lemma coeff_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (n : ℕ) :
    (polyLinear ℓ p).coeff n = ℓ (p.coeff n) := rfl

end EuclideanFiveColor.AlgebraicCayley

end

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley
variable (N : IntermediateField ℚ ℂ)
def realSlice : Subfield ℝ := N.toSubfield.comap Complex.ofRealHom
def asN : realSlice N →+* N where
  toFun a := ⟨(a : ℝ),a.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp
@[simp] lemma coe_asN (a : realSlice N) : ((asN N a : N) : ℂ) = (a : ℝ) := rfl
variable (hi : Complex.I ∈ N)
def iN : N := ⟨Complex.I, hi⟩
@[simp] lemma coe_iN : ((iN N hi : N) : ℂ) = Complex.I := rfl

def realCayley (a : realSlice N) : N :=
  (1+iN N hi*asN N a)/(1-iN N hi*asN N a)

variable [FiniteDimensional ℚ N]

def realLine (a b : realSlice N) (t : ℚ) : realSlice N :=
  a+algebraMap ℚ (realSlice N) t*(b-a)
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_zero (a b : realSlice N) : realLine N a b 0 = a := by simp [realLine]
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_one (a b : realSlice N) : realLine N a b 1 = b := by simp [realLine]
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

def General (s : Finset V) : Prop :=
  ∀ t ⊆ s, t.card ≤ finrank ℚ V → LinearIndepOn ℚ id (t : Set V)

end EuclideanFiveColor.GeneralPosition
end

noncomputable section
open Module
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley

def generatingSet (s : Finset ℂ) : Finset ℂ :=
  {Complex.I} ∪ s.image (fun z => (z.re : ℂ)) ∪ s.image (fun z => (z.im : ℂ))
def generatedField (s : Finset ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (generatingSet s : Set ℂ)
end EuclideanFiveColor.AlgebraicCayley
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Selections
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a * m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)

def Good (n : ℕ) (x : α) : Prop := c^n ≤ m x
end EuclideanFiveColor.CappedResidues
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

def signedList (a : ℤ) (x : α) : List α :=
  match a with
  | .ofNat n => List.replicate n x
  | .negSucc n => List.replicate (n+1) (-x)
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_length (a : ℤ) (x : α) : (signedList a x).length = a.natAbs := by
  cases a <;> simp [signedList]
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_sum (a : ℤ) (x : α) : (signedList a x).sum = a • x := by
  cases a <;> simp [signedList]
  ring
end EuclideanFiveColor.CappedResidues
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SpectralMeasure
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
def mulLp (f : Func X) (g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (show MemLp (fun point => f point * g point) 2 μ by simpa only [mul_comm] using MemLp.mul' (show MemLp (f : X → ℂ) ∞ μ from memLp μ f ∞) (Lp.memLp g)).toLp (fun point => f point * g point)
lemma mulLp_ae (f : Func X) (g : Lp ℂ 2 μ) :
    mulLp μ f g =ᵐ[μ] fun x => f x * g x := MemLp.coeFn_toLp _
def mulLpLinear (f : Func X) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLp μ f
  map_add' g h := by
    apply Lp.ext
    filter_upwards [mulLp_ae μ f (g+h),mulLp_ae μ f g,mulLp_ae μ f h,
      Lp.coeFn_add g h,Lp.coeFn_add (mulLp μ f g) (mulLp μ f h)] with x ha hb hc hd he
    simp only [ha,he,Pi.add_apply,hb,hc,hd]
    exact mul_add _ _ _
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [mulLp_ae μ f (c • g),mulLp_ae μ f g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (mulLp μ f g)] with x ha hb hc hd
    simp only [RingHom.id_apply,ha,hd,Pi.smul_apply,hb,hc,smul_eq_mul]
    ring
lemma mulLp_norm_le (f : Func X) (g : Lp ℂ 2 μ) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖mulLp μ f g‖ ≤ C * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulLp_ae μ f g] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)
def mulLpCLM (f : Func X) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulLpLinear μ f).mkContinuous (bound f) (fun g => mulLp_norm_le μ f g (norm_le_bound f))
end EuclideanFiveColor.BoundedMeasurable
end

noncomputable section
open scoped ComplexConjugate IsMulCommutative
namespace EuclideanFiveColor.CommutingSpectral
variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* unitary (H →L[ℂ] H))
abbrev algebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))).topologicalClosure
instance algebra_closed : IsClosed (algebra U : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _
lemma adjoin_comm : IsMulCommutative (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))) := by
  apply StarAlgebra.isMulCommutative_adjoin
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩
    change ((U left * U right : unitary _) : H →L[ℂ] H) = ((U right * U left : unitary _) : H →L[ℂ] H)
    rw [← map_mul,← map_mul,mul_comm]
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩
    change ((U left * (U right)⁻¹ : unitary _) : H →L[ℂ] H) = (((U right)⁻¹ * U left : unitary _) : H →L[ℂ] H)
    rw [← map_inv,← map_mul,← map_mul,mul_comm]
open scoped IsMulCommutative in
instance algebra_commRing : CommRing (algebra U) :=
  StarSubalgebra.commRingTopologicalClosure _ (fun x y => by
    have := adjoin_comm U
    exact mul_comm x y)
instance algebra_commCStar : CommCStarAlgebra (algebra U) where

def generator (g : G) : algebra U :=
  ⟨U g,StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g))⟩
@[simp] lemma generator_one : generator U 1 = 1 := by ext; simp [generator]
@[simp] lemma generator_mul (g h : G) : generator U (g*h) = generator U g * generator U h := by
  apply Subtype.ext; change (U (g*h) : H →L[ℂ] H) = (U g : H →L[ℂ] H) * U h
  rw [map_mul]; rfl
lemma generator_unitary (g : G) : generator U g ∈ unitary (algebra U) := by
  constructor <;> apply Subtype.ext
  · exact (U g).property.1
  · exact (U g).property.2
variable [TopologicalSpace G] [DiscreteTopology G]
abbrev Spectrum := WeakDual.characterSpace ℂ (algebra U)
def character (φ : Spectrum U) : PontryaginDual G where
  toFun g := ⟨gelfandStarTransform (algebra U) (generator U g) φ, by
    change gelfandStarTransform (algebra U) (generator U g) φ ∈ Metric.sphere (0:ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    apply CStarRing.norm_of_mem_unitary
    exact Unitary.map_mem ((ContinuousMap.evalStarAlgHom ℂ ℂ φ).comp
      (gelfandStarTransform (algebra U)).toStarAlgHom) (generator_unitary U g)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change _ = (gelfandStarTransform (algebra U) (generator U g) φ) *
      (gelfandStarTransform (algebra U) (generator U h) φ)
    simp
  continuous_toFun := continuous_of_discreteTopology
lemma character_continuous : Continuous (character U) := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi; intro g
  exact Continuous.subtype_mk (map_continuous (gelfandStarTransform (algebra U) (generator U g))) _
def calculus : C(PontryaginDual G,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (algebra U).subtype.comp <| (gelfandStarTransform (algebra U)).symm.toStarAlgHom.comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨character U,character_continuous U⟩)
def evaluation (g : G) : C(PontryaginDual G,ℂ) :=
  ⟨fun d => (d g : ℂ),continuous_subtype_val.comp ((continuous_apply g).comp ContinuousMonoidHom.isClosedEmbedding_coe.continuous)⟩
end EuclideanFiveColor.CommutingSpectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
open BoundedMeasurable
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
def boundedCM (f : C(X,ℂ)) : Func X :=
  ⟨f,f.continuous.measurable,‖f‖₊,fun x => ContinuousMap.norm_coe_le_norm f x⟩
omit [T2Space X] in
@[simp] lemma boundedCM_apply (f : C(X,ℂ)) (x : X) : boundedCM f x = f x := rfl
end EuclideanFiveColor.VectorMeasure
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma evaluation_one : evaluation (1:G) = 1 := by
  ext d
  change (d 1 : ℂ) = 1
  rw [map_one]; rfl
lemma evaluation_mul (g h : G) : evaluation (g*h) = evaluation g * evaluation h := by
  ext d
  change (d (g*h) : ℂ) = (d g : ℂ)*(d h : ℂ)
  rw [map_mul]; rfl
@[simps] def evaluationHom : G →* C(PontryaginDual G,ℂ) where
  toFun := evaluation
  map_one' := evaluation_one
  map_mul' := evaluation_mul
end EuclideanFiveColor.CommutingSpectral
namespace EuclideanFiveColor.CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrableCM (f : C(X,ℂ)) : Integrable (f : X → ℂ) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def linear : C(X,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (integrableCM μ f) (integrableCM μ g)
  map_smul' c f := integral_smul c f
lemma norm_le (f : C(X,ℂ)) : ‖linear μ f‖ ≤ μ.real Set.univ * ‖f‖ := by
  simpa only [linear,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (ContinuousMap.norm_coe_le_norm f))
def clm : C(X,ℂ) →L[ℂ] ℂ := (linear μ).mkContinuous (μ.real Set.univ) (norm_le μ)
end EuclideanFiveColor.CompactIntegral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Ergodicity
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor
structure ConvexAverage (G : Type*) where
  n : ℕ
  pt : Fin n → G
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1
namespace ConvexAverage
variable {G H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
def apply (A : ConvexAverage G) (f : G → H) : H := ∑ i, A.weight i • f (A.pt i)
end ConvexAverage
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor
namespace ConvexAverage
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
def bm (A : ConvexAverage G) (f : Func X) : Func X := ∑ i, A.weight i • act (A.pt i) f
end ConvexAverage
namespace InvariantSequence
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
def limit (f : Func X) : Lp ℂ 2 μ := M.vector (Amenable.Mean.orbit (Amenable.Koopman.action μ) (l2 μ f))
end InvariantSequence
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor
open BoundedMeasurable
namespace ErgodicCriterion
variable (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
def testSet (s : Finset ℕ) : Set X := ⋂ n ∈ s, MeasurableSpace.natGeneratingSequence X n
lemma measurable_testSet (s : Finset ℕ) : MeasurableSet (testSet X s) :=
  Finset.measurableSet_biInter s (fun n _ => MeasurableSpace.measurableSet_natGeneratingSequence n)
def test (s : Finset ℕ) : Func X :=
  ⟨(testSet X s).indicator (fun _ => 1),(measurable_const.indicator (measurable_testSet X s)),1,
    fun x => by by_cases hx : x ∈ testSet X s <;> simp [hx]⟩
end ErgodicCriterion
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor.InvariantDecomposition
open BoundedMeasurable ErgodicCriterion
variable {G X : Type*} [AddCommGroup G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
def code (x : X) : Finset ℕ → ℂ := fun i => InvariantSequence.limit μ M (test X i) x
end EuclideanFiveColor.InvariantDecomposition
end

end OAI
end


