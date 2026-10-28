-- Prove2me | Definitions.Def_OAIQ4Nl000
-- name    : OAIQ4Nl000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:09:15.167809+00:00
-- url     : https://prove2.me/theorems/5eac6755-6411-4ca3-8011-a4552bd47631
-- title:
--   Definitions bundle OAIQ4Nl000 of the split of OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 257 declarations of OpenAI's Lean: 208 definitions, 11 inductive types or structures, 6 instances and 32 theorems. The definitions and types are `OAI.SharpNodal.Carleman.ShrinkingSupports`, `OAI.SharpNodal.Carleman.Smooth`, `OAI.SharpNodal.Carleman.SupportIndex`, `OAI.SharpNodal.Carleman.SupportLimit`, `OAI.SharpNodal.Carleman.bilaplacianEnergy`, `OAI.SharpNodal.Carleman.conjugatedOperator`, `OAI.SharpNodal.Carleman.coordinateGradient`, `OAI.SharpNodal.Carleman.euclideanLaplacian`, `OAI.SharpNodal.Carleman.gradientEnergy`, `OAI.SharpNodal.Carleman.gradientSquared`, `OAI.SharpNodal.Carleman.hessianEnergy`, `OAI.SharpNodal.Carleman.hessianGradientEnergy`, `OAI.SharpNodal.Carleman.l2norm`, `OAI.SharpNodal.Carleman.l2sq`, `OAI.SharpNodal.Carleman.normalizedPartial`, `OAI.SharpNodal.Carleman.normalizedTransport`, `OAI.SharpNodal.Carleman.plusPart`, `OAI.SharpNodal.Carleman.potentialTransport`, `OAI.SharpNodal.Carleman.quadraticEnergy`, `OAI.SharpNodal.Carleman.skewPart`, `OAI.SharpNodal.Carleman.supportFilter`, `OAI.SharpNodal.Carleman.tiltedWeight`, `OAI.SharpNodal.Descent.Label`, `OAI.SharpNodal.Descent.Tree`, `OAI.SharpNodal.Descent.Tree.ScaledFloors`, `OAI.SharpNodal.Descent.Tree.Valid`, `OAI.SharpNodal.Descent.Tree.floorCost`, `OAI.SharpNodal.Descent.Tree.goodProb`, `OAI.SharpNodal.Descent.Tree.massCost`, `OAI.SharpNodal.Descent.Tree.root`, `OAI.SharpNodal.Descent.Tree.tiltCost`, `OAI.SharpNodal.Geometry.ChartSmooth`, `OAI.SharpNodal.Geometry.IsConformal`, `OAI.SharpNodal.Geometry.NormalizedEigen`, `OAI.SharpNodal.Geometry.chartConductivity`, `OAI.SharpNodal.Geometry.chartScalarLaplace`, `OAI.SharpNodal.Geometry.conformalFactor`, `OAI.SharpNodal.Geometry.coordDet`, `OAI.SharpNodal.Geometry.pullMetric`, `OAI.SharpNodal.Geometry.scalarDensity` and 179 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/NodalLength, in whole or in part: `NodalLength_AffineError`, `NodalLength_Carleman`, `NodalLength_Cells`, `NodalLength_Commutator`, `NodalLength_ComplexDerivatives`, `NodalLength_Conductivity`, `NodalLength_Cutoffs`, `NodalLength_Decomposition`, `NodalLength_Descent`, `NodalLength_Distributional`, `NodalLength_Divisors`, `NodalLength_Eigenfunctions`, `NodalLength_Elliptic`, `NodalLength_Energy`, `NodalLength_Excursions`, `NodalLength_GridImprovement`, `NodalLength_GridPaths`, `NodalLength_HolomorphicGradient`, `NodalLength_Integration`, `NodalLength_InteriorMass`, `NodalLength_Isothermal`, `NodalLength_Lattice`, `NodalLength_LogGradients`, `NodalLength_MassComparison`, `NodalLength_MetricFamilies`, `NodalLength_MetricFlux`, `NodalLength_Multipliers`, `NodalLength_NodalGraphs`, `NodalLength_Normalization`, `NodalLength_NormalizedCharts`, `NodalLength_Parametrix`, `NodalLength_Persistence`, `NodalLength_Potential`, `NodalLength_ProfileExtraction`, `NodalLength_ProfileTests`, `NodalLength_RegularWeights`, `NodalLength_Regularization`, `NodalLength_RieszMeasure`, `NodalLength_ScaledWaves`, `NodalLength_Similarity`, `NodalLength_StoppedTrees`, `NodalLength_Subdivision`, `NodalLength_Subharmonic`, `NodalLength_SupportLimits`, `NodalLength_TerminalGrid`, `NodalLength_Vitali`, `NodalLength_WitnessPacking`.
--
--   **Imports.** It imports the published bundle `Def_NodalLength`.
--
--   **Imported by** (directly, in this split): the statements `OAI_SharpNodal_Geometry_IsConformal_eigenfunction`, `OAI.SharpNodal.Geometry.IsConformal.uniform_chart_wave`, `OAI.SharpNodal.Geometry.conjugate_chart_conformal`, `OAI.SharpNodal.Geometry.exists_isothermal_chart`, `OAI_SharpNodal_Geometry_exists_normalized_global_length`, `OAI.SharpNodal.Geometry.laplaceBeltrami_in_chart`, `OAI.SharpNodal.Geometry.normalized_frequency_gap`, `OAI.SharpNodal.Geometry.uniform_local_sup_lower`, `OAI.SharpNodal.Grid.uniform_terminal_growth`, `OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates`, `OAI.SharpNodal.Profiles.full_test_of_profile`, `OAI.SharpNodal.Profiles.normalized_small_potential_length`, `OAI.SharpNodal.Profiles.profile_small_affine_grid_gap`, `OAI.SharpNodal.Profiles.sup_profile_le_local`, `OAI.SharpNodal.Profiles.uniform_normalized_subdivision`, `OAI.SharpNodal.Profiles.uniform_persistence_alternative` and `OAI.SharpNodal.Profiles.uniform_plane_length`; the proofs of `OAI_SharpNodal_Geometry_IsConformal_eigenfunction`, `OAI.SharpNodal.Geometry.IsConformal.uniform_chart_wave`, `OAI.SharpNodal.Geometry.conjugate_chart_conformal`, `OAI.SharpNodal.Geometry.exists_isothermal_chart`, `OAI_SharpNodal_Geometry_exists_normalized_global_length`, `OAI.SharpNodal.Geometry.laplaceBeltrami_in_chart`, `OAI.SharpNodal.Geometry.normalized_frequency_gap`, `OAI.SharpNodal.Geometry.uniform_local_sup_lower`, `OAI.SharpNodal.Grid.uniform_terminal_growth`, `OAI.SharpNodal.Main`, `OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates`, `OAI.SharpNodal.Profiles.full_test_of_profile`, `OAI.SharpNodal.Profiles.normalized_small_potential_length`, `OAI.SharpNodal.Profiles.profile_small_affine_grid_gap`, `OAI.SharpNodal.Profiles.sup_profile_le_local`, `OAI.SharpNodal.Profiles.uniform_normalized_subdivision`, `OAI.SharpNodal.Profiles.uniform_persistence_alternative` and `OAI.SharpNodal.Profiles.uniform_plane_length`.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/NodalLength at commit adc7f12

import Mathlib
import Definitions.Def_NodalLength

section
-- module Solutions.OAIQ4_Nl.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Integration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

abbrev Smooth (f : Plane → ℝ) : Prop := ContDiff ℝ ∞ f

lemma smooth_partial {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) :
    Smooth (coordPartial f i) := by
  exact (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).clm_apply contDiff_const

lemma compact_partial {f : Plane → ℝ} (hf : HasCompactSupport f) (i : Fin 2) :
    HasCompactSupport (coordPartial f i) :=
  hf.fderiv_apply ℝ (EuclideanSpace.single i 1)

lemma partial_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y + g y) i x =
      coordPartial f i x + coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_add (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt]
  rfl

lemma partial_const_mul {f : Plane → ℝ} (hf : Smooth f) (c : ℝ)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => c * f y) i x = c * coordPartial f i x := by
  unfold coordPartial
  rw [fderiv_const_mul (hf.differentiable (by simp)).differentiableAt]
  rfl

def euclideanLaplacian (f : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, coordPartial (coordPartial f i) i x

def skewPart (T v : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, (-2 * coordPartial T i x * coordPartial v i x -
    coordPartial (coordPartial T i) i x * v x)

lemma smooth_laplacian {f : Plane → ℝ} (hf : Smooth f) :
    Smooth (euclideanLaplacian f) :=
  ContDiff.sum fun i _ => smooth_partial (smooth_partial hf i) i

lemma compact_laplacian {f : Plane → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (euclideanLaplacian f) := by
  convert (HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ => compact_partial (compact_partial hf i) i)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (funext x; simp [euclideanLaplacian, Finset.sum_apply])


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Commutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

def gradientSquared (T : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, coordPartial T i x * coordPartial T i x

def l2sq (f : Plane → ℝ) : ℝ := ∫ x, f x * f x

def quadraticEnergy (A B C : ℝ) (f g : Plane → ℝ) : ℝ :=
  A * l2sq f + (2 * B) * (∫ x, f x * g x) + C * l2sq g


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

def l2norm (f : Plane → ℝ) : ℝ := Real.sqrt (l2sq f)

def plusPart (a v : Plane → ℝ) (x : Plane) : ℝ := euclideanLaplacian v x + a x * v x

def gradientEnergy (v : Plane → ℝ) : ℝ := ∑ i : Fin 2, l2sq (coordPartial v i)

def hessianEnergy (T v : Plane → ℝ) : ℝ :=
  ∑ j : Fin 2, ∑ i : Fin 2,
    ∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x

def bilaplacianEnergy (T v : Plane → ℝ) : ℝ :=
  ∑ j : Fin 2, ∑ i : Fin 2,
    ∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x * (v x * v x)

def potentialTransport (a T v : Plane → ℝ) : ℝ :=
  ∑ i : Fin 2, ∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

def normalizedPartial (v : Plane → ℝ) (D : ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  coordPartial v i x / D

def normalizedTransport (T v : Plane → ℝ) (D : ℝ) (x : Plane) : ℝ :=
  (coordPartial T 0 x / D) * normalizedPartial v D 0 x +
  (coordPartial T 1 x / D) * normalizedPartial v D 1 x


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_SupportLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

abbrev SupportIndex (v : ℕ → Plane → ℝ) := Σ j : ℕ, {x : Plane // x ∈ tsupport (v j)}

def supportFilter (v : ℕ → Plane → ℝ) : Filter (SupportIndex v) :=
  Filter.comap (fun z => z.1) Filter.atTop

def SupportLimit (v f : ℕ → Plane → ℝ) (A : ℝ) : Prop :=
  Filter.Tendsto (fun z : SupportIndex v => f z.1 z.2.1) (supportFilter v) (𝓝 A)

def hessianGradientEnergy (T v : Plane → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    ∫ x, coordPartial (coordPartial T j) i x * coordPartial T j x * coordPartial T i x * (v x*v x)


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Carleman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

def tiltedWeight (B : Plane) (S : ℝ) (χ : Plane → ℝ) (x : Plane) : ℝ :=
  -inner ℝ B x-S*χ x

open Filter in

def ShrinkingSupports (v : ℕ → Plane → ℝ) (x₀ : Plane) : Prop :=
  Tendsto (fun z : SupportIndex v => z.2.1) (supportFilter v) (𝓝 x₀)

def coordinateGradient (χ : Plane → ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 (fun i => coordPartial χ i x)

def conjugatedOperator (T p : Plane → ℝ) (K : ℝ) (v : Plane → ℝ) (x : Plane) : ℝ :=
  plusPart (fun y => gradientSquared T y+K^2*p y) v x+skewPart T v x

lemma laplacian_const_mul {v : Plane → ℝ} (hv : Smooth v) (c : ℝ) :
    euclideanLaplacian (fun x => c*v x) = fun x => c*euclideanLaplacian v x := by
  ext x
  unfold euclideanLaplacian
  simp_rw [funext (partial_const_mul hv c _)]
  simp_rw [partial_const_mul (smooth_partial hv _) c]
  rw [Finset.mul_sum]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Cutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma smooth_cutoff_mul {Ω : Set Plane} {ζ f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hζ : Smooth ζ) (hsub : tsupport ζ ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) : Smooth (fun x => ζ x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ζ
  · exact hζ.contDiffAt.mul (hf.contDiffAt (hΩ.mem_nhds (hsub hx)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

lemma exists_smooth_cutoff {Ω : Set Plane} {x₀ : Plane}
    (hΩ : Ω ∈ 𝓝 x₀) : ∃ (ζ : Plane → ℝ) (r : ℝ),
      0 < r ∧ Smooth ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Ω ∧
      ∀ x ∈ Metric.ball x₀ r, ζ x=1 := by
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hΩ
  let ζ : ContDiffBump x₀ :=
    { rIn := R/4
      rOut := R/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨ζ, R/4, by positivity, ζ.contDiff, ζ.hasCompactSupport, ?_, ?_⟩
  · rw [ζ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [ζ]; linarith)).trans hRsub
  · intro x hx
    exact ζ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)

lemma partial_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 2) : coordPartial f i =ᶠ[𝓝 x] coordPartial g i := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hy

lemma laplacian_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) : euclideanLaplacian f =ᶠ[𝓝 x] euclideanLaplacian g := by
  have h₀ := partial_eventuallyEq (partial_eventuallyEq h 0) 0
  have h₁ := partial_eventuallyEq (partial_eventuallyEq h 1) 1
  filter_upwards [h₀, h₁] with y hy₀ hy₁
  simp only [euclideanLaplacian, Fin.sum_univ_two, hy₀, hy₁]

end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MassComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section
open scoped Topology ENNReal
open MeasureTheory Filter Set
namespace SharpNodal.Profiles

def logRate (S : ℝ) (m : ℝ≥0∞) : EReal := ((2*S)⁻¹ : ℝ) * m.log

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

def tiltedMass (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ)
    (f : Plane → ℝ) (E : Set Plane) : ℝ≥0∞ :=
  ∫⁻ x in E, ENNReal.ofReal (c*(Real.exp (tiltedWeight B S (fun y => -f y) x)*U x)^2)

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

namespace SharpNodal.Profiles
open Carleman

structure WeightedProfileBounds (Ω : Set Plane) (S : ℕ → ℝ) (B : ℕ → Plane)
    (U : ℕ → Plane → ℝ) (c : ℕ → ℝ) (V : Plane → EReal) : Prop where
  upper : ∀ (f : Plane → ℝ), ContinuousOn f Ω → ∀ F : Set Plane,
    IsCompact F → F⊆Ω →
    limsup (fun j => logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f F)) atTop ≤
      ⨆ x∈F, V x+(f x:EReal)
  lower : ∀ (f : Plane → ℝ), ContinuousOn f Ω → ∀ G : Set Plane,
    IsOpen G → G⊆Ω →
    (⨆ x∈G, V x+(f x:EReal)) ≤
      liminf (fun j => logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f G)) atTop

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

def radiusSquare (x₀ x : Plane) : ℝ := ‖x-x₀‖^2

def contactQuartic (x₀ x : Plane) : ℝ := radiusSquare x₀ x*radiusSquare x₀ x

lemma laplacian_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun y => f y+g y) x=euclideanLaplacian f x+euclideanLaplacian g x := by
  unfold euclideanLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show coordPartial (fun y => f y+g y) i = fun y => coordPartial f i y+coordPartial g i y
    from funext (partial_add hf hg i)]
  exact partial_add (smooth_partial hf i) (smooth_partial hg i) i x

theorem smooth_extension_near {Ω : Set Plane} {f : Plane → ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω) (hf : ContDiffOn ℝ ∞ f Ω) :
    ∃ (g : Plane → ℝ) (r : ℝ), Smooth g ∧ 0 < r ∧ Metric.ball x₀ r⊆Ω ∧
      ∀ x∈Metric.ball x₀ r, g x=f x := by
  obtain ⟨ζ, r, hr, hζ, hcζ, hζΩ, hζ1⟩ := exists_smooth_cutoff (hΩ.mem_nhds hx₀)
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  refine ⟨fun x => ζ x*f x, min r R, smooth_cutoff_mul hΩ hζ hζΩ hf,
    lt_min hr hR, (Metric.ball_subset_ball (min_le_right _ _)).trans hRΩ, ?_⟩
  intro x hx
  dsimp only
  rw [hζ1 x (Metric.ball_subset_ball (min_le_left _ _) hx), one_mul]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

abbrev BilinearForm := Plane →L[ℝ] Plane →L[ℝ] ℝ

def SymmetricForm (A : BilinearForm) : Prop := ∀ x y, A x y=A y x

def centeredQuadratic (A : BilinearForm) (x₀ x : Plane) : ℝ :=
  (1/2:ℝ)*A (x-x₀) (x-x₀)

def secondTaylorPolynomial (f : Plane → ℝ) (x₀ x : Plane) : ℝ :=
  f x₀+fderiv ℝ f x₀ (x-x₀)+centeredQuadratic (fderiv ℝ (fderiv ℝ f) x₀) x₀ x

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

def IsUpperTest (V : Plane → EReal) (f : Plane → ℝ) (x₀ : Plane) : Prop :=
  V x₀=(f x₀:EReal) ∧ ∀ᶠ x in 𝓝 x₀, V x≤(f x:EReal)

def NonexceptionalTestProperty (Ω : Set Plane) (V : Plane → EReal) : Prop :=
  ∀ (f : Plane → ℝ), Smooth f → ∀ x₀∈Ω, IsUpperTest V f x₀ →
    coordinateGradient f x₀≠0 → 0≤euclideanLaplacian f x₀

def FullTestProperty (Ω : Set Plane) (V : Plane → EReal) : Prop :=
  ∀ (f : Plane → ℝ), Smooth f → ∀ x₀∈Ω, IsUpperTest V f x₀ →
    0≤euclideanLaplacian f x₀

def formTrace (A : BilinearForm) : ℝ :=
  ∑ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

def quadraticAffine (c : ℝ) (L : Plane →L[ℝ] ℝ) (A : BilinearForm)
    (x₀ x : Plane) : ℝ := c+L (x-x₀)+centeredQuadratic A x₀ x

def innerForm : BilinearForm := innerSL ℝ

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

namespace SharpNodal.Profiles

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

def basisProfile (ell : countableBasis X → EReal) (x : X) : EReal :=
  ⨅ i, ⨅ (_ : x∈i.val), ell i

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
namespace SharpNodal.Profiles

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

def weightedMass (μ : Measure X) (S : ℝ) (f : X → ℝ) (E : Set X) : ℝ≥0∞ :=
  ∫⁻ x in E, ENNReal.ofReal (Real.exp (2*S*f x)) ∂μ

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
namespace SharpNodal.Profiles
open Carleman

def tiltedDensity (B : Plane) (U : Plane → ℝ) (c : ℝ) (x : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (c*(Real.exp (-inner ℝ B x)*U x)^2)

def tiltedMeasure (Ω : Set Plane) (B : Plane) (U : Plane → ℝ) (c : ℝ) : Measure Plane :=
  (volume.restrict Ω).withDensity (tiltedDensity B U c)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def ShiftedTestProperty (Ω : Set Plane) (V : Plane → EReal) (b : Plane) (d : ℝ) : Prop :=
  ∀ (f : Plane → ℝ), Smooth f → ∀ x₀∈Ω, IsUpperTest V f x₀ →
    b+d • coordinateGradient f x₀≠0 → 0≤euclideanLaplacian f x₀

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subharmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

def planeComplex : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

end SharpNodal.Profiles
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Regularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

variable {X : Type*} [PseudoMetricSpace X]

def truncBelow (V : X → EReal) (n : ℕ) (x : X) : ℝ :=
  (max (V x) ((-(n:ℝ):ℝ):EReal)).toReal

def supRegularize (K : Set X) (V : X → EReal) (n : ℕ) (x : X) : ℝ :=
  ⨆ y : K, truncBelow V n y-(n:ℝ)*dist x y

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def circleParameterMeasure : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioc 0 (2*Real.pi))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def polarParameterMeasure : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioo (-Real.pi) Real.pi)

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Distributional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def planeCircleAverage (f : Plane → ℝ) (a : Plane) (r : ℝ) : ℝ :=
  Real.circleAverage (f∘planeComplex.symm) (planeComplex a) r

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def circleVector (r t : ℝ) : Plane := planeComplex.symm (circleMap 0 r t)

instance circleParameter_isProbability : IsProbabilityMeasure circleParameterMeasure := by
  constructor
  rw [circleParameterMeasure,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Ioc,smul_eq_mul,sub_zero,← ENNReal.ofReal_mul (by positivity),inv_mul_cancel₀ (by positivity)]
  simp

lemma integrable_mul_continuous_compact {w f : Plane → ℝ} (hw : Integrable w)
    (hf : Continuous f) (hc : HasCompactSupport f) : Integrable (fun x => w x*f x) := by
  obtain ⟨M,hM⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  exact hw.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall fun x => hM (mem_range_self x))

end SharpNodal.Profiles
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_RieszMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def smoothCompactTests : Submodule ℝ C_c(Plane, ℝ) where
  carrier := {f | Smooth (f : Plane → ℝ)}
  zero_mem' := by
    change Smooth (fun _ : Plane => (0:ℝ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change Smooth (f : Plane → ℝ) at hf
    change Smooth (g : Plane → ℝ) at hg
    change Smooth (fun x => f x+g x)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Smooth (f : Plane → ℝ) at hf
    change Smooth (fun x => c*f x)
    exact contDiff_const.mul hf

def compactTestsPositiveCone : PointedCone ℝ C_c(Plane,ℝ) where
  carrier := {f | ∀x,0≤f x}
  zero_mem' := by intro x; rfl
  add_mem' := by intro f g hf hg x; exact add_nonneg (hf x) (hg x)
  smul_mem' := by intro c f hf x; exact mul_nonneg c.property (hf x)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def localizedLaplacianFunctional {w ζ : Plane → ℝ} (hw : Integrable w)
    (hζ : Smooth ζ) (hcζ : HasCompactSupport ζ) : smoothCompactTests →ₗ[ℝ] ℝ where
  toFun f := ∫x,w x*euclideanLaplacian (fun y => ζ y*f.val y) x
  map_add' := by
    intro f g
    have hf : Smooth (f.val : Plane → ℝ) := f.property
    have hg : Smooth (g.val : Plane → ℝ) := g.property
    change (∫x,w x*euclideanLaplacian (fun y => ζ y*(f.val y+g.val y)) x)=_
    simp_rw [mul_add,laplacian_add (hζ.mul hf) (hζ.mul hg),mul_add]
    exact integral_add (integrable_mul_continuous_compact hw (smooth_laplacian (hζ.mul hf)).continuous (compact_laplacian hcζ.mul_right))
      (integrable_mul_continuous_compact hw (smooth_laplacian (hζ.mul hg)).continuous (compact_laplacian hcζ.mul_right))
  map_smul' := by
    intro c f
    have hf : Smooth (f.val : Plane → ℝ) := f.property
    change (∫x,w x*euclideanLaplacian (fun y => ζ y*(c*f.val y)) x)=c*(∫x,w x*euclideanLaplacian (fun y => ζ y*f.val y) x)
    simp_rw [show (fun y => ζ y*(c*f.val y))=(fun y => c*(ζ y*f.val y)) by funext y; ring,
      laplacian_const_mul (hζ.mul hf) c]
    simp_rw [show ∀x,w x*(c*euclideanLaplacian (fun y => ζ y*f.val y) x)=c*(w x*euclideanLaplacian (fun y => ζ y*f.val y) x) by intro x; ring]
    exact integral_const_mul _ _

end SharpNodal.Profiles
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def regularizedLog (ε : ℝ) (x : Plane) : ℝ := Real.log (‖x‖^2+ε^2)/2

def logDenom (ε : ℝ) (x : Plane) : ℝ := ‖x‖^2+ε^2

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def logKernel (ε : ℝ) (x : Plane) : ℝ := ε^2/(Real.pi*(‖x‖^2+ε^2)^2)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def aeLogPotential (ν : Measure Plane) (x : Plane) : ℝ := ∫z,Real.log ‖x-z‖ ∂ν

end SharpNodal.Profiles
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Parametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

def parametrixCutoff : ContDiffBump (0:Plane) := ⟨1/8,1/4,by norm_num,by norm_num⟩
def parametrixInner : ContDiffBump (0:Plane) := ⟨1/16,1/8,by norm_num,by norm_num⟩
def parametrixSmoothLog (x : Plane) : ℝ := Real.log (‖x‖^2+(parametrixInner x)^2)/2

def parametrixCorrection (x : Plane) : ℝ := (parametrixCutoff x-1)*parametrixSmoothLog x
def parametrixKernel (x : Plane) : ℝ := euclideanLaplacian parametrixCorrection x
def logParametrix (x : Plane) : ℝ := parametrixCutoff x*Real.log ‖x‖

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def rconv (f g : Plane → ℝ) : Plane → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def WeakHarmonicOn (w : Plane → ℝ) (Ω : Set Plane) : Prop :=
  ∀ (ψ : Plane → ℝ), Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
    (∫x,w x*euclideanLaplacian ψ x)=0

def weylRepresentative (w : Plane → ℝ) : Plane → ℝ :=
  fun x => -(2*Real.pi)⁻¹*rconv w (fun y => parametrixKernel (-y)) x

end SharpNodal.Profiles
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def normalizedRiesz (μ : Measure Plane) : Measure Plane :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • μ.restrict (Metric.ball (0:Plane) 4)

end SharpNodal.Profiles
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_AffineError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def logDiskAverage (y : Plane) (ρ : ℝ) (z : Plane) : ℝ :=
  Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖y+ρ • ξ-z‖)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

instance unitDisk_volume_finite : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def farGradient (R ρ : ℝ) (y z : Plane) : Plane :=
  if 2*R*ρ<‖y-z‖ then (‖y-z‖^2)⁻¹ • (y-z) else 0

def farWeight (R ρ : ℝ) (y z : Plane) : ℝ :=
  if 2*R*ρ<‖y-z‖ then ρ^2/‖y-z‖^2 else 1

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def diskAverage (f : Plane → ℝ) (y : Plane) (ρ : ℝ) : ℝ :=
  Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,f (y+ρ • ξ))

end SharpNodal.Profiles
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_RegularWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function

namespace SharpNodal.Profiles
open Carleman

def regularWeight (ρ : ℝ) (x : Plane) : ℝ := ρ^2/(ρ^2+‖x‖^2)
def regularGradientWeight (ρ : ℝ) (x : Plane) : ℝ := (ρ+‖x‖)⁻¹

end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GridImprovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

abbrev GridIndex (A : ℕ) := Fin 2 → Fin A

def gridCenter (A : ℕ) (p : GridIndex A) : Plane :=
  WithLp.toLp 2 (fun i => ((p i:ℝ)+1/2)/(A:ℝ)-1/2)

def gridCenters (A : ℕ) : Finset Plane := (Finset.univ : Finset (GridIndex A)).image (gridCenter A)

lemma gridCenter_coord {A : ℕ} (hA : 0<A) (p : GridIndex A) (i : Fin 2) :
    |gridCenter A p i|≤1/2 := by
  change |((p i:ℝ)+1/2)/(A:ℝ)-1/2|≤1/2
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr hA
  have hp0 : 0≤(p i:ℝ) := Nat.cast_nonneg _
  have hpA : (p i:ℝ)+1≤(A:ℝ) := by exact_mod_cast (p i).isLt
  rw [abs_le]
  constructor
  · have hd : 0≤((p i:ℝ)+1/2)/(A:ℝ) := by positivity
    linarith
  · have hd : ((p i:ℝ)+1/2)/(A:ℝ)≤1 := (div_le_one hAr).mpr (by linarith)
    linarith

lemma gridCenter_norm {A : ℕ} (hA : 0<A) (p : GridIndex A) : ‖gridCenter A p‖≤1 := by
  have h0 := gridCenter_coord hA p 0
  have h1 := gridCenter_coord hA p 1
  have hn := EuclideanSpace.real_norm_sq_eq (gridCenter A p)
  rw [Fin.sum_univ_two] at hn
  have hs0 := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hs1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs] at hs0 hs1
  nlinarith [norm_nonneg (gridCenter A p)]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def massExcess (a b : ℝ≥0∞) : ℝ := Real.log (a.toReal/b.toReal)/2

end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def gridExcess (A : ℕ) (S : ℝ) (B : Plane) (U : Plane → ℝ) (d : ℝ)
    (c : Plane → Plane) (y : Plane) : ℝ :=
  massExcess (tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
      (Metric.ball y (1000*(A:ℝ)⁻¹)))
    (tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
      (Metric.ball y ((A:ℝ)⁻¹)))

def gridMassesFinite (A : ℕ) (S : ℝ) (B : Plane) (U : Plane → ℝ) (d : ℝ)
    (c : Plane → Plane) : Prop :=
  ∀y∈gridCenters A,tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
    (Metric.ball y ((A:ℝ)⁻¹))≠0 ∧
    tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
      (Metric.ball y (1000*(A:ℝ)⁻¹))≠⊤

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

structure NormalizedPDEData (Cp : ℝ) where
  p : Plane → ℝ
  U : Plane → ℝ
  B : Plane
  S : ℝ
  K : ℝ
  d : ℝ
  smooth_p : ContDiffOn ℝ ∞ p (Metric.ball 0 1000)
  smooth_U : ContDiffOn ℝ ∞ U (Metric.ball 0 1000)
  S_pos : 0<S
  d_pos : 0<d
  coefficient_bound : ∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp
  equation : ∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0
  normalized : tiltedMass S B U d 0 (Metric.ball 0 1000)≤1
  parent_growth : (-1:EReal)≤logRate S (tiltedMass S B U d 0 (Metric.ball 0 1))

def NormalizedPDEData.Small {Cp : ℝ} (D : NormalizedPDEData Cp) (T : ℝ) : Prop :=
  T≤D.S ∧ |D.K/(D.S+‖D.B‖)|≤T⁻¹ ∧
  ∀i x,x∈Metric.ball (0:Plane) 1000 →
    |D.K^2*coordPartial D.p i x/(D.S*(D.S+‖D.B‖))|≤Cp*T⁻¹

def NormalizedPDEData.HasGridCorrection {Cp : ℝ} (D : NormalizedPDEData Cp)
    (A : ℕ) (Cs : ℝ) : Prop :=
  ∃c : Plane → Plane,((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖)≤Cs ∧
    gridMassesFinite A D.S D.B D.U D.d c ∧
    ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,gridExcess A D.S D.B D.U D.d c y/D.S)<(A:ℝ)⁻¹/2

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def centeredMass (T : Plane) (U : Plane → ℝ) (y : Plane) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻x in Metric.ball y r,ENNReal.ofReal ((Real.exp (-inner ℝ T (x-y))*U x)^2)

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Descent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

structure UnitWave (Cp a₀ : ℝ) where
  p : Plane → ℝ
  U : Plane → ℝ
  K : ℝ
  frequency_lower : a₀ ≤ K
  smooth_p : ContDiffOn ℝ ∞ p (Metric.ball 0 1000)
  smooth_U : ContDiffOn ℝ ∞ U (Metric.ball 0 1000)
  coefficient_bound : ∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp
  derivative_bound : ∀i x,x∈Metric.ball (0:Plane) 1000 → |coordPartial p i x|≤Cp
  equation : ∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0
  inner_nonzero : centeredMass 0 U 0 1≠0
  outer_finite : centeredMass 0 U 0 1000≠⊤

def UnitWave.excess {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) : ℝ :=
  massExcess (centeredMass (D.K • b) D.U 0 1000) (centeredMass (D.K • b) D.U 0 1)

def UnitWave.growth {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) : ℝ :=
  D.excess b/D.K

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_StoppedTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory

namespace SharpNodal.Descent

structure Label where
  mass : ℝ
  tilt : Plane
  floor : ℝ

inductive Tree (ι : Type*) where
  | stop (root : Label)
  | step (root : Label) (children : ι → Tree ι)

namespace Tree
variable {ι : Type*} [Fintype ι]

def root : Tree ι → Label
  | .stop a => a
  | .step a _ => a

def massCost : Tree ι → ℝ
  | .stop a => a.mass
  | .step a t => a.mass + 𝔼 i, massCost (t i)

def tiltCost : Tree ι → ℝ
  | .stop _ => 0
  | .step a t => 𝔼 i, (‖(root (t i)).tilt-a.tilt‖+tiltCost (t i))

def floorCost : Tree ι → ℝ
  | .stop _ => 0
  | .step a t => a.floor + 𝔼 i, floorCost (t i)

def Valid (C : ℝ) : Tree ι → Prop
  | .stop a => 0 ≤ a.mass ∧ 0 ≤ a.floor
  | .step a t => 0 ≤ a.mass ∧ 0 ≤ a.floor ∧
      (𝔼 i, (root (t i)).mass) ≤ (a.mass+a.floor)/2 ∧
      (𝔼 i, ‖(root (t i)).tilt-a.tilt‖) ≤ C*(a.mass+a.floor) ∧
      ∀i, Valid C (t i)

end Tree
end SharpNodal.Descent

noncomputable section
open scoped BigOperators
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def goodProb (P : Label → Prop) [DecidablePred P] : Tree ι → ℝ
  | .stop a => if P a then 1 else 0
  | .step a t => if P a then 𝔼 i, goodProb P (t i) else 0

end SharpNodal.Descent.Tree

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_LogGradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

def logGradient (x : Plane) : Plane := (‖x‖^2)⁻¹ • x

def aeLogGradient (ν : Measure Plane) (x : Plane) : Plane := ∫z,logGradient (x-z) ∂ν

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def WeakGradientZeroOn (w : Plane → ℝ) (Ω : Set Plane) : Prop :=
  ∀(ψ : Plane → ℝ), Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
    ∀i : Fin 2,(∫x,w x*coordPartial ψ i x)=0

def gradientBump (n : ℕ) : ContDiffBump (0:Plane) :=
  ⟨1/(2*((n:ℝ)+1)),1/((n:ℝ)+1),by positivity,by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]⟩

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Persistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology
open Filter Set MeasureTheory
namespace SharpNodal.Profiles

def extendedGridCenter (r : ℝ) (p : Fin 2 → ℤ) : Plane :=
  WithLp.toLp 2 (fun i => -1/2+((p i:ℝ)+1/2)*r)

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ScaledWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

def rescaleMap (y : Plane) (r : ℝ) (x : Plane) : Plane := y+r • x

lemma smooth_rescaleMap (y : Plane) (r : ℝ) : ContDiff ℝ ∞ (rescaleMap y r) := by
  unfold rescaleMap
  fun_prop

lemma partial_rescale {f : Plane → ℝ} (hf : Smooth f) (y : Plane) (r : ℝ)
    (x : Plane) (i : Fin 2) :
    coordPartial (f ∘ rescaleMap y r) i x=r*coordPartial f i (rescaleMap y r x) := by
  have h := ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
    (((hasFDerivAt_id (𝕜:=ℝ) x).const_smul r).const_add y)
  change fderiv ℝ (f ∘ rescaleMap y r) x _ = _
  have he : fderiv ℝ (f ∘ rescaleMap y r) x=
    (fderiv ℝ f (rescaleMap y r x)).comp (r • ContinuousLinearMap.id ℝ Plane) := by
    simpa only [Function.comp_def,rescaleMap,Pi.smul_apply,id_eq] using h.fderiv
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,coordPartial]

lemma laplacian_rescale {f : Plane → ℝ} (hf : Smooth f) (y : Plane) (r : ℝ) (x : Plane) :
    euclideanLaplacian (f ∘ rescaleMap y r) x=r^2*euclideanLaplacian f (rescaleMap y r x) := by
  unfold euclideanLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (f ∘ rescaleMap y r) i=(fun x =>r*coordPartial f i (rescaleMap y r x)) from
    funext (fun x =>partial_rescale hf y r x i)]
  change coordPartial (fun z =>r*((coordPartial f i) ∘ rescaleMap y r) z) i x = _
  rw [partial_const_mul ((smooth_partial hf i).comp (smooth_rescaleMap y r)),
    partial_rescale (smooth_partial hf i)]
  ring

lemma partial_rescale_local {Ω : Set Plane} {f : Plane → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (y : Plane) (r : ℝ) (x : Plane) (hx : rescaleMap y r x∈Ω)
    (i : Fin 2) :
    coordPartial (f ∘ rescaleMap y r) i x=r*coordPartial f i (rescaleMap y r x) := by
  obtain ⟨g,t,hg,ht,_,he⟩ := smooth_extension_near hΩ hx hf
  have hfg : f=ᶠ[𝓝 (rescaleMap y r x)] g := by
    filter_upwards [Metric.ball_mem_nhds _ ht] with z hz using (he z hz).symm
  have hfg' := hfg.comp_tendsto (smooth_rescaleMap y r).continuous.continuousAt
  rw [(partial_eventuallyEq hfg' i).eq_of_nhds, (partial_eventuallyEq hfg i).eq_of_nhds]
  exact partial_rescale hg y r x i

lemma laplacian_rescale_local {Ω : Set Plane} {f : Plane → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (y : Plane) (r : ℝ) (x : Plane) (hx : rescaleMap y r x∈Ω) :
    euclideanLaplacian (f ∘ rescaleMap y r) x=r^2*euclideanLaplacian f (rescaleMap y r x) := by
  obtain ⟨g,t,hg,ht,_,he⟩ := smooth_extension_near hΩ hx hf
  have hfg : f=ᶠ[𝓝 (rescaleMap y r x)] g := by
    filter_upwards [Metric.ball_mem_nhds _ ht] with z hz using (he z hz).symm
  have hfg' := hfg.comp_tendsto (smooth_rescaleMap y r).continuous.continuousAt
  rw [(laplacian_eventuallyEq hfg').eq_of_nhds, (laplacian_eventuallyEq hfg).eq_of_nhds]
  exact laplacian_rescale hg y r x

lemma rescaleMap_ball_preimage (y : Plane) {s : ℝ} (hs : 0 < s) (z : Plane) (r : ℝ) :
    (rescaleMap y s) ⁻¹' Metric.ball (rescaleMap y s z) (s*r)=Metric.ball z r := by
  ext x
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,rescaleMap]
  rw [show y+s • x-(y+s • z)=s • (x-z) by module,
    norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  exact mul_lt_mul_iff_right₀ hs

lemma map_volume_rescaleMap (y : Plane) {s : ℝ} (hs : 0 < s) :
    Measure.map (rescaleMap y s) volume=ENNReal.ofReal (s^2)⁻¹ • (volume : Measure Plane) := by
  have he : rescaleMap y s=(fun x : Plane =>y+x) ∘ (fun x : Plane =>s • x) := rfl
  have hm1 : Measurable (fun x : Plane =>y+x) := by fun_prop
  have hm2 : Measurable (fun x : Plane =>s • x) := by fun_prop
  rw [he,← Measure.map_map hm1 hm2,
    Measure.map_addHaar_smul volume hs.ne',Measure.map_smul,map_add_left_eq_self]
  simp only [Plane, finrank_euclideanSpace_fin,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg s)),
    ENNReal.ofReal_inv_of_pos (sq_pos_of_pos hs)]

lemma centeredMass_rescale (T : Plane) (U : Plane → ℝ) (y z : Plane) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    centeredMass (s • T) (U ∘ rescaleMap y s) z r=
      ENNReal.ofReal (s^2)⁻¹*centeredMass T U (rescaleMap y s z) (s*r) := by
  let e : Plane ≃ᵐ Plane := ((Homeomorph.smul (Units.mk0 s hs.ne')).trans (Homeomorph.addLeft y)).toMeasurableEquiv
  have he (x : Plane) : e x=rescaleMap y s x := rfl
  have hpre : e ⁻¹' Metric.ball (rescaleMap y s z) (s*r)=Metric.ball z r :=
    rescaleMap_ball_preimage y hs z r
  have hmap := map_volume_rescaleMap y hs
  have hf (x : Plane) :
      ENNReal.ofReal ((Real.exp (-inner ℝ T (e x-rescaleMap y s z))*U (e x))^2)=
        ENNReal.ofReal ((Real.exp (-inner ℝ (s • T) (x-z))*(U ∘ rescaleMap y s) x)^2) := by
    rw [he]
    have hh : rescaleMap y s x-rescaleMap y s z=s • (x-z) := by unfold rescaleMap; module
    rw [hh,inner_smul_right,inner_smul_left]
    rfl
  have hh := lintegral_map_equiv
    ((Metric.ball (rescaleMap y s z) (s*r)).indicator
      (fun x => ENNReal.ofReal ((Real.exp (-inner ℝ T (x-rescaleMap y s z))*U x)^2))) e
    (μ:=(volume : Measure Plane))
  rw [show Measure.map e volume=ENNReal.ofReal (s^2)⁻¹ • (volume : Measure Plane) from hmap,
    lintegral_smul_measure,lintegral_indicator Metric.isOpen_ball.measurableSet] at hh
  have hind : (fun a =>(Metric.ball (rescaleMap y s z) (s*r)).indicator
      (fun x => ENNReal.ofReal ((Real.exp (-inner ℝ T (x-rescaleMap y s z))*U x)^2)) (e a))=
    (Metric.ball z r).indicator
      (fun x => ENNReal.ofReal ((Real.exp (-inner ℝ (s • T) (x-z))*(U ∘ rescaleMap y s) x)^2)) := by
    funext x
    have hm : e x∈Metric.ball (rescaleMap y s z) (s*r) ↔ x∈Metric.ball z r := by
      change x∈e ⁻¹' Metric.ball (rescaleMap y s z) (s*r) ↔ _
      rw [hpre]
    by_cases hx : x∈Metric.ball z r
    · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (hm.mpr hx),hf]
    · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (fun h => hx (hm.mp h))]
  rw [hind,lintegral_indicator Metric.isOpen_ball.measurableSet] at hh
  exact hh.symm

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

structure ScaledWave (Cp a₀ : ℝ) extends UnitWave Cp a₀ where
  side : ℝ
  side_pos : 0 < side
  side_le_one : side ≤ 1
  physical_derivative : ∀i x,x∈Metric.ball (0:Plane) 1000 →
    |coordPartial p i x|≤Cp*side

lemma rescaleMap_mapsTo {y : Plane} {r : ℝ} (hy : ‖y‖≤1) (hr : 0 ≤ r) (hr' : r≤1/2) :
    MapsTo (rescaleMap y r) (Metric.ball 0 1000) (Metric.ball 0 1000) := by
  intro x hx
  rw [Metric.mem_ball,dist_zero_right] at hx ⊢
  calc
    ‖rescaleMap y r x‖ ≤ ‖y‖+r*‖x‖ := by
      simpa only [rescaleMap,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] using norm_add_le y (r • x)
    _ ≤ 1+(1/2)*‖x‖ := add_le_add hy (mul_le_mul_of_nonneg_right hr' (norm_nonneg _))
    _ < 1000 := by linarith

def ScaledWave.child {Cp a₀ : ℝ} (D : ScaledWave Cp a₀) {A : ℕ} (hA : 2≤A)
    (i : GridIndex A) (hbottom : a₀≤D.K/(A:ℝ))
    (hm0 : centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹≠0)
    (hmt : centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹)≠⊤) :
    ScaledWave Cp a₀ where
  p := D.p ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹
  U := D.U ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹
  K := D.K/(A:ℝ)
  frequency_lower := hbottom
  smooth_p := D.smooth_p.comp (smooth_rescaleMap _ _).contDiffOn
    (rescaleMap_mapsTo (gridCenter_norm (by omega) i) (by positivity)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)))
  smooth_U := D.smooth_U.comp (smooth_rescaleMap _ _).contDiffOn
    (rescaleMap_mapsTo (gridCenter_norm (by omega) i) (by positivity)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)))
  coefficient_bound := fun x hx => D.coefficient_bound _
    (rescaleMap_mapsTo (gridCenter_norm (by omega) i) (by positivity)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx)
  derivative_bound := by
    intro j x hx
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have hmap := rescaleMap_mapsTo (gridCenter_norm (by omega : 0<A) i) (by positivity : 0≤(A:ℝ)⁻¹)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx
    rw [partial_rescale_local Metric.isOpen_ball D.smooth_p _ _ x hmap j,
      abs_mul,abs_of_pos (inv_pos.mpr (by positivity : 0<(A:ℝ)))]
    have hd := D.derivative_bound j _ hmap
    have hi : (A:ℝ)⁻¹≤1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
    calc
      _ ≤ 1*|coordPartial D.p j (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)| :=
        mul_le_mul_of_nonneg_right hi (abs_nonneg _)
      _ ≤ Cp := by simpa using hd
  equation := by
    intro x hx
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have hmap := rescaleMap_mapsTo (gridCenter_norm (by omega : 0<A) i) (by positivity : 0≤(A:ℝ)⁻¹)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx
    rw [laplacian_rescale_local Metric.isOpen_ball D.smooth_U _ _ x hmap]
    dsimp only [Function.comp_apply]
    have he := D.equation _ hmap
    calc
      _ = (A:ℝ)⁻¹^2*(euclideanLaplacian D.U (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)+
        D.K^2*D.p (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)*D.U (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)) := by ring
      _ = 0 := by rw [he,mul_zero]
  inner_nonzero := by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have he := centeredMass_rescale 0 D.U (gridCenter A i) 0
      (inv_pos.mpr (by positivity : 0<(A:ℝ))) 1
    simp only [smul_zero,rescaleMap,add_zero,mul_one] at he
    rw [he]
    exact mul_ne_zero (by simp [show A≠0 by omega]) hm0
  outer_finite := by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have he := centeredMass_rescale 0 D.U (gridCenter A i) 0
      (inv_pos.mpr (by positivity : 0<(A:ℝ))) 1000
    simp only [smul_zero,rescaleMap,add_zero] at he
    rw [he]
    exact ENNReal.mul_ne_top (by simp) (by simpa [mul_comm] using hmt)
  side := D.side/(A:ℝ)
  side_pos := div_pos D.side_pos (by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    linarith)
  side_le_one := by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    exact (div_le_self D.side_pos.le (by linarith)).trans D.side_le_one
  physical_derivative := by
    intro j x hx
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have hmap := rescaleMap_mapsTo (gridCenter_norm (by omega : 0<A) i) (by positivity : 0≤(A:ℝ)⁻¹)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx
    rw [partial_rescale_local Metric.isOpen_ball D.smooth_p _ _ x hmap j,
      abs_mul,abs_of_pos (inv_pos.mpr (by positivity : 0<(A:ℝ)))]
    calc
      _ ≤ (A:ℝ)⁻¹*(Cp*D.side) := mul_le_mul_of_nonneg_left
        (D.physical_derivative j _ hmap) (by positivity)
      _ = Cp*(D.side/(A:ℝ)) := by ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def GridChild {Cp a₀ : ℝ} (A : ℕ) (D E : ScaledWave Cp a₀) (i : GridIndex A) : Prop :=
  E.p=D.p ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹ ∧
  E.U=D.U ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹ ∧
  E.K=D.K/(A:ℝ) ∧ E.side=D.side/(A:ℝ)

def DescentRule (A : ℕ) (Cp a₀ C₀ C₁ L : ℝ) : Prop :=
  ∀ (D : ScaledWave Cp a₀) (b : Plane), a₀≤D.K/(A:ℝ) →
    (L<D.growth 0 ∨ L<‖b‖) →
    ∃(E : GridIndex A → ScaledWave Cp a₀) (b' : GridIndex A → Plane),
      (∀i,GridChild A D (E i) i) ∧
      (𝔼 i,‖b' i-b‖)≤C₁*(D.growth b+(C₀/D.K+D.side)) ∧
      (𝔼 i,(E i).growth (b' i))≤(D.growth b+(C₀/D.K+D.side))/2

end SharpNodal.Profiles
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def ScaledFloors (A C₀ K s : ℝ) : ℕ → Tree ι → Prop
  | _, .stop _ => True
  | 0, .step _ _ => False
  | n+1, .step a t => a.floor=C₀/K+s ∧ ∀i,ScaledFloors A C₀ (K/A) (s/A) n (t i)

end SharpNodal.Descent.Tree

noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace SharpNodal.Profiles

inductive WaveTree (A : ℕ) (Cp a₀ : ℝ) where
  | stop (wave : ScaledWave Cp a₀) (tilt : Plane)
  | step (wave : ScaledWave Cp a₀) (tilt : Plane) (children : GridIndex A → WaveTree A Cp a₀)

namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

def rootWave : WaveTree A Cp a₀ → ScaledWave Cp a₀
  | .stop D _ => D
  | .step D _ _ => D

def rootTilt : WaveTree A Cp a₀ → Plane
  | .stop _ b => b
  | .step _ b _ => b

def label (C₀ : ℝ) (D : ScaledWave Cp a₀) (b : Plane) : Descent.Label :=
  ⟨D.growth b,b,C₀/D.K+D.side⟩

def numerical (C₀ : ℝ) : WaveTree A Cp a₀ → Descent.Tree (GridIndex A)
  | .stop D b => .stop (label C₀ D b)
  | .step D b t => .step (label C₀ D b) (fun i => numerical C₀ (t i))

def Coherent : ℕ → WaveTree A Cp a₀ → Prop
  | _, .stop _ _ => True
  | 0, .step _ _ _ => False
  | n+1, .step D _ t => ∀i,GridChild A D (t i).rootWave i ∧ Coherent n (t i)

def Stopped (C₀ : ℝ) (P : Descent.Label → Prop) : ℕ → WaveTree A Cp a₀ → Prop
  | 0, .stop _ _ => True
  | _+1, .stop D b => ¬P (label C₀ D b)
  | 0, .step _ _ _ => False
  | n+1, .step D b t => P (label C₀ D b) ∧ ∀i,Stopped C₀ P n (t i)

end WaveTree
end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GridPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory

namespace SharpNodal.Profiles

abbrev GridWord (A n : ℕ) := Fin n → GridIndex A

def wordIndex (A : ℕ) : (n : ℕ) → GridWord A n → GridIndex (A^n)
  | 0, _ => fun _ => 0
  | n+1,w => fun j => Fin.cast (pow_succ' A n).symm
      (finProdFinEquiv (w 0 j,wordIndex A n (Fin.tail w) j))

def wordCenter (A n : ℕ) (w : GridWord A n) : Plane := gridCenter (A^n) (wordIndex A n w)

end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
namespace SharpNodal.Profiles
namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

def PathGood (C₀ : ℝ) (P : Descent.Label → Prop) :
    (n : ℕ) → WaveTree A Cp a₀ → GridWord A n → Prop
  | 0,t,_ => P (label C₀ t.rootWave t.rootTilt)
  | _+1,.stop D b,_ => P (label C₀ D b)
  | n+1,.step D b t,w => P (label C₀ D b) ∧ PathGood C₀ P n (t (w 0)) (Fin.tail w)

end WaveTree

def HighWavePath {Cp a₀ : ℝ} (A : ℕ) (L : ℝ) :
    (n : ℕ) → ScaledWave Cp a₀ → GridWord A n → Prop
  | 0,D,_ => L<D.growth 0
  | n+1,D,w => L<D.growth 0 ∧ ∃E : ScaledWave Cp a₀,
      GridChild A D E (w 0) ∧ HighWavePath A L n E (Fin.tail w)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma rescaleMap_mapsTo_margin {y : Plane} {r : ℝ} (hr : 0 < r)
    (hmargin : ‖y‖+1000*r≤1000) :
    MapsTo (rescaleMap y r) (Metric.ball 0 1000) (Metric.ball 0 1000) := by
  intro x hx
  rw [Metric.mem_ball,dist_zero_right] at hx ⊢
  calc
    ‖rescaleMap y r x‖ ≤ ‖y‖+r*‖x‖ := by
      simpa only [rescaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos hr] using norm_add_le y (r • x)
    _ < ‖y‖+r*1000 := by gcongr
    _ ≤ 1000 := by nlinarith only [hmargin]

def ScaledWave.rebase {Cp a₀ : ℝ} (D : ScaledWave Cp a₀) (y : Plane) (r : ℝ)
    (hr : 0 < r) (hr1 : r≤1) (hmargin : ‖y‖+1000*r≤1000)
    (hbottom : a₀≤D.K*r)
    (hm0 : centeredMass 0 D.U y r≠0)
    (hmt : centeredMass 0 D.U y (1000*r)≠⊤) : ScaledWave Cp a₀ where
  p := D.p ∘ rescaleMap y r
  U := D.U ∘ rescaleMap y r
  K := D.K*r
  frequency_lower := hbottom
  smooth_p := D.smooth_p.comp (smooth_rescaleMap _ _).contDiffOn (rescaleMap_mapsTo_margin hr hmargin)
  smooth_U := D.smooth_U.comp (smooth_rescaleMap _ _).contDiffOn (rescaleMap_mapsTo_margin hr hmargin)
  coefficient_bound := fun x hx =>D.coefficient_bound _ (rescaleMap_mapsTo_margin hr hmargin hx)
  derivative_bound := by
    intro j x hx
    have hmap := rescaleMap_mapsTo_margin hr hmargin hx
    rw [partial_rescale_local Metric.isOpen_ball D.smooth_p _ _ x hmap j,
      abs_mul,abs_of_pos hr]
    exact (mul_le_of_le_one_left (abs_nonneg _) hr1).trans (D.derivative_bound j _ hmap)
  equation := by
    intro x hx
    have hmap := rescaleMap_mapsTo_margin hr hmargin hx
    rw [laplacian_rescale_local Metric.isOpen_ball D.smooth_U _ _ x hmap]
    dsimp only [Function.comp_apply]
    calc
      _ = r^2*(euclideanLaplacian D.U (rescaleMap y r x)+
        D.K^2*D.p (rescaleMap y r x)*D.U (rescaleMap y r x)) := by ring
      _ = 0 := by rw [D.equation _ hmap,mul_zero]
  inner_nonzero := by
    have he := centeredMass_rescale (0:Plane) D.U y 0 hr 1
    simp only [smul_zero,rescaleMap,add_zero,mul_one] at he
    rw [he]
    exact mul_ne_zero (by simp [hr.ne']) hm0
  outer_finite := by
    have he := centeredMass_rescale (0:Plane) D.U y 0 hr 1000
    simp only [smul_zero,rescaleMap,add_zero] at he
    rw [he]
    exact ENNReal.mul_ne_top (by simp) (by simpa only [mul_comm] using hmt)
  side := D.side*r
  side_pos := mul_pos D.side_pos hr
  side_le_one := (mul_le_of_le_one_right D.side_pos.le hr1).trans D.side_le_one
  physical_derivative := by
    intro j x hx
    have hmap := rescaleMap_mapsTo_margin hr hmargin hx
    rw [partial_rescale_local Metric.isOpen_ball D.smooth_p _ _ x hmap j,abs_mul,abs_of_pos hr]
    calc
      _ ≤ r*(Cp*D.side) := mul_le_mul_of_nonneg_left (D.physical_derivative j _ hmap) hr.le
      _ = Cp*(D.side*r) := by ring

def UnitWave.scaled {Cp a₀ : ℝ} (D : UnitWave Cp a₀) : ScaledWave Cp a₀ where
  toUnitWave := D
  side := 1
  side_pos := by norm_num
  side_le_one := le_rfl
  physical_derivative := by simpa only [mul_one] using D.derivative_bound

end SharpNodal.Profiles
noncomputable section
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory

noncomputable section
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
namespace SharpNodal.Profiles

def PersistentSquare (A : ℕ) (L : ℝ) {Cp a₀ : ℝ} (D : UnitWave Cp a₀)
    (depth M : ℕ) : Prop :=
  ∃m : ℕ,2 ≤ m ∧ m≤M ∧ m≤depth ∧ ∃p : Fin 2 → ℤ,
    let r:=((A:ℝ)⁻¹)^m
    let y:=extendedGridCenter r p
    ‖y‖+2000*r<3 ∧ 1000*r<1/4 ∧ ∃E : ScaledWave Cp a₀,
      E.U=D.U ∘ rescaleMap y r ∧ E.K=D.K*r ∧ E.side=r ∧
      (3:ℝ)/4≤𝔼 w : GridWord A (depth-m),
        if HighWavePath A L (depth-m) E w then (1:ℝ) else 0

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set

namespace SharpNodal.Grid
abbrev Point := Fin 2 → ℤ

def box (a b : Point) : Finset Point := Fintype.piFinset (fun i =>Finset.Ico (a i) (b i))

@[simp] lemma mem_box {z a b : Point} : z∈box a b ↔ ∀i,a i≤z i ∧ z i<b i := by
  simp [box]

def square (s : ℕ) (p : Point) : Finset Point :=
  box (fun i =>p i*s) (fun i =>(p i+1)*s)

@[simp] lemma mem_square {s : ℕ} {p z : Point} : z∈square s p ↔ ∀i,p i*s≤z i ∧ z i<(p i+1)*s := by
  simp [square]

def neighborhood (D s : ℕ) (p : Point) : Finset Point :=
  box (fun i =>(p i-D)*s) (fun i =>(p i+1+D)*s)

@[simp] lemma mem_neighborhood {D s : ℕ} {p z : Point} :
    z∈neighborhood D s p ↔ ∀i,(p i-D)*s≤z i ∧ z i<(p i+1+D)*s := by
  simp [neighborhood]

end SharpNodal.Grid

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Cells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set

namespace SharpNodal.Grid

@[ext] structure Cell where
  level : ℕ
  pos : Point
  deriving DecidableEq

def Cell.side (A : ℕ) (Q : Cell) : ℕ := A^Q.level
def Cell.points (A : ℕ) (Q : Cell) : Finset Point := square (Q.side A) Q.pos
def Cell.near (A D : ℕ) (Q : Cell) : Finset Point := neighborhood D (Q.side A) Q.pos

end SharpNodal.Grid

namespace SharpNodal.Grid

def Cell.ancestors (A : ℕ) (F : Finset Cell) (Q : Cell) : Finset Cell :=
  F.filter (fun P =>Q.level<P.level ∧ Q.points A⊆P.points A)
def Cell.rank (A : ℕ) (F : Finset Cell) (Q : Cell) : ℕ := 1+(Q.ancestors A F).card

def Cell.largerAt (A : ℕ) (F : Finset Cell) (Q : Cell) (x : Point) : Finset Cell :=
  F.filter (fun P =>Q.level<P.level ∧ x∈P.points A)
def Cell.smallerAt (A : ℕ) (F : Finset Cell) (Q : Cell) (x : Point) : Finset Cell :=
  F.filter (fun P =>P.level<Q.level ∧ x∈P.points A)
def Cell.mismatch (A : ℕ) (F : Finset Cell) (Q : Cell) (x : Point) : ℕ :=
  (Q.ancestors A F ∆ Q.largerAt A F x).card

def totalAt (A : ℕ) (F : Finset Cell) (x : Point) : ℕ := (F.filter (fun Q =>x∈Q.points A)).card

end SharpNodal.Grid

noncomputable section
open scoped BigOperators
open Set

namespace SharpNodal.Grid

def expanded (s h : ℕ) (p : Point) : Finset Point :=
  box (fun i =>p i*s-h) (fun i =>(p i+1)*s+h)

def strip (s h : ℕ) (p : Point) (i : Fin 2) (upper : Bool) : Finset Point :=
  box (fun j =>if upper && decide (j=i) then (p j+1)*s-h else p j*s-h)
    (fun j =>if !upper && decide (j=i) then p j*s+h else (p j+1)*s+h)

def border (s h : ℕ) (p : Point) : Finset Point :=
  (Finset.univ : Finset (Fin 2 × Bool)).biUnion (fun ib =>strip s h p ib.1 ib.2)

end SharpNodal.Grid

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_WitnessPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set

namespace SharpNodal.Grid

def mismatchConstant (D : ℕ) : ℕ := (2*D+1)^2*(8*(D+1)+16*(D+1)^2)

end SharpNodal.Grid

namespace SharpNodal.Grid

def packingConstant (D c J : ℕ) : ℕ :=
  let c' :=(4*D+3)^2*c
  2*c'*(2*(2*c'*mismatchConstant D+J+1)+1)*(2*D+1)^2

end SharpNodal.Grid

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Excursions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set

namespace SharpNodal.Profiles

def fieldGrowth (U : Plane → ℝ) (K : ℝ) : ℝ :=
  massExcess (centeredMass 0 U 0 1000) (centeredMass 0 U 0 1)/K

def pathGrowth (A : ℕ) : (n : ℕ) → (Plane → ℝ) → ℝ → GridWord A n → ℝ
  | 0,U,K,_ => fieldGrowth U K
  | n+1,U,K,w =>pathGrowth A n (U ∘ rescaleMap (gridCenter A (w 0)) (A:ℝ)⁻¹)
      (K/(A:ℝ)) (Fin.tail w)

def PathHigh (A : ℕ) (L : ℝ) : (n : ℕ) → (Plane → ℝ) → ℝ → GridWord A n → Prop
  | 0,U,K,_ =>L<fieldGrowth U K
  | n+1,U,K,w =>L<fieldGrowth U K ∧ PathHigh A L n
      (U ∘ rescaleMap (gridCenter A (w 0)) (A:ℝ)⁻¹) (K/(A:ℝ)) (Fin.tail w)

def activeGrowth (A : ℕ) (L : ℝ) (n : ℕ) (U : Plane → ℝ) (K : ℝ) (w : GridWord A n) : ℝ :=
  if PathHigh A L n U K w then pathGrowth A n U K w else 0

namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

def StopsAtLow (L : ℝ) : ℕ → WaveTree A Cp a₀ → Prop
  | 0,.stop _ _ =>True
  | _+1,.stop D _ =>D.growth 0≤L
  | 0,.step _ _ _ =>False
  | n+1,.step D _ t =>L<D.growth 0 ∧ ∀i,StopsAtLow L n (t i)

end WaveTree
end SharpNodal.Profiles

namespace SharpNodal.Profiles

def excursionCostConstant (C₀ C₁ a₀ : ℝ) : ℝ :=
  2+2002*C₁+(1+2002*C₁)*(2*(C₀/a₀+1))

end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
open Set
namespace SharpNodal.Grid

def atLevel (A n : ℕ) (x : Point) : Cell := ⟨n,fun i =>x i/(A:ℤ)^n⟩

def fullTree (A : ℕ) (root : Cell) : Finset Cell :=
  (Finset.range (root.level+1)).biUnion (fun n =>(root.points A).image (atLevel A n))

def entries (A : ℕ) (F : Finset Cell) (N : Cell → ℝ) (L H : ℝ) : Finset Cell :=
  F.filter (fun Q =>H<N Q ∧ ∀P∈Q.ancestors A F,H<N P →
    ∃R∈F,Q.level<R.level ∧ R.level<P.level ∧ Q.points A⊆R.points A ∧ N R≤L)

def activeSet (A : ℕ) (F : Finset Cell) (N : Cell → ℝ) (L : ℝ) (Q : Cell) : Finset Point :=
  (Q.points A).filter (fun x =>∀R∈F,R.level≤Q.level → x∈R.points A → L<N R)

end SharpNodal.Grid

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_TerminalGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set

namespace SharpNodal.Grid
open Profiles

def wordPoint (A n : ℕ) (p : Point) (w : GridWord A n) : Point :=
  fun j =>p j*(A:ℤ)^n+(wordIndex A n w j:ℕ)

def childPos (A : ℕ) (p : Point) (i : GridIndex A) : Point := fun j =>p j*A+(i j:ℕ)

def cellScale (A : ℕ) (t : ℝ) (Q : Cell) : ℝ := t*(A:ℝ)^Q.level

def cellMap (A : ℕ) (t : ℝ) (Q : Cell) : Plane → Plane :=
  rescaleMap (extendedGridCenter (cellScale A t Q) Q.pos) (cellScale A t Q)

def gridGrowth (A : ℕ) (t : ℝ) (U : Plane → ℝ) (K : ℝ) (Q : Cell) : ℝ :=
  fieldGrowth (U ∘ cellMap A t Q) (K*cellScale A t Q)

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

def Cell.parent (A : ℕ) (Q : Cell) : Cell := ⟨Q.level+1,fun j =>Q.pos j/(A:ℤ)⟩

def cellDigit {A : ℕ} (hA : 0<A) (Q : Cell) : GridIndex A := fun j =>
  ⟨(Q.pos j%(A:ℤ)).toNat,(Int.toNat_lt' hA).mpr (Int.emod_lt_of_pos _ (by exact_mod_cast hA))⟩

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

def offsetPos (A m : ℕ) (p q : Point) : Point := fun j =>p j*(A:ℤ)^m+q j

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

def goodWordPoints (A n : ℕ) (p : Point) (P : GridWord A n → Prop) : Finset Point :=
  (Finset.univ.filter P).image (wordPoint A n p)

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

def entryBound (A : ℕ) (C₀ C₁ L a₀ H : ℝ) : ℝ :=
  (A:ℝ)^2*((1/2+1001*C₁)*(H+1001*(L+1)+C₀/a₀+1)+1001*(L+1))

end SharpNodal.Grid

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Multipliers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def newtonPotential (g : Plane → ℝ) : Plane → ℝ :=
  fun x => (2*Real.pi)⁻¹*rconv (fun y => Real.log ‖y‖) g x

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def NewtonControl (C : ℝ) : Prop := 1≤C ∧ ∀(g : Plane → ℝ),
    Smooth g → HasCompactSupport g → ∀B : ℝ,0≤B →
    (∀x,3≤‖x‖ → g x=0) → (∀x∈Metric.ball (0:Plane) 3,|g x|≤B) →
    ∀x∈Metric.ball (0:Plane) 3,
      |newtonPotential g x|≤C*B ∧ ∀i : Fin 2,|coordPartial (newtonPotential g) i x|≤C*B

def neumannTerm (q : Plane → ℝ) : ℕ → Plane → ℝ
  | 0 => fun _ =>1
  | n+1 => fun x => -newtonPotential (fun y =>q y*neumannTerm q n y) x

def multiplierApprox (q : Plane → ℝ) (n : ℕ) : Plane → ℝ :=
  fun x => 1+∑j∈Finset.range n,neumannTerm q (j+1) x

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def multiplierLimit (q : Plane → ℝ) : Plane → ℝ :=
  fun x =>1+∑'j : ℕ,neumannTerm q (j+1) x

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def multiplierCutoff : ContDiffBump (0:Plane) := ⟨5/2,11/4,by norm_num,by norm_num⟩

def positiveApprox (q : Plane → ℝ) (n : ℕ) : Plane → ℝ :=
  fun x =>1+multiplierCutoff x*(multiplierApprox q n x-1)

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ComplexDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def complexPartial (f : Plane → ℂ) (i : Fin 2) (x : Plane) : ℂ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

def barPartial (f : Plane → ℂ) (x : Plane) : ℂ :=
  (complexPartial f 0 x+Complex.I*complexPartial f 1 x)/2

abbrev CSmooth (f : Plane → ℂ) : Prop := ContDiff ℝ ∞ f

def complexGradient (f : Plane → ℝ) (x : Plane) : ℂ :=
  (coordPartial f 0 x : ℂ)-Complex.I*(coordPartial f 1 x : ℂ)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def cauchyPotential (g : Plane → ℂ) : Plane → ℂ := fun x =>
  2*complexGradient (newtonPotential (fun y =>(g y).re)) x+
  Complex.I*(2*complexGradient (newtonPotential (fun y =>(g y).im)) x)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def complexToPlane : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

def planeToComplex : Plane ≃ₗᵢ[ℝ] ℂ := complexToPlane.symm

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Similarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate

namespace SharpNodal.Profiles
open Carleman

def regularizedCoefficient (w b : Plane → ℂ) (η : ℝ) (x : Plane) : ℂ :=
  b x*conj (w x)/((Complex.normSq (w x)+η^2 : ℝ) : ℂ)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
namespace SharpNodal.Profiles
open Carleman

def similarityCutoff : ContDiffBump (0:Plane) := ⟨2,9/4,by norm_num,by norm_num⟩
def correctionCutoff : ContDiffBump (0:Plane) := ⟨3/2,7/4,by norm_num,by norm_num⟩

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_HolomorphicGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def conductivityDrift (U φ : Plane → ℝ) (x : Plane) : ℂ :=
  (-(∑i : Fin 2,coordPartial φ i x/φ x*coordPartial (fun y =>U y/φ y) i x) : ℝ)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

structure SmallPotential (C ε δ : ℝ) (q : Plane → ℝ) : Prop where
  control : NewtonControl C
  ε_nonneg : 0 ≤ ε
  δ_nonneg : 0 ≤ δ
  δ_le : δ ≤ 1/4
  small : C*ε ≤ δ
  smooth : Smooth q
  compact : HasCompactSupport q
  support : ∀x,3 ≤ ‖x‖ → q x=0
  bound : ∀x∈Metric.ball (0:Plane) 3,|q x| ≤ ε

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_NodalGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn

namespace SharpNodal.Holomorphic

def blaschke (R : ℝ) (a z : ℂ) : ℂ := (R : ℂ)*(z-a)/((R : ℂ)^2-conj a*z)

end SharpNodal.Holomorphic

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Divisors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric

namespace SharpNodal.Holomorphic

def zeroWeight (S : Finset ℂ) (m : ℂ → ℕ) (B : ℝ) (z : ℂ) : ℝ :=
  B+∑a∈S,(m a:ℝ)*‖z-a‖⁻¹

end SharpNodal.Holomorphic

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Vitali
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
namespace SharpNodal.Profiles
open Holomorphic

def weightMeasure (S : Finset ℂ) (m : ℂ → ℕ) (B : ℝ) : Measure Plane :=
  volume.withDensity (fun x=>ENNReal.ofReal (zeroWeight S m B (planeToComplex x)))

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Elliptic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def localNewton (g : Plane → ℝ) : Plane → ℝ := fun x=>(2*Real.pi)⁻¹*rconv logParametrix g x

namespace Elliptic
abbrev Kind := Option (Fin 2) × Fin 2

def jet (f : Plane → ℝ) : Kind → Plane → ℝ
  | (none,i) => coordPartial (localNewton f) i
  | (some j,i) => coordPartial (coordPartial (localNewton f) j) i

def operator (a : Kind → Plane → ℝ) (f : Plane → ℝ) : Plane → ℝ :=
  fun x=>∑α,a α x*jet f α x

def Supported (f : Plane → ℝ) : Prop := ∀x,(1/64:ℝ)≤‖x‖ → f x=0

def Good (f : Plane → ℝ) : Prop := Smooth f ∧ HasCompactSupport f ∧ Supported f

def SNorm : ℕ → (Plane → ℝ) → ℝ
  | 0,f => l2norm f
  | n+1,f => SNorm n f+∑i:Fin 2,SNorm n (coordPartial f i)

def iterate (a : Kind → Plane → ℝ) (f : Plane → ℝ) : ℕ → Plane → ℝ
  | 0 => f
  | n+1 => operator a (iterate a f n)

def wordPartial : List (Fin 2) → (Plane → ℝ) → Plane → ℝ
  | [],f => f
  | i::w,f => coordPartial (wordPartial w f) i

structure Regular (f : ℕ → Plane → ℝ) : Prop where
  smooth : ∀n,Smooth (f n)
  bound : ∀w:List (Fin 2),∃B:ℝ,0≤B ∧ ∀n x,|wordPartial w (f n) x|≤B*(1/2:ℝ)^n

def fieldJet (h : Plane → ℝ) : Kind → Plane → ℝ
  | (none,i) => coordPartial h i
  | (some j,i) => coordPartial (coordPartial h j) i

def differential (a : Kind → Plane → ℝ) (h : Plane → ℝ) : Plane → ℝ :=
  fun x=>∑α,a α x*fieldJet h α x

def solution (a : Kind → Plane → ℝ) (f : Plane → ℝ) : Plane → ℝ :=
  fun x=>∑'n,localNewton (iterate a f n) x

end Elliptic
end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory

namespace SharpNodal.Profiles
open Carleman
namespace Elliptic

def metricCutoff : ContDiffBump (0:Plane) := ⟨1/128,1/64,by norm_num,by norm_num⟩

def flatCut (A : Plane → ℝ) (t : ℝ) : Plane → ℝ :=
  fun x=>metricCutoff x*(A (t • x)-A 0)

def coeffs (b : Fin 2 → Fin 2 → Plane → ℝ) : Kind → Plane → ℝ
  | (none,j) => fun x=> -(∑i:Fin 2,coordPartial (b i j) i x)
  | (some j,i) => fun x=> -b i j x

def perturbation (b : Fin 2 → Fin 2 → Plane → ℝ) (u : Plane → ℝ) : Plane → ℝ :=
  fun x=>∑i:Fin 2,coordPartial (fun y=>∑j:Fin 2,b i j y*coordPartial u j y) i x

def oneForm (p q : Plane → ℝ) (x : Plane) : Plane →L[ℝ] ℝ :=
  p x • (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ)+q x • (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ)

def metricFlux (b : Fin 2 → Fin 2 → Plane → ℝ) (u : Plane → ℝ) (i : Fin 2) : Plane → ℝ :=
  fun x=>coordPartial u i x+∑j:Fin 2,b i j x*coordPartial u j x

def coordMap (u v : Plane → ℝ) (x : Plane) : Plane :=
  u x • EuclideanSpace.single 0 1+v x • EuclideanSpace.single 1 1

end Elliptic
end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric

noncomputable section
open scoped Matrix

noncomputable section
open scoped Topology ContDiff
open Filter Set Metric
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

def scalarDensity (a b c : Plane → ℝ) (x : Plane) : ℝ :=
  Real.sqrt (a x*c x-(b x)^2)
def scalarFlux0 (a b c U : Plane → ℝ) (x : Plane) : ℝ :=
  (c x*coordPartial U 0 x-b x*coordPartial U 1 x)/scalarDensity a b c x
def scalarFlux1 (a b c U : Plane → ℝ) (x : Plane) : ℝ :=
  (a x*coordPartial U 1 x-b x*coordPartial U 0 x)/scalarDensity a b c x
def scalarLaplace (a b c U : Plane → ℝ) (x : Plane) : ℝ :=
  (coordPartial (scalarFlux0 a b c U) 0 x+coordPartial (scalarFlux1 a b c U) 1 x)/
    scalarDensity a b c x

def transformA (a b c f g : Plane → ℝ) (x : Plane) : ℝ :=
  a (coordMap f g x)*(coordPartial f 0 x)^2+
  2*b (coordMap f g x)*coordPartial f 0 x*coordPartial g 0 x+
  c (coordMap f g x)*(coordPartial g 0 x)^2
def transformB (a b c f g : Plane → ℝ) (x : Plane) : ℝ :=
  a (coordMap f g x)*coordPartial f 0 x*coordPartial f 1 x+
  b (coordMap f g x)*(coordPartial f 0 x*coordPartial g 1 x+coordPartial f 1 x*coordPartial g 0 x)+
  c (coordMap f g x)*coordPartial g 0 x*coordPartial g 1 x
def transformC (a b c f g : Plane → ℝ) (x : Plane) : ℝ :=
  a (coordMap f g x)*(coordPartial f 1 x)^2+
  2*b (coordMap f g x)*coordPartial f 1 x*coordPartial g 1 x+
  c (coordMap f g x)*(coordPartial g 1 x)^2
def coordDet (f g : Plane → ℝ) (x : Plane) : ℝ :=
  coordPartial f 0 x*coordPartial g 1 x-coordPartial f 1 x*coordPartial g 0 x

end SharpNodal.Geometry

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_NormalizedCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

def pullMetric (f : Plane → M) (y : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j=>inner ℝ (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y (EuclideanSpace.single j 1))

def ChartSmooth (e : OpenPartialHomeomorph M Plane) : Prop :=
  ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (e : M → Plane) e.source ∧
  ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (e.symm : Plane → M) e.target

end SharpNodal.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Conductivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

def chartConductivity (e : OpenPartialHomeomorph M Plane) (i j : Fin 2) (y : Plane) : ℝ :=
  (if i=0 then (if j=0 then pullMetric (e.symm : Plane → M) y 1 1 else -pullMetric (e.symm : Plane → M) y 0 1)
    else (if j=0 then -pullMetric (e.symm : Plane → M) y 0 1 else pullMetric (e.symm : Plane → M) y 0 0)) /
    Real.sqrt (pullMetric (e.symm : Plane → M) y).det

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
def scaleChart (e : OpenPartialHomeomorph M Plane) (r : ℝ) (hr : r≠0) : OpenPartialHomeomorph M Plane :=
  e.trans (Homeomorph.smul (Units.mk0 r hr)).symm.toOpenPartialHomeomorph

end SharpNodal.Geometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Isothermal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

def IsConformal (e : OpenPartialHomeomorph M Plane) : Prop :=
  ChartSmooth e ∧ ∀y∈e.target,∃p : ℝ,0<p ∧
    pullMetric (e.symm : Plane → M) y=p • (1 : Matrix (Fin 2) (Fin 2) ℝ)

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

def chartScalarLaplace (e : OpenPartialHomeomorph M Plane) (u : M → ℝ) (y : Plane) : ℝ :=
  scalarLaplace (fun z=>pullMetric (e.symm : Plane → M) z 0 0)
    (fun z=>pullMetric (e.symm : Plane → M) z 0 1)
    (fun z=>pullMetric (e.symm : Plane → M) z 1 1) (u ∘ e.symm) y

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

def conformalFactor (e : OpenPartialHomeomorph M Plane) (y : Plane) : ℝ :=
  pullMetric (e.symm : Plane → M) y 0 0

end SharpNodal.Geometry

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_InteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

namespace SharpNodal.Profiles

variable {X : Type*}
def supMass (u : X → ℝ) (s : Set X) : ℝ≥0∞ := ⨆x∈s,ENNReal.ofReal ((u x)^2)

variable [TopologicalSpace X] [SecondCountableTopology X]

def SupLocalBound (u : ℕ → X → ℝ) (S : ℕ → ℝ) (x : X) (a : ℝ) : Prop :=
  ∃G : Set X,IsOpen G ∧ x∈G ∧ ∀ᶠj in atTop,supMass (u j) G≤ENNReal.ofReal (Real.exp (2*S j*a))

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

def plainMass (U : Plane → ℝ) (E : Set Plane) : ℝ≥0∞:=∫⁻x in E,ENNReal.ofReal (U x^2)

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Eigenfunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

structure NormalizedEigen (K : ℝ) (u : M → ℝ) : Prop where
  smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ u
  equation : ∀x,-laplaceBeltrami u x=K^2*u x
  bound : ∀x,|u x|≤1
  maximum : ∃x,|u x|=1

end SharpNodal.Geometry

end

end OAI
end


