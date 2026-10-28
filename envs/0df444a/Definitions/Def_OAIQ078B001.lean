-- Prove2me | Definitions.Def_OAIQ078B001
-- name    : OAIQ078B001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:20:58.653983+00:00
-- url     : https://prove2.me/theorems/da0f79fd-5255-48f5-ac9e-64522c31c5a7
-- title:
--   Definitions bundle OAIQ078B001 of the split of OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 547 declarations of OpenAI's Lean: 345 definitions, 11 inductive types or structures, 22 instances and 169 theorems. The definitions and types are `OAI.CriticalPercolation.ClusterColumns.hitValue`, `OAI.CriticalPercolation.ClusterColumns.jointHitValue`, `OAI.CriticalPercolation.CompactQuotient.HasSparsePolynomialWordGrowth`, `OAI.CriticalPercolation.Corridor.ScaleChoice.J`, `OAI.CriticalPercolation.Corridor.ScaleChoice.L`, `OAI.CriticalPercolation.Corridor.ScaleChoice.contour`, `OAI.CriticalPercolation.Corridor.ScaleChoice.delta`, `OAI.CriticalPercolation.Corridor.ScaleChoice.e`, `OAI.CriticalPercolation.Corridor.ScaleChoice.epsilon`, `OAI.CriticalPercolation.Corridor.ScaleChoice.eta`, `OAI.CriticalPercolation.Corridor.ScaleChoice.kappa`, `OAI.CriticalPercolation.CosetGrowth.ball`, `OAI.CriticalPercolation.DiskWinding.increment`, `OAI.CriticalPercolation.EuclideanEllipse.boundaryError`, `OAI.CriticalPercolation.EuclideanEllipse.diagonal`, `OAI.CriticalPercolation.EuclideanEllipse.diskExpand`, `OAI.CriticalPercolation.EuclideanEllipse.diskNormalize`, `OAI.CriticalPercolation.EuclideanEllipse.diskRadius`, `OAI.CriticalPercolation.EuclideanEllipse.expand`, `OAI.CriticalPercolation.EuclideanEllipse.gridPoint`, `OAI.CriticalPercolation.EuclideanEllipse.lineAngle`, `OAI.CriticalPercolation.EuclideanEllipse.normalize`, `OAI.CriticalPercolation.EuclideanEllipse.parameterDisk`, `OAI.CriticalPercolation.FiniteClusters.coefficient`, `OAI.CriticalPercolation.FiniteCyclicConstruction`, `OAI.CriticalPercolation.FiniteEntropy.binaryDivergence`, `OAI.CriticalPercolation.FiniteEntropy.binaryRemainder`, `OAI.CriticalPercolation.FiniteEntropy.divergence`, `OAI.CriticalPercolation.FiniteEntropy.endpointKernel`, `OAI.CriticalPercolation.FiniteEntropy.fiberValue`, `OAI.CriticalPercolation.FiniteMarkov.Associated`, `OAI.CriticalPercolation.FiniteMarkov.avg`, `OAI.CriticalPercolation.FiniteMarkov.compose`, `OAI.CriticalPercolation.FiniteMarkov.remainder`, `OAI.CriticalPercolation.FiniteMarkov.step`, `OAI.CriticalPercolation.FiniteProduct.closedThin`, `OAI.CriticalPercolation.FiniteProduct.exposureLaw`, `OAI.CriticalPercolation.FiniteProduct.forceClosed`, `OAI.CriticalPercolation.FiniteProduct.freeze`, `OAI.CriticalPercolation.GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient` and 316 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `BenjaminiSchramm_Cayley`, `BenjaminiSchramm_CayleyInputs`, `BenjaminiSchramm_FiniteOrbitStationary`, `BenjaminiSchramm_GhostFan`, `BenjaminiSchramm_GhostField`, `BenjaminiSchramm_PeakFiniteEnergy`, `BenjaminiSchramm_PrefixMaximumBootstrap`, `BenjaminiSchramm_ProbeEntropy`, `BenjaminiSchramm_SubcriticalLayerConvolution`, `CriticalPercolation_Clusters_HitValue`, `CriticalPercolation_Criticality_BandScale`, `CriticalPercolation_Criticality_ClassTwoRankOne`, `CriticalPercolation_Criticality_DiskWinding`, `CriticalPercolation_Criticality_IntegerBoxes`, `CriticalPercolation_Criticality_InterpolationUniform`, `CriticalPercolation_Criticality_NormalClosureGrowth`, `CriticalPercolation_Criticality_Weight`, `CriticalPercolation_Entropy_Divergence`, `CriticalPercolation_Entropy_EndpointKernel`, `CriticalPercolation_Entropy_FiberValue`, `CriticalPercolation_Entropy_FreshSet`, `CriticalPercolation_Entropy_Uniform01`, `CriticalPercolation_Exploration_ClosedFresh`, `CriticalPercolation_Exploration_IncidenceIdentity`, `CriticalPercolation_Exploration_IncidenceSearch`, `CriticalPercolation_Exploration_Score`, `CriticalPercolation_Exploration_Select`, `CriticalPercolation_Exploration_SequentialExposure`, `CriticalPercolation_Exploration_Tagged`, `CriticalPercolation_Exploration_Visits`, `CriticalPercolation_Gluing_CorridorScaleChoice`, `CriticalPercolation_Gluing_HonestChoice`, `CriticalPercolation_Gluing_RelayGeometry`, `CriticalPercolation_GraphGeometry_EllipseAngles`, `CriticalPercolation_GraphGeometry_EllipseGrid`, `CriticalPercolation_GraphGeometry_EllipseMesh`, `CriticalPercolation_GraphGeometry_EuclideanEllipse`, `CriticalPercolation_GraphGeometry_FiniteActionAverage`, `CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods`, `CriticalPercolation_GraphGeometry_GraphQuotientPolynomial`, `CriticalPercolation_GraphGeometry_Link`, `CriticalPercolation_GraphGeometry_Link2`, `CriticalPercolation_GraphTopology_GraphAutomorphismTopology`, `CriticalPercolation_GraphTopology_GraphNeighborhoodCompact`, `CriticalPercolation_GraphTopology_LocalProjectiveTopology`, `CriticalPercolation_GraphTopology_TopologicalClassificationBoundary`, `CriticalPercolation_Growth_CosetBallIndex`, `CriticalPercolation_Growth_CosetBounded`, `CriticalPercolation_Growth_CosetGeometry`, `CriticalPercolation_Growth_CosetNormalClosure`, `CriticalPercolation_Growth_CosetSparseGrowth`, `CriticalPercolation_Growth_CosetTransfer`, `CriticalPercolation_Growth_GraphRelativeGrowth`, `CriticalPercolation_Growth_HomogeneousAverage`, `CriticalPercolation_Growth_HomogeneousGeometry`, `CriticalPercolation_Growth_HomogeneousGrowth`, `CriticalPercolation_Growth_HomogeneousPolynomialSpace`, `CriticalPercolation_Growth_PolynomialGrowthDescent`, `CriticalPercolation_Growth_WordBallPacking`, `CriticalPercolation_Growth_WordLengthGeometry`, `CriticalPercolation_Harmonic_CayleyCaccioppoli`, `CriticalPercolation_Harmonic_CayleyPoincare`, `CriticalPercolation_Harmonic_FiniteHilbert`, `CriticalPercolation_Harmonic_FunctionGramMatrix`, `CriticalPercolation_Harmonic_GeneralizedGramSpectrum`, `CriticalPercolation_Harmonic_GraphHarmonicLinear`, `CriticalPercolation_Harmonic_GraphProjectedFunctions`, `CriticalPercolation_Harmonic_GraphWalkOperator`, `CriticalPercolation_Harmonic_GraphWalkProbability`, `CriticalPercolation_Harmonic_HarmonicFunctionSpace`, `CriticalPercolation_Harmonic_HarmonicLinearQuotient`, `CriticalPercolation_Harmonic_LazyWalkHilbert`, `CriticalPercolation_Harmonic_LazyWalkProbability`, `CriticalPercolation_Harmonic_PolynomialHarmonicSpace`, `CriticalPercolation_Harmonic_ProjectedWalkFunctions`, `CriticalPercolation_LinearGroups_AbsoluteMatrixSpan`, `CriticalPercolation_LinearGroups_ConjugationMatrixGrowth`, `CriticalPercolation_LinearGroups_FgMatrixRing`, `CriticalPercolation_LinearGroups_FiniteSubspaceOrbit`, `CriticalPercolation_LinearGroups_FullSpanAlternative`, `CriticalPercolation_LinearGroups_InvariantBlockSolvability`, `CriticalPercolation_LinearGroups_LocalFurstenbergBound`, `CriticalPercolation_LinearGroups_LocalProjectiveAction`, `CriticalPercolation_LinearGroups_ProjectivePeriodicity`, `CriticalPercolation_LinearGroups_ProjectivelyPeriodicSchur`, `CriticalPercolation_Modular_CappedDiscrepancy`, `CriticalPercolation_Modular_ClusterMassInfinite`, `CriticalPercolation_Modular_InputMass`, `CriticalPercolation_Modular_OrderMass`, `CriticalPercolation_Modular_WeightedIncidenceSearch`, `CriticalPercolation_Nilpotent_CharacteristicNilpotentCore`, `CriticalPercolation_Nilpotent_FiniteCyclicConstruction`, `CriticalPercolation_Nilpotent_LowerCentralFG`, `CriticalPercolation_ProductMeasure_Associated`, `CriticalPercolation_ProductMeasure_ClosedThin`, `CriticalPercolation_ProductMeasure_CompactInvariantMeasure`, `CriticalPercolation_ProductMeasure_ExposureLaw`, `CriticalPercolation_ProductMeasure_FiniteMarkovAvg`, `CriticalPercolation_ProductMeasure_ForceClosed`, `CriticalPercolation_ProductMeasure_LayerExpectation`, `CriticalPercolation_ProductMeasure_LevelContactMeasurability`, `UnimodularPercolation_Clusters_KernelMoments`, `UnimodularPercolation_Clusters_Resampling`, `UnimodularPercolation_Clusters_Uniqueness`, `UnimodularPercolation_Criticality_Operator`, `UnimodularPercolation_Criticality_Sharpness`, `UnimodularPercolation_Criticality_Susceptibility`, `UnimodularPercolation_Deformation_AveragedDecrease`, `UnimodularPercolation_Deformation_Calibration`, `UnimodularPercolation_Deformation_Corridors`, `UnimodularPercolation_Deformation_Derivatives`, `UnimodularPercolation_Escape_CollisionTails`, `UnimodularPercolation_Escape_Labels`, `UnimodularPercolation_Escape_PathSelection`, `UnimodularPercolation_Escape_PositiveEscapes`, `UnimodularPercolation_Exploration_FractionalMoments`, `UnimodularPercolation_Exploration_Goodness`, `UnimodularPercolation_Exploration_Marked`, `UnimodularPercolation_Exploration_Moments`, `UnimodularPercolation_Exploration_TailBounds`, `UnimodularPercolation_Graph_Topology`, `UnimodularPercolation_Kernel_Amplification`, `UnimodularPercolation_Kernel_Bounds`, `UnimodularPercolation_Kernel_Connections`, `UnimodularPercolation_Kernel_ContactTrace`, `UnimodularPercolation_Kernel_Covariance`, `UnimodularPercolation_Kernel_DistinctMoments`, `UnimodularPercolation_Kernel_ScaleBudget`, `UnimodularPercolation_Kernel_Spectral`, `UnimodularPercolation_Kernel_Sprinkling`, `UnimodularPercolation_Kernel_TraceBounds`, `UnimodularPercolation_ProductMeasure_Association`, `UnimodularPercolation_Splicing_EndpointMoments`, `UnimodularPercolation_Splicing_GapCodes`, `UnimodularPercolation_Splicing_ReferenceLaws`, `UnimodularPercolation_Splicing_Replay`, `UnimodularPercolation_Subdivision_Coupling`, `UnimodularPercolation_Subdivision_Operator`, `UnimodularPercolation_Transport_EndpointKernels`, `UnimodularPercolation_Transport_Haar`, `UnimodularPercolation_Transport_TrajectoryMass`, `UnimodularPercolation_TwoCluster_Score`.
--
--   **Imports.** It imports the published bundle `Def_BenjaminiSchramm`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ078B002`; the statements `OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs`, `OAI_CriticalPercolation_BondGraph_halfspace_fractional_profile_bootstrap`, `OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap_bs`, `OAI_CriticalPercolation_BondGraph_main_failure_topological_classification_counterexample`, `OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs`, `OAI_CriticalPercolation_BondGraph_normalized_crossing_exponent_approximation`, `OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs`, `OAI_CriticalPercolation_BondGraph_peak_sprinkling_eventual_survival`, `OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs`, `OAI_CriticalPercolation_BondGraph_restricted_interpolation_measure`, `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs`, `OAI_CriticalPercolation_BondGraph_subcritical_normalized_layer_rate`, `OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs`, `OAI_CriticalPercolation_BondGraph_upward_ceiling_profile`, `OAI.CriticalPercolation.BondGraph.upward_ceiling_profile_bs`, `OAI_CriticalPercolation_BondGraph_upward_fractional_slab_profile`, `OAI.CriticalPercolation.BondGraph.upward_fractional_slab_profile_bs`, `OAI_CriticalPercolation_CompactQuotient_virtuallyNilpotent_of_sparse_word_growth`, `OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs`, `OAI_CriticalPercolation_HarmonicAnalysis_WordGeometry_exists_infinite_finiteDimensional_linear_image`, `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs`, `OAI_CriticalPercolation_HomogeneousAnalysis_Geometry_finite_stabilizer_harmonic_image`, `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.finite_stabilizer_harmonic_image_bs`, `OAI_CriticalPercolation_LinearGrowth_StrongFullSpan_virtually_comm_range`, `OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs`, `OAI_CriticalPercolation_RelativeGrowth_virtually_indicable` and `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs`; the proofs of `OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs`, `OAI_CriticalPercolation_BondGraph_coordinate_pinned_corridor_failure`, `OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs`, `OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs`, `OAI_CriticalPercolation_BondGraph_ellipse_critical_contradiction`, `OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs`, `OAI_CriticalPercolation_BondGraph_original_root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.original_root_corridor_miss_bs`, `OAI_CriticalPercolation_BondGraph_unique_cluster_direction_unbounded_ae`, `OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs`, `OAI_CriticalPercolation_CompactQuotient_virtuallyNilpotent_of_sparse_word_growth`, `OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs`, `OAI_CriticalPercolation_HarmonicAnalysis_WordGeometry_exists_infinite_finiteDimensional_linear_image`, `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs`, `OAI_CriticalPercolation_LinearGrowth_StrongFullSpan_virtually_comm_range`, `OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs`, `OAI_CriticalPercolation_RelativeGrowth_virtually_indicable`, `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs`, `OAI_CriticalPercolation_nilpotent_descent` and `OAI.CriticalPercolation.nilpotent_descent_bs`.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_BenjaminiSchramm

section
-- module Solutions.OAIQ078_BS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h

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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

 
noncomputable def finiteEmbedding : (V →₀ ℂ) →ₗ[ℂ] Hilbert V :=
  Finsupp.linearCombination ℂ (fun y => lp.single 2 y (1 : ℂ))

@[simp] theorem finiteEmbedding_single (y : V) (c : ℂ) :
    finiteEmbedding (Finsupp.single y c) = lp.single 2 y c := by
  simp [finiteEmbedding, ← lp.single_smul]

end KernelLimits

section Coupling

instance labelLaw_isProbabilityMeasure :
    IsProbabilityMeasure (labelLaw : Measure (E → unitInterval)) := by
  dsimp [labelLaw]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Coupling

section KernelDomination
attribute [local instance] Classical.propDecidable

@[simp] theorem finiteEmbedding_apply (f : V →₀ ℂ) (x : V) :
    finiteEmbedding f x = f x := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    ← lp.single_smul, lp.coeFn_sum, lp.coeFn_single]
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with h
  · simp
  · exact (Finsupp.notMem_support_iff.mp h).symm

 
noncomputable def positivePart (f : Hilbert V) : Hilbert V :=
  ⟨fun x => (‖f x‖ : ℂ), (lp.memℓp f).mono' (by intro x; simp)⟩

@[simp] theorem positivePart_apply (f : Hilbert V) (x : V) :
    positivePart f x = (‖f x‖ : ℂ) := rfl

@[simp] theorem norm_positivePart (f : Hilbert V) : ‖positivePart f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp



end KernelDomination

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology

 
def FiniteWitness (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Finset E, (s : Set E) ⊆ ω ∧ (s : Set E) ∈ A

 noncomputable def edgeExhaustion [Encodable E] (n : ℕ) : Finset E :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

end WitnessAssociation

section Automorphisms
attribute [local instance] Classical.propDecidable

theorem measurable_set_preimage (b : E ≃ E) :
    Measurable (fun ω : Set E => b ⁻¹' ω) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply (b e)).comp MeasurableEquiv.setOfPred.symm.measurable))


end Automorphisms

section DisjointWitness
attribute [local instance] Classical.propDecidable

 
def DisjointOccurrence (A B : Set (Set E)) : Set (Set E) :=
  {ω | ∃ s t : Finset E, (s : Set E) ⊆ ω ∧ (t : Set E) ⊆ ω ∧
    Disjoint s t ∧ (s : Set E) ∈ A ∧ (t : Set E) ∈ B}


def openSection (A : Set (Set E)) (e : E) : Set (Set E) := {ω | insert e ω ∈ A}



noncomputable def finiteProbability (p : unitInterval) (s : Finset E) (A : Set (Set E)) : ℝ :=
  ∑ t ∈ s.powerset, if (t : Set E) ∈ A then
    (p : ℝ) ^ t.card * (1 - p : ℝ) ^ (s.card - t.card) else 0

@[simp] theorem finiteProbability_empty (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p ∅ A = if ∅ ∈ A then 1 else 0 := by
  simp [finiteProbability]

end DisjointWitness

section FiniteBK
attribute [local instance] Classical.propDecidable

@[simp] theorem empty_mem_disjointOccurrence (A B : Set (Set E)) :
    (∅ : Set E) ∈ DisjointOccurrence A B ↔ ∅ ∈ A ∧ ∅ ∈ B := by
  constructor
  · rintro ⟨s, t, hs, ht, _, ha, hb⟩
    have hse : (s : Set E) = ∅ := Set.subset_empty_iff.mp hs
    have hte : (t : Set E) = ∅ := Set.subset_empty_iff.mp ht
    exact ⟨hse ▸ ha, hte ▸ hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨∅, ∅, by simp, by simp, by simp, by simpa using ha, by simpa using hb⟩



end FiniteBK

section ORLift
attribute [local instance] Classical.propDecidable

noncomputable def orParameter (q : unitInterval) (m : ℕ) : unitInterval :=
  ⟨1 - (1 - (q : ℝ)) ^ m,
    sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr q.2.2) (by linarith [q.2.1])),
    by linarith [pow_nonneg (sub_nonneg.mpr q.2.2) m]⟩

noncomputable abbrev bitLaw (q : unitInterval) : Measure Prop :=
  unitInterval.toNNReal q • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm q) • Measure.dirac False

end ORLift

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FinitePairBound
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate

noncomputable def deltaSum (F : Finset V) : Hilbert V := ∑ x ∈ F, lp.single 2 x (1 : ℂ)

@[simp] theorem deltaSum_apply (F : Finset V) (x : V) :
    deltaSum F x = if x ∈ F then 1 else 0 := by
  simp only [deltaSum, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  simp

@[simp] theorem inner_deltaSum (F : Finset V) (f : Hilbert V) :
    inner ℂ (deltaSum F) f = ∑ x ∈ F, f x := by
  simp [deltaSum, lp.inner_single_left]

end FinitePairBound

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

noncomputable def sprinkleParameter (p a : unitInterval) : unitInterval :=
  ⟨(p : ℝ) + (1-p)*a, by
    constructor
    · exact add_nonneg p.2.1 (mul_nonneg (sub_nonneg.mpr p.2.2) a.2.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr a.2.2)]⟩

def fieldUnion (f : Bool → Set E) : Set E := f true ∪ f false

end SprinklingLaw

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 def colorInclusion (m : ℕ) : E × Fin m ↪ E × Fin (m+1) :=
  Function.Embedding.prodMap (Function.Embedding.refl E) Fin.castSuccEmb

 def baseColors (m : ℕ) : Set (E × Fin (m+1)) := Set.range (colorInclusion (E := E) m)

 def baseField (m : ℕ) (ω : Set (E × Fin (m+1))) : Set E :=
  Prod.fst '' (colorInclusion m ⁻¹' ω)

end ColoredSprinkling

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
noncomputable def bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) : ℝ :=
  ∑ t ∈ s.powerset, f t * p ^ t.card * (1-p) ^ (s.card-t.card)

@[simp] theorem bernoulliPolynomial_empty (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial ∅ f p = f ∅ := by simp [bernoulliPolynomial]

theorem bernoulliPolynomial_insert (s : Finset E) (e : E) (he : e ∉ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (insert e s) f p =
      (1-p)*bernoulliPolynomial s f p + p*bernoulliPolynomial s (fun t => f (insert e t)) p := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [bernoulliPolynomial, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card+1-t.card = (s.card-t.card)+1 := by omega
    rw [hexp, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ]
    ring


@[simp] theorem bernoulliPolynomial_zero (s : Finset E) (p : ℝ) :
    bernoulliPolynomial s (fun _ => 0) p = 0 := by simp [bernoulliPolynomial]

theorem bernoulliPolynomial_const (s : Finset E) (c p : ℝ) :
    bernoulliPolynomial s (fun _ => c) p = c := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih => rw [bernoulliPolynomial_insert s e he]; simp only [ih]; ring


noncomputable def finiteEventPolynomial (s : Finset E) (A : Set (Set E)) (p : ℝ) : ℝ :=
  bernoulliPolynomial s (fun t => if (t : Set E) ∈ A then 1 else 0) p


def closedPivotal (A : Set (Set E)) (e : E) : Set (Set E) :=
  {ω | e ∉ ω ∧ ω ∉ A ∧ insert e ω ∈ A}

end FiniteRusso

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

noncomputable def vertexExhaustion [Encodable V] (n : ℕ) : Finset V :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

end SharpnessBridge

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedExploration


inductive ProbeTree where
  | done (success : Bool)
  | edge (closed open_ : ProbeTree)
  | mark (unmarked marked : ProbeTree)

namespace ProbeTree

@[reducible] def Leaf : ProbeTree → Type
  | .done _ => Unit
  | .edge t₀ t₁ => Leaf t₀ ⊕ Leaf t₁
  | .mark t₀ t₁ => Leaf t₀ ⊕ Leaf t₁

instance leafFintype : (t : ProbeTree) → Fintype t.Leaf
  | .done _ => inferInstanceAs (Fintype Unit)
  | .edge t₀ t₁ => @instFintypeSum _ _ (leafFintype t₀) (leafFintype t₁)
  | .mark t₀ t₁ => @instFintypeSum _ _ (leafFintype t₀) (leafFintype t₁)

noncomputable def weight (p h : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 1
  | .edge t₀ _, .inl l => (1-p)*weight p h t₀ l
  | .edge _ t₁, .inr l => p*weight p h t₁ l
  | .mark t₀ _, .inl l => (1-h)*weight p h t₀ l
  | .mark _ t₁, .inr l => h*weight p h t₁ l

noncomputable def score (p : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => score p t₀ l-p
  | .edge _ t₁, .inr l => score p t₁ l+(1-p)
  | .mark t₀ _, .inl l => score p t₀ l
  | .mark _ t₁, .inr l => score p t₁ l

def queries : (t : ProbeTree) → t.Leaf → ℕ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => queries t₀ l+1
  | .edge _ t₁, .inr l => queries t₁ l+1
  | .mark t₀ _, .inl l => queries t₀ l
  | .mark _ t₁, .inr l => queries t₁ l

@[reducible] def outcome : (t : ProbeTree) → t.Leaf → Bool
  | .done b, _ => b
  | .edge t₀ _, .inl l => outcome t₀ l
  | .edge _ t₁, .inr l => outcome t₁ l
  | .mark t₀ _, .inl l => outcome t₀ l
  | .mark _ t₁, .inr l => outcome t₁ l

noncomputable def successWeight (p h : ℝ) (t : ProbeTree) (l : t.Leaf) : ℝ :=
  if outcome t l then weight p h t l else 0

noncomputable def successMass (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l

noncomputable def successScore (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * score p t l

noncomputable def successQueries (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * queries t l

noncomputable def dweight (p h : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => -weight p h t₀ l+(1-p)*dweight p h t₀ l
  | .edge _ t₁, .inr l => weight p h t₁ l+p*dweight p h t₁ l
  | .mark t₀ _, .inl l => (1-h)*dweight p h t₀ l
  | .mark _ t₁, .inr l => h*dweight p h t₁ l


inductive IsMarkSearch : ProbeTree → Prop
  | fail : IsMarkSearch (.done false)
  | edge {t₀ t₁} : IsMarkSearch t₀ → IsMarkSearch t₁ → IsMarkSearch (.edge t₀ t₁)
  | mark {t₀} : IsMarkSearch t₀ → IsMarkSearch (.mark t₀ (.done true))

def marks : (t : ProbeTree) → t.Leaf → ℕ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => marks t₀ l
  | .edge _ t₁, .inr l => marks t₁ l
  | .mark t₀ _, .inl l => marks t₀ l+1
  | .mark _ t₁, .inr l => marks t₁ l+1

noncomputable def successMarks (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * marks t l

@[simp] lemma successMass_done (p h : ℝ) (b : Bool) :
    successMass p h (.done b) = if b then 1 else 0 := by
  cases b <;> simp [successMass,successWeight,outcome,weight]

@[simp] lemma successMarks_done (p h : ℝ) (b : Bool) : successMarks p h (.done b) = 0 := by
  simp [successMarks,marks]


end ProbeTree
end MarkedExploration

section LabelledExploration
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

inductive LabelledTree (V E : Type*) where
  | done (success : Bool)
  | edge (e : E) (closed opened : LabelledTree V E)
  | mark (v : V) (unmarked marked : LabelledTree V E)

namespace LabelledTree

def forget : LabelledTree V E → ProbeTree
  | .done b => .done b
  | .edge _ t₀ t₁ => .edge t₀.forget t₁.forget
  | .mark _ t₀ t₁ => .mark t₀.forget t₁.forget

@[reducible] noncomputable def eval (ω : Finset E) (m : Finset V) : LabelledTree V E → Bool
  | .done b => b
  | .edge e t₀ t₁ => if e ∈ ω then eval ω m t₁ else eval ω m t₀
  | .mark v t₀ t₁ => if v ∈ m then eval ω m t₁ else eval ω m t₀

def Valid (Q : Finset E) (F : Finset V) : LabelledTree V E → Prop
  | .done _ => True
  | .edge e t₀ t₁ => e ∈ Q ∧ Valid (Q.erase e) F t₀ ∧ Valid (Q.erase e) F t₁
  | .mark v t₀ t₁ => v ∈ F ∧ Valid Q (F.erase v) t₀ ∧ Valid Q (F.erase v) t₁

end LabelledTree

end LabelledExploration

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace ProbeTree

def Budget (t : ProbeTree) (K d : ℕ) : Prop := ∀ l, queries t l ≤ K+d*marks t l

end ProbeTree


end GraphSearchCost

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def exteriorMarks (m : Finset V) (W : Set V) : Finset V :=
  m.filter fun x => x ∉ W

@[simp] theorem coe_exteriorMarks (m : Finset V) (W : Set V) :
    (exteriorMarks m W : Set V) = (m : Set V) ∩ Wᶜ := by
  ext x; simp [exteriorMarks]


end MarkedRecursion

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Goodness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteInverseCost
attribute [local instance] Classical.propDecidable Classical.decEq

 
def bernoulliWeight (Q ω : Finset E) (p : ℝ) : ℝ :=
  p^ω.card*(1-p)^(Q.card-ω.card)

theorem bernoulliWeight_nonneg (Q ω : Finset E) (p : unitInterval) :
    0 ≤ bernoulliWeight Q ω p := mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)


end FiniteInverseCost

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable

 
noncomputable def levelIndicator (a t : ℝ) : ℝ := if 0 ≤ t ∧ t < a then 1 else 0

end IsoperimetricEnergy

section FiniteQuadraticForms
attribute [local instance] Classical.propDecidable

@[simp] theorem finiteEmbedding_inner_left (f : V →₀ ℂ) (g : Hilbert V) :
    inner ℂ (finiteEmbedding f) g = ∑ x ∈ f.support, star (f x) * g x := by
  simp [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.inner_single_left, mul_comm]

@[simp] theorem finiteEmbedding_inner_right (f : Hilbert V) (g : V →₀ ℂ) :
    inner ℂ f (finiteEmbedding g) = ∑ x ∈ g.support, star (f x) * g x := by
  simp [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.inner_single_right, mul_comm]

@[simp] theorem finiteEmbedding_norm_sq (f : V →₀ ℂ) :
    ‖finiteEmbedding f‖^2 = ∑ x ∈ f.support, ‖f x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [finiteEmbedding_inner_left]
  simp only [map_sum, finiteEmbedding_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

end FiniteQuadraticForms

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable
local instance spectralRealOperatorScalarTower :
    IsScalarTower ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_assoc scalar first second := by
    ext vector vertex
    rfl
local instance spectralRealOperatorSMulCommClass :
    SMulCommClass ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_comm scalar first second := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (first.map_smul_of_tower scalar (second vector)).symm
local instance spectralNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
noncomputable def permuteHilbert (a : V ≃ V) : Hilbert V ≃ₗᵢ[ℂ] Hilbert V where
  toFun f := ⟨fun x => f (a.symm x), by
    apply memℓp_gen
    exact a.symm.summable_iff.mpr (lp.memℓp f |>.summable (by norm_num))⟩
  invFun f := ⟨fun x => f (a x), by
    apply memℓp_gen
    exact a.summable_iff.mpr (lp.memℓp f |>.summable (by norm_num))⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact a.symm.tsum_eq (fun x => ‖f x‖ ^ (2:ℝ≥0∞).toReal)

@[simp] theorem permuteHilbert_apply (a : V ≃ V) (f : Hilbert V) (x : V) :
    permuteHilbert a f x = f (a.symm x) := rfl

@[simp] theorem permuteHilbert_single (a : V ≃ V) (x : V) (c : ℂ) :
    permuteHilbert a (lp.single 2 x c) = lp.single 2 (a x) c := by
  ext y
  simp only [permuteHilbert_apply, lp.coeFn_single]
  simp [Pi.single_apply, eq_comm, Equiv.eq_symm_apply]

noncomputable def matrixCoeff (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) : ℂ :=
  A (lp.single 2 y (1:ℂ)) x

@[simp] theorem matrixCoeff_eq_inner (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff A x y = inner ℂ (lp.single 2 x (1:ℂ)) (A (lp.single 2 y (1:ℂ))) := by
  simp [matrixCoeff,lp.inner_single_left]

@[simp] theorem matrixCoeff_adjoint (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (star A) x y = star (matrixCoeff A y x) := by
  rw [matrixCoeff_eq_inner, matrixCoeff_eq_inner]
  change inner ℂ _ ((ContinuousLinearMap.adjoint A) _) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa only [RCLike.star_def] using
    (inner_conj_symm (A (lp.single 2 x (1:ℂ))) (lp.single 2 y (1:ℂ))).symm


section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

noncomputable def rootTrace (A : Hilbert V →L[ℂ] Hilbert V) : ℂ :=
  ∑ i, (weight i : ℂ) * matrixCoeff A (root i) (root i)

@[simp] theorem rootTrace_add (A B : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (A+B) = rootTrace root weight A + rootTrace root weight B := by
  simp [rootTrace, matrixCoeff, add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem rootTrace_smul (c : ℂ) (A : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (c • A) = c * rootTrace root weight A := by
  simp [rootTrace, matrixCoeff, smul_apply, ← Finset.mul_sum, mul_left_comm]

@[simp] theorem rootTrace_one (hw : ∑ i, weight i = 1) :
    rootTrace root weight (1 : Hilbert V →L[ℂ] Hilbert V) = 1 := by
  simpa [rootTrace, matrixCoeff, lp.coeFn_single, ← Complex.ofReal_sum] using
    congrArg (fun t : ℝ => (t : ℂ)) hw

 
def KernelInvariant (Γ : Set (V ≃ V)) (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ a ∈ Γ, ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y



def RootTransport (Γ : Set (V ≃ V)) : Prop :=
  ∀ m : V → V → ℂ,
    (∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y) →
    (∀ x, Summable (m x)) → (∀ y, Summable (fun x => m x y)) →
    (∑ i, (weight i : ℂ) * ∑' y, m (root i) y) =
    (∑ i, (weight i : ℂ) * ∑' x, m x (root i))

@[simp] theorem rootTrace_real_smul (c : ℝ) (A : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (c • A) = (c : ℂ) * rootTrace root weight A := by
  simp [rootTrace, matrixCoeff, smul_apply, Complex.real_smul,
    ← Finset.mul_sum, mul_left_comm]

end RootTrace

end InvariantOperatorTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_GapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def domainBits (Q : Finset E) (ω : Set E) : Finset E := Q.filter (· ∈ ω)

@[simp] theorem mem_domainBits (Q : Finset E) (ω : Set E) (e : E) :
    e ∈ domainBits Q ω ↔ e ∈ Q ∧ e ∈ ω := Finset.mem_filter

theorem domainBits_subset (Q : Finset E) (ω : Set E) : domainBits Q ω ⊆ Q :=
  Finset.filter_subset _ _

end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapCount
attribute [local instance] Classical.propDecidable Classical.decEq



theorem inverse_contact_weight_le (K l : ℕ) (L : ℝ) (hK : 1 ≤ K) (hl : 1 ≤ l)
    (hL : 1 ≤ L) (hgap : (l:ℝ) ≤ 1 + K*L) :
    (K:ℝ)⁻¹ ≤ min 1 (2*L/l) := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hlr : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hKr
  have hlpos : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one hlr
  apply le_min
  · exact inv_le_one_of_one_le₀ hKr
  · apply (le_div_iff₀ hlpos).mpr
    apply (inv_mul_le_iff₀ hKpos).mpr
    by_cases h1 : l = 1
    · simp only [h1,Nat.cast_one]
      nlinarith
    · have h2 : (2:ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
      nlinarith

end BridgeGapCount

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GapCode
attribute [local instance] Classical.propDecidable Classical.decEq



def decodeGapOrdinals (N : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (i,l)::rest =>
    let decoded := decodeGapOrdinals N rest
    (i, (match decoded with | [] => N+1 | (_,r)::_ => r)-l)::decoded


end GapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InverseCodeMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def gapWeight (L : ℝ) (l : ℕ) : ℝ := min 1 (2*L/l)

 
noncomputable def inverseCodeMass (M : ℕ) (L : ℝ) : ℝ :=
  1 + ∑ l ∈ Finset.Icc 1 M, gapWeight L l

 
noncomputable def gapLetterWeight (L : ℝ) (l : ℕ) : ℝ := if l = 0 then 1 else gapWeight L l

theorem gapWeight_nonneg (L : ℝ) (hL : 0 ≤ L) (l : ℕ) : 0 ≤ gapWeight L l := by
  exact le_min zero_le_one (by positivity)

theorem gapLetterWeight_nonneg (L : ℝ) (hL : 0 ≤ L) (l : ℕ) : 0 ≤ gapLetterWeight L l := by
  unfold gapLetterWeight
  split_ifs
  · exact zero_le_one
  · exact gapWeight_nonneg L hL l

theorem sum_fin_succ_eq_Icc (M : ℕ) (f : ℕ → ℝ) :
    ∑ l : Fin M, f (l.val+1) = ∑ l ∈ Finset.Icc 1 M, f l := by
  rw [Fin.sum_univ_eq_sum_range (fun l => f (l+1)) M]
  apply Finset.sum_bij (fun l _ => l+1)
  · intro l hl
    exact Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hl; omega⟩
  · intro l hl m hm h
    omega
  · intro l hl
    obtain ⟨h1,hM⟩ := Finset.mem_Icc.mp hl
    exact ⟨l-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intros
    rfl

theorem sum_gapLetterWeight (M : ℕ) (L : ℝ) :
    ∑ l : Fin (M+1), gapLetterWeight L l.val = inverseCodeMass M L := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,gapLetterWeight,Fin.val_succ,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,if_false]
  exact congrArg (1+·) (sum_fin_succ_eq_Icc M (gapWeight L))

 

theorem total_gap_code_mass (k M : ℕ) (L : ℝ) :
    ∑ c : Fin k → Fin (M+1), ∏ i : Fin k, gapLetterWeight L (c i).val =
      inverseCodeMass M L ^ k := by
  rw [← Fintype.prod_sum (fun (_ : Fin k) (l : Fin (M+1)) => gapLetterWeight L l.val)]
  simp only [sum_gapLetterWeight,Finset.prod_const,Finset.card_univ,Fintype.card_fin]


def contactInterval (K a : ℕ) : Set unitInterval :=
  {u | (a:ℝ)/K ≤ (u:ℝ) ∧ (u:ℝ) < (a+1:ℕ)/K}

end InverseCodeMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Replay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SparseGapCode
attribute [local instance] Classical.propDecidable Classical.decEq

 

def ValidSparseGapCode (k M : ℕ) (c : List (ℕ × ℕ)) : Prop :=
  c.Pairwise (fun q r => q.1 < r.1) ∧
    ∀ q ∈ c, 1 ≤ q.1 ∧ q.1 ≤ k ∧ 1 ≤ q.2 ∧ q.2 ≤ M

def sparseGapValue : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (j,l)::c, i => if i = j then l else sparseGapValue c i

theorem sparseGapValue_bound (k M : ℕ) (c : List (ℕ × ℕ))
    (h : ValidSparseGapCode k M c) (i : ℕ) : sparseGapValue c i ≤ M := by
  induction c with
  | nil => exact Nat.zero_le _
  | cons q c ih =>
    obtain ⟨j,l⟩ := q
    rw [sparseGapValue]
    split_ifs
    · exact (h.2 (j,l) (by simp)).2.2.2
    · exact ih ⟨(List.pairwise_cons.mp h.1).2,fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩


def sparseGapArray (k M : ℕ) (c : List (ℕ × ℕ)) (h : ValidSparseGapCode k M c) :
    Fin k → Fin (M+1) :=
  fun i => ⟨sparseGapValue c (i.val+1),Nat.lt_succ_of_le (sparseGapValue_bound k M c h _)⟩

end SparseGapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceMaskSupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
def maskUnion (masks : List (ℕ × Set E)) : Set E :=
  {e | ∃ q ∈ masks, e ∈ q.2}

@[simp] theorem maskUnion_nil : maskUnion ([] : List (ℕ × Set E)) = ∅ := by
  ext e
  simp [maskUnion]

@[simp] theorem maskUnion_cons (i : ℕ) (M : Set E) (ms : List (ℕ × Set E)) :
    maskUnion ((i,M)::ms) = M ∪ maskUnion ms := by
  ext e
  simp [maskUnion,or_and_right,exists_or]


end TraceMaskSupport

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev JointSpliceState (E : Type v) := Set E × (ℕ → Set E) × (ℕ → Set E)

noncomputable def jointTupleWeight (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (s : JointSpliceState E) : ℝ :=
  bernoulliWeight Q (domainBits Q s.1) p *
    (∏ i ∈ J₁, bernoulliWeight Q (domainBits Q (s.2.1 i)) p) *
    ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (s.2.2 i)) p

end JointWeight

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_ReferenceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactSelector
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def uniformRank (K : ℕ) (hK : 0 < K) (t : unitInterval) : Fin K :=
  ⟨min ⌊(K:ℝ)*(t:ℝ)⌋₊ (K-1), lt_of_le_of_lt (min_le_right ..) (by omega)⟩



noncomputable def uniformContact (K : Finset E) (hK : K.Nonempty)
    (t : unitInterval) : E :=
  ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).val



noncomputable def chooseContact [Nonempty E] (seed : ℕ → unitInterval)
    (i : ℕ) (K : Set E) : E :=
  if hf : K.Finite then if hn : K.Nonempty then
    uniformContact hf.toFinset (by simpa using hn) (seed i)
  else Classical.arbitrary E else Classical.arbitrary E

end UniformContactSelector
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]



def finiteContactSeeds (k : ℕ) (u : Fin k → unitInterval) (i : ℕ) : unitInterval :=
  if hi : 1 ≤ i ∧ i ≤ k then u ⟨i-1,by omega⟩ else 0

@[simp] theorem finiteContactSeeds_at (k : ℕ) (u : Fin k → unitInterval) (i : Fin k) :
    finiteContactSeeds k u (i.val+1) = u i := by
  have hi : 1 ≤ i.val+1 ∧ i.val+1 ≤ k := ⟨by omega,by omega⟩
  simp only [finiteContactSeeds,dite_eq_left hi,Nat.add_sub_cancel]

end SeededTraceLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def oldPathWeight (k : ℕ) (q : Set E → V → V → ℝ)
    (y : ℕ → V) (η : ℕ → Set E) : ℝ :=
  ∏ i : ↥(Finset.Icc 1 k), q (η i) (y i) (y (i.val-1))

end OldPathWeight

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

 
def oldRunConsEquiv (k : ℕ) : (Fin (k+1) → W) ≃ W × (Fin k → W) where
  toFun y := (y 0, Fin.tail y)
  invFun y := Fin.cons y.1 y.2
  left_inv := Fin.cons_self_tail
  right_inv y := by simp

 

noncomputable def oldRunWeight (K : ℕ → W → W → ℝ) : (k : ℕ) → W → (Fin k → W) → ℝ
  | 0, _, _ => 1
  | k+1, z, y => K (k+1) z (y 0) * oldRunWeight K k (y 0) (Fin.tail y)

theorem oldRunWeight_nonneg (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (k : ℕ) (z : W) (y : Fin k → W) : 0 ≤ oldRunWeight K k z y := by
  induction k generalizing z with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (hK _ _ _) (ih _ _)

theorem sum_oldRunWeight_succ [Fintype W] (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) :
    (∑ y : Fin (k+1) → W, oldRunWeight K (k+1) z y) =
      ∑ a : W, K (k+1) z a * ∑ y : Fin k → W, oldRunWeight K k a y := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun y => K (k+1) z y.1 * oldRunWeight K k y.1 y.2) (by intro y; rfl),
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

 

theorem sum_oldRunWeight_le [Fintype W] (K : ℕ → W → W → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (u : ℝ) (hu : 0 ≤ u)
    (hrow : ∀ i a, ∑ b, K i a b ≤ u) (k : ℕ) (z : W) :
    (∑ y : Fin k → W, oldRunWeight K k z y) ≤ u^k := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    rw [sum_oldRunWeight_succ]
    calc
      _ ≤ ∑ a : W, K (k+1) z a * u^k := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (ih a) (hK _ _ _)
      _ = (∑ a : W, K (k+1) z a) * u^k := (Finset.sum_mul _ _ _).symm
      _ ≤ u * u^k := mul_le_mul_of_nonneg_right (hrow _ _) (pow_nonneg hu _)
      _ = u^(k+1) := by ring



def oldRunVertices : (k : ℕ) → W → (Fin k → W) → ℕ → W
  | 0, z, _ => fun _ => z
  | k+1, z, y => fun i => if i ≤ k then oldRunVertices k (y 0) (Fin.tail y) i else z

@[simp] theorem oldRunVertices_last (k : ℕ) (z : W) (y : Fin k → W) :
    oldRunVertices k z y k = z := by
  cases k <;> simp [oldRunVertices]

end FiniteOldRun

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedCodeFiber
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem sum_comp_le_sum_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, w (f a)) ≤ ∑ b, w b := by
  rw [← Finset.sum_image hf.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun b _ _ => hw b)

 
theorem finite_sum_group_weight {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (m : A → ℝ) (w : B → ℝ) :
    (∑ a, m a * w (f a)) = ∑ b, w b * ∑ a, if f a = b then m a else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  exact mul_comm _ _



end WeightedCodeFiber
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldRunArrival
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

noncomputable def oldRunArrival (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (A : Finset W) : ℝ :=
  ∑ y : Fin k → W, if oldRunVertices k z y 0 ∈ A then oldRunWeight K k z y else 0

end OldRunArrival

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_local_of_subset (Q S : Finset E) (hQS : Q ⊆ S) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) (ω : Set E) :
    f ω = f (ω ∩ (S : Set E)) := by
  rw [hf ω,hf (ω ∩ (S : Set E))]
  congr 1
  exact (Set.inter_assoc _ _ _).trans (congrArg (ω ∩ ·) (Set.inter_eq_right.mpr hQS)) |>.symm

end CappedGoodLocality

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedLocalLoad
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_prop_local_of_subset (Q S : Finset E) (hQS : Q ⊆ S) (P : Set E → Prop)
    (hf : ∀ ω, P ω ↔ P (ω ∩ (Q : Set E))) (ω : Set E) :
    P ω ↔ P (ω ∩ (S : Set E)) := by
  have he : (ω ∩ (S : Set E)) ∩ (Q : Set E) = ω ∩ (Q : Set E) :=
    (Set.inter_assoc _ _ _).trans (congrArg (ω ∩ ·) (Set.inter_eq_right.mpr hQS))
  exact (hf ω).trans ((he ▸ hf (ω ∩ (S : Set E))).symm)



end CappedLocalLoad

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CategoricalAmplificationInput
attribute [local instance] Classical.propDecidable Classical.decEq

 

def amplificationVertices (B : Finset V) (k : ℕ) (z : ↥B) (r : Fin k → ↥B) : ℕ → V :=
  fun i => (oldRunVertices k z r i).val

end CategoricalAmplificationInput

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 
def PositiveRealMatrix (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (matrixCoeff A x y).im = 0 ∧ 0 ≤ (matrixCoeff A x y).re

end PositivePathOperator

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MarkedOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}



noncomputable def markedOldRun (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, oldRunWeight (fun j a b => if j = i then C j a b else K j a b) k z r

end MarkedOldRun

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointHit
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def allAmplificationVertices (B : Finset V) (k : ℕ)
    (r : ↥B × (Fin k → ↥B)) (_η : ℕ → Set E) : ℕ → V :=
  amplificationVertices B k r.1 r.2

end AllEndpointHit

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteFieldCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finset_aut_eq_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') : Q' = Q.map b.toEmbedding := by
  ext e
  simpa only [Finset.mem_map_equiv,b.apply_symm_apply] using (hQ (b.symm e)).symm

end FiniteFieldCovariance

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceInput
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRunVertices_map {W W' : Type*} (f : W → W') (k : ℕ) (z : W)
    (r : Fin k → W) (i : ℕ) :
    oldRunVertices k (f z) (fun j => f (r j)) i = f (oldRunVertices k z r i) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunVertices]
    split_ifs with hi
    · exact ih (r 0) (Fin.tail r)
    · rfl

theorem oldRunWeight_map {W W' : Type*} (f : W → W')
    (K : ℕ → W → W → ℝ) (K' : ℕ → W' → W' → ℝ)
    (hK : ∀ i a b, K' i (f a) (f b) = K i a b) (k : ℕ) (z : W) (r : Fin k → W) :
    oldRunWeight K' k (f z) (fun i => f (r i)) = oldRunWeight K k z r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunWeight,hK]
    rw [show Fin.tail (fun i => f (r i)) = (fun i => f (Fin.tail r i)) from rfl,ih]

def finiteVertexEquiv (a : V ≃ V) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B') : ↥B ≃ ↥B' :=
  a.subtypeEquiv hB

def finiteRunEquiv (a : V ≃ V) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B') (k : ℕ) :
    (Fin k → ↥B) ≃ (Fin k → ↥B') :=
  Equiv.piCongrRight fun _ => finiteVertexEquiv a B B' hB

theorem amplificationVertices_aut_map (a : V ≃ V) (B B' : Finset V)
    (hB : ∀ x, x ∈ B ↔ a x ∈ B') (k : ℕ) (z : ↥B) (r : Fin k → ↥B) (i : ℕ) :
    amplificationVertices B' k (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) i =
      a (amplificationVertices B k z r i) :=
  congrArg Subtype.val (oldRunVertices_map (finiteVertexEquiv a B B' hB) k z r i)

end AmplificationCovarianceInput

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FinitePathExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finitePathTest (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (k : ℕ) (z : ↥B) : ℝ :=
  ∑ r : Fin k → ↥B, oldRunWeight (fun _ a b => K a.val b.val) k z r * F (oldRunVertices k z r 0).val

@[simp] theorem finitePathTest_zero (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (z : ↥B) :
    finitePathTest B K F 0 z = F z.val := by
  simp [finitePathTest,oldRunWeight,oldRunVertices]

end FinitePathExhaustion

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def amplificationMomentFactor (k M d : ℕ) (c a t : ℝ) : ℝ :=
  4 + (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) + (2*c*(k*M:ℕ))^2*t/a

end QuantitativeAmplificationMoment
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section LogarithmicChainLength

noncomputable def logarithmicChainLength (t : ℝ) (n : ℕ) : ℕ := ⌊Real.log n / t⌋₊

end LogarithmicChainLength
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationContraction

noncomputable def amplificationContraction (β s ξ : ℝ) : ℝ :=
  (β+ξ+(s+ξ)*(1+ξ))/(1-ξ)

end AmplificationContraction

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Resampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedConnectionLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def restrictedBondExhaustion [Encodable E] (S : Set E) (K : Finset E)
    (n : ℕ) : Finset E := K ∪ (vertexExhaustion (V := E) n).filter (· ∈ S)

end RestrictedConnectionLimit
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteClassTransport
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteClassTransport (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (x y : V) : ℝ :=
  if y ∈ S x then t x / (S x).card * ∑ z ∈ S x, K x z else 0

end FiniteClassTransport
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePotentialIteration
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realAction (A : Hilbert V →L[ℂ] Hilbert V) (f : V → ℝ) (x : V) : ℝ :=
  ∑' y, (matrixCoeff A x y).re*f y

end PositivePotentialIteration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory Function
section PivotalSprinklingGain
attribute [local instance] Classical.propDecidable Classical.decEq

def singleSprinkle (Q : Finset E) (e : (Q : Set E)) : Set (Set E) :=
  {η | Subtype.val ⁻¹' η = {e}}

end PivotalSprinklingGain
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section VanishingSprinkles
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def vanishingSprinkle (n : ℕ) : unitInterval :=
  ⟨1/((n:ℝ)+1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
  ⟩

end VanishingSprinkles
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_FractionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section DyadicGhostParameters
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def dyadicGhost (j : ℕ) : unitInterval :=
  ⟨(1/2:ℝ)^j,⟨pow_nonneg (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩⟩

end DyadicGhostParameters
end Percolation


namespace Percolation
universe u v
variable {E : Type v}
section DecisionCovarianceAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteCovariance (Q : Finset E) (p : ℝ) (f g : Finset E → ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => f ω*g ω) p - bernoulliPolynomial Q f p*bernoulliPolynomial Q g p

noncomputable def coordinateAverage (e : E) (p : ℝ) (f : Finset E → ℝ) (ω : Finset E) : ℝ :=
  (1-p)*f ω+p*f (insert e ω)

noncomputable def coordinateVariation (Q : Finset E) (p : ℝ) (f : Finset E → ℝ) (e : E) : ℝ :=
  bernoulliPolynomial (Q.erase e) (fun ω => |f (insert e ω)-f ω|) p

end DecisionCovarianceAlgebra
end Percolation


namespace Percolation
universe v
variable {E : Type v}
section EdgeDecisionTrees
attribute [local instance] Classical.propDecidable Classical.decEq

 
inductive EdgeQueryTree (E : Type v) where
  | done (b : Bool)
  | query (e : E) (closed opened : EdgeQueryTree E)

namespace EdgeQueryTree

def Valid (Q : Finset E) : EdgeQueryTree E → Prop
  | .done _ => True
  | .query e t₀ t₁ => e ∈ Q ∧ Valid (Q.erase e) t₀ ∧ Valid (Q.erase e) t₁

noncomputable def eval (ω : Finset E) : EdgeQueryTree E → Bool
  | .done b => b
  | .query e t₀ t₁ => if e ∈ ω then eval ω t₁ else eval ω t₀

noncomputable def value (t : EdgeQueryTree E) (ω : Finset E) : ℝ := if t.eval ω then 1 else 0

noncomputable def reads (ω : Finset E) (i : E) : EdgeQueryTree E → Prop
  | .done _ => False
  | .query e t₀ t₁ => i = e ∨ if e ∈ ω then reads ω i t₁ else reads ω i t₀

noncomputable def revealment (p : ℝ) (i : E) : EdgeQueryTree E → ℝ
  | .done _ => 0
  | .query e t₀ t₁ => if i = e then 1 else (1-p)*revealment p i t₀+p*revealment p i t₁

end EdgeQueryTree
end EdgeDecisionTrees
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe v
variable {E : Type v}
section QueryTranscriptLaw
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

@[reducible] def forget : EdgeQueryTree E → ProbeTree
  | .done b => .done b
  | .query _ t₀ t₁ => .edge t₀.forget t₁.forget

noncomputable def leaf (ω : Finset E) : (t : EdgeQueryTree E) → t.forget.Leaf
  | .done _ => ()
  | .query e t₀ t₁ => if e ∈ ω then Sum.inr (t₁.leaf ω) else Sum.inl (t₀.leaf ω)

noncomputable def score (p : ℝ) (t : EdgeQueryTree E) (ω : Finset E) : ℝ :=
  ProbeTree.score p t.forget (t.leaf ω)

noncomputable def queryCount (t : EdgeQueryTree E) (ω : Finset E) : ℕ :=
  ProbeTree.queries t.forget (t.leaf ω)


end EdgeQueryTree
end QueryTranscriptLaw
end Percolation


namespace Percolation
universe v
variable {E : Type v}
section QueryScoreSets
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

noncomputable def readSet (t : EdgeQueryTree E) (Q ω : Finset E) : Finset E :=
  Q.filter (fun e => t.reads ω e)

@[simp] theorem mem_readSet (t : EdgeQueryTree E) (Q ω : Finset E) (e : E) :
    e ∈ t.readSet Q ω ↔ e ∈ Q ∧ t.reads ω e := Finset.mem_filter

end EdgeQueryTree
end QueryScoreSets
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ContactTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def ennMatrixCoeff (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixCoeff A x y).re

end NonnegativeOperatorDiagram
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
section IntegratingFactor

noncomputable def traceIntegratingFactor (q C A t : ℝ) : ℝ :=
  Real.exp (C/(1-A)*(q-t)^(1-A))

end IntegratingFactor
end Percolation


namespace Percolation
universe u
section ChronologicalErasure
open List
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq

 

inductive HoldingWalk (H : SimpleGraph V) : ℕ → V → V → Type u
  | nil (x : V) : HoldingWalk H 0 x x
  | hold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : HoldingWalk H (k+1) x y
  | step {k : ℕ} {x z y : V} (h : H.Adj x z) (w : HoldingWalk H k z y) :
      HoldingWalk H (k+1) x y

namespace HoldingWalk
variable {H : SimpleGraph V} {k : ℕ} {x y : V}

def withoutHolds : {k : ℕ} → {x y : V} → HoldingWalk H k x y → H.Walk x y
  | _,_,_,.nil _ => .nil
  | _,_,_,.hold w => w.withoutHolds
  | _,_,_,.step h w => .cons h w.withoutHolds

def vertices : {k : ℕ} → {x y : V} → HoldingWalk H k x y → List V
  | _,x,_,.nil _ => [x]
  | _,x,_,.hold w => x :: w.vertices
  | _,x,_,.step _ w => x :: w.vertices

noncomputable def mass (P : V → V → ℝ) : {k : ℕ} → {x y : V} → HoldingWalk H k x y → ℝ
  | _,_,_,.nil _ => 1
  | _,x,_,.hold w => P x x * w.mass P
  | _,x,_,.step (z := z) _ w => P x z * w.mass P



noncomputable def erase (w : HoldingWalk H k x y) : H.Walk x y :=
  w.withoutHolds.reverse.bypass.reverse

end HoldingWalk
end ChronologicalErasure
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralCorridors
attribute [local instance] Classical.propDecidable Classical.decEq

instance HoldingWalk.countable [Countable V] (H : SimpleGraph V) (k : ℕ) (x y : V) :
    Countable (HoldingWalk H k x y) := by
  induction k generalizing x y with
  | zero =>
    apply Function.Injective.countable (f := fun _ : HoldingWalk H 0 x y => ())
    intro a b _
    cases a
    cases b
    rfl
  | succ k ih =>
    let (a b : V) : Countable (HoldingWalk H k a b) := ih a b
    let f : HoldingWalk H (k+1) x y →
        HoldingWalk H k x y ⊕ (Σ z : {z // H.Adj x z}, HoldingWalk H k z.val y)
      | .hold w => .inl w
      | .step (z := z) h w => .inr ⟨⟨z,h⟩,w⟩
    apply Function.Injective.countable (f := f)
    intro a b hab
    cases a with
    | hold a =>
      cases b with
      | hold b => exact congrArg HoldingWalk.hold (Sum.inl.inj hab)
      | step h b => cases hab
    | @step _ _ z _ h a =>
      cases b with
      | hold b => cases hab
      | @step _ _ z' _ h' b =>
        have he := Sum.inr.inj hab
        have hz := congrArg (fun t => t.1.val) he
        change z = z' at hz
        subst z'
        have hab' : a = b := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
        subst b
        rfl


end LiteralCorridors
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Corridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

def edgePattern (A B : Finset E) : Set (Set E) :=
  {ω | (A : Set E) ⊆ ω ∧ Disjoint (B : Set E) ω}

end ExactCorridorPattern
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev RawFrom (H : SimpleGraph V) (k : ℕ) (x : V) := Σ y : V, HoldingWalk H k x y

namespace RawFrom
variable {H : SimpleGraph V}

def zeroEquiv (x : V) : RawFrom H 0 x ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨x,.nil x⟩
  left_inv w := by rcases w with ⟨y,w⟩; cases w; rfl
  right_inv _ := rfl

def succEquiv (k : ℕ) (x : V) : RawFrom H (k+1) x ≃
    RawFrom H k x ⊕ (Σ z : H.neighborSet x, RawFrom H k z.val) where
  toFun
    | ⟨y,.hold w⟩ => .inl ⟨y,w⟩
    | ⟨y,.step (z := z) h w⟩ => .inr ⟨⟨z,h⟩,y,w⟩
  invFun
    | .inl ⟨y,w⟩ => ⟨y,.hold w⟩
    | .inr ⟨⟨z,h⟩,y,w⟩ => ⟨y,.step h w⟩
  left_inv w := by rcases w with ⟨y,w⟩; cases w <;> rfl
  right_inv w := by rcases w with ⟨y,w⟩ | ⟨⟨z,h⟩,y,w⟩ <;> rfl

instance finite [∀ x, Finite (H.neighborSet x)] (k : ℕ) (x : V) : Finite (RawFrom H k x) := by
  induction k generalizing x with
  | zero => exact Finite.of_equiv Unit (zeroEquiv x).symm
  | succ k ih =>
    let (z : V) : Finite (RawFrom H k z) := ih z
    exact Finite.of_equiv _ (succEquiv k x).symm

noncomputable def integral (P : V → V → ℝ) (k : ℕ) (x : V) (f : V → ℝ) : ℝ :=
  ∑' w : RawFrom H k x, w.2.mass P * f w.1

end RawFrom

end RawPathIntegration
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decision-tree scores and influences for two-cluster events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def cappedDensity (n s : ℕ) : ℝ := min (n:ℝ) s / s

end Percolation

 

 

open MeasureTheory ProbabilityTheory

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def rawWeightBase (r q : ℝ) (d : ℕ) : ℝ := r⁻¹ * (q⁻¹)^d

end UniformRawWeight
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u u' v
section ErasureNaturality
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {H : SimpleGraph V} {H' : SimpleGraph V'}

namespace HoldingWalk

def map (f : H →g H') : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H' k (f x) (f y)
  | _,_,_,.nil _ => .nil _
  | _,_,_,.hold w => .hold (w.map f)
  | _,_,_,.step h w => .step (f.map_rel h) (w.map f)

end HoldingWalk
end ErasureNaturality
end Percolation

 
namespace Percolation
universe u u' u'' v
section RawWalkMaps
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {V'' : Type u''}
  {H : SimpleGraph V} {H' : SimpleGraph V'} {H'' : SimpleGraph V''}
namespace HoldingWalk

theorem map_map (f : H →g H') (g : H' →g H'')
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).map g = w.map (g.comp f) := by
  induction w with
  | nil => rfl
  | hold w ih => exact congrArg hold ih
  | step h w ih => exact congrArg (step _) ih

theorem map_id {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.map ((SimpleGraph.Hom.id : H →g H)) = w := by
  induction w with
  | nil => rfl
  | hold w ih => exact congrArg hold ih
  | step h w ih => exact congrArg (step _) ih

end HoldingWalk

def rawWalkMap (f : H →g H') (k : ℕ) (w : Σ x y, HoldingWalk H k x y) :
    Σ x y, HoldingWalk H' k x y := ⟨f w.1,f w.2.1,w.2.2.map f⟩

theorem rawWalkMap_comp (f : H →g H') (g : H' →g H'') (k : ℕ)
    (w : Σ x y, HoldingWalk H k x y) : rawWalkMap g k (rawWalkMap f k w) = rawWalkMap (g.comp f) k w := by
  cases w with
  | mk x w =>
    cases w with
    | mk y w =>
      simp only [rawWalkMap,HoldingWalk.map_map]
      rfl

theorem rawWalkMap_id (k : ℕ) (w : Σ x y, HoldingWalk H k x y) :
    rawWalkMap ((SimpleGraph.Hom.id : H →g H)) k w = w := by
  cases w with
  | mk x w =>
    cases w with
    | mk y w =>
      simp only [rawWalkMap,HoldingWalk.map_id]
      rfl

def rawWalkEquiv (f : H ≃g H') (k : ℕ) :
    (Σ x y, HoldingWalk H k x y) ≃ (Σ x y, HoldingWalk H' k x y) where
  toFun := rawWalkMap f.toHom k
  invFun := rawWalkMap f.symm.toHom k
  left_inv w := by
    rw [rawWalkMap_comp]
    have he : f.symm.toHom.comp f.toHom = (SimpleGraph.Hom.id : H →g H) := by
      ext x
      exact f.symm_apply_apply x
    rw [he,rawWalkMap_id]
  right_inv w := by
    rw [rawWalkMap_comp]
    have he : f.toHom.comp f.symm.toHom = (SimpleGraph.Hom.id : H' →g H') := by
      ext x
      exact f.apply_symm_apply x
    rw [he,rawWalkMap_id]

end RawWalkMaps
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_AveragedDecrease
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

def segmentAut (a : V ≃ V) : (I → V) ≃ (I → V) where
  toFun s := a ∘ s
  invFun s := a.symm ∘ s
  left_inv s := by funext i; exact a.symm_apply_apply (s i)
  right_inv s := by funext i; exact a.apply_symm_apply (s i)

end AnchoredPositionKernels
end Percolation


namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}

 
def snocHold : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H (k+1) x y
  | _,_,_,.nil x => .hold (.nil x)
  | _,_,_,.hold w => .hold (snocHold w)
  | _,_,_,.step h w => .step h (snocHold w)

 
def snocStep : {k : ℕ} → {x y z : V} → HoldingWalk H k x y → H.Adj y z → HoldingWalk H (k+1) x z
  | _,_,_,z,.nil _,h => .step h (.nil z)
  | _,_,_,_,.hold w,h => .hold (snocStep w h)
  | _,_,_,_,.step h' w,h => .step h' (snocStep w h)

 

def reverse : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H k y x
  | _,_,_,.nil x => .nil x
  | _,_,_,.hold w => snocHold (reverse w)
  | _,_,_,.step h w => snocStep (reverse w) h.symm

theorem reverse_snocHold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.reverse = w.reverse.hold := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocHold,reverse,ih]
  | step h w ih => simp only [snocHold,reverse,ih,snocStep]

theorem reverse_snocStep {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).reverse = .step h.symm w.reverse := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocStep,reverse,ih,snocHold]
  | step h' w ih => simp only [snocStep,reverse,ih]

theorem reverse_reverse {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.reverse = w := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,reverse_snocHold,ih]
  | step h w ih => simp only [reverse,reverse_snocStep,ih]

end HoldingWalk
end RawReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def append : {k l : ℕ} → {x y z : V} → HoldingWalk H k x y → HoldingWalk H l y z → HoldingWalk H (l+k) x z
  | _,_,_,_,_,.nil _,v => v
  | _,_,_,_,_,.hold w,v => .hold (w.append v)
  | _,_,_,_,_,.step h w,v => .step h (w.append v)

end HoldingWalk
end Percolation


namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def position : {k : ℕ} → {x y : V} → HoldingWalk H k x y → ℕ → V
  | _,x,_,.nil _,_ => x
  | _,x,_,.hold _,0 => x
  | _,_,_,.hold w,n+1 => w.position n
  | _,x,_,.step _ _,0 => x
  | _,_,_,.step _ w,n+1 => w.position n

@[simp] theorem position_zero {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.position 0 = x := by
  cases w <;> rfl

@[simp] theorem position_length {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.position k = y := by
  induction w with
  | nil => rfl
  | hold w ih => exact ih
  | step h w ih => exact ih

end HoldingWalk
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_CollisionTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def fromPositions : (k : ℕ) → (f : Fin (k+1) → V) →
    (∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) →
    HoldingWalk H k (f 0) (f (Fin.last k))
  | 0,f,_ => .nil (f 0)
  | k+1,f,h => .step (h 0) (fromPositions k (fun i => f i.succ) (fun i => h i.succ))

end HoldingWalk
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

def segmentCenter (J : ℕ) : Fin (J+J+1) := ⟨J,by omega⟩

def segmentPositivePositions (J : ℕ) (s : Fin (J+J+1) → V) : Fin (J+1) → V :=
  fun i => s ⟨J+i.val,by omega⟩

def positiveStem (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) :
    HoldingWalk H J (s (segmentCenter J)) (s (Fin.last (J+J))) :=
  HoldingWalk.fromPositions J (segmentPositivePositions J s) (fun i => hs ⟨J+i.val,by omega⟩)

end IntrinsicVisibleBlocks
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_PositiveEscapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
section QuantitativeEarlyCutoff

 

noncomputable def earlyCollisionCost (ρ : ℝ) (J : ℕ) : ℝ :=
  2*((J:ℝ)+1)*ρ^J/(1-ρ) + 2*ρ^J/(1-ρ)^2

end QuantitativeEarlyCutoff
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]



noncomputable def suffixCollisionCost (ρ c : ℝ) (J : ℕ) : ℝ :=
  ((J:ℝ)+1)^2*Real.sqrt c + ((J:ℝ)+1)*Real.sqrt c/(1-ρ)



end CombinedRawAvoidance
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_PathSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


def negativeStem (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) :
    HoldingWalk H J (s (segmentCenter J)) (s 0) :=
  (HoldingWalk.fromPositions J (fun i => s ⟨i.val,by omega⟩)
    (fun i => hs ⟨i.val,by omega⟩)).reverse

def segmentPositiveIndex (J : ℕ) : Fin (J+1) → Fin (J+J+1) :=
  fun i => ⟨J+i.val,by omega⟩
def segmentNegativeIndex (J : ℕ) : Fin (J+1) → Fin (J+J+1) :=
  fun i => ⟨i.val,by omega⟩

end EscapeGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise topology on permutation groups. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
namespace PointwisePerm
open Topology Set
universe u
variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

 
def coordinates (g : Equiv.Perm X) : (X → X) × (X → X) := (g, g.symm)

instance topology : TopologicalSpace (Equiv.Perm X) :=
  TopologicalSpace.induced coordinates inferInstance

omit [DiscreteTopology X] in
theorem isEmbedding_coordinates : Topology.IsEmbedding (coordinates (X := X)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  intro g h he
  exact Equiv.ext (congrFun (congrArg Prod.fst he))

omit [DiscreteTopology X] in
theorem continuous_apply (x : X) : Continuous (fun g : Equiv.Perm X => g x) :=
  (_root_.continuous_apply x).comp (continuous_fst.comp isEmbedding_coordinates.continuous)

omit [DiscreteTopology X] in
theorem continuous_symm_apply (x : X) : Continuous (fun g : Equiv.Perm X => g.symm x) :=
  (_root_.continuous_apply x).comp (continuous_snd.comp isEmbedding_coordinates.continuous)

theorem continuous_eval : Continuous (fun p : (X → X) × X => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => _root_.continuous_apply x

instance topologicalGroup : IsTopologicalGroup (Equiv.Perm X) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact (continuous_eval (X := X)).comp
        ((continuous_fst.comp (isEmbedding_coordinates.continuous.comp continuous_fst)).prodMk
          ((continuous_apply x).comp continuous_snd))
    · apply continuous_pi
      intro x
      exact (continuous_eval (X := X)).comp
        ((continuous_snd.comp (isEmbedding_coordinates.continuous.comp continuous_snd)).prodMk
          ((continuous_symm_apply x).comp continuous_fst))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    exact (continuous_snd.comp isEmbedding_coordinates.continuous).prodMk
      (continuous_fst.comp isEmbedding_coordinates.continuous)

instance hausdorff : T2Space (Equiv.Perm X) :=
  isEmbedding_coordinates.t2Space

instance secondCountable [Countable X] : SecondCountableTopology (Equiv.Perm X) :=
  isEmbedding_coordinates.secondCountableTopology



omit [TopologicalSpace X] [DiscreteTopology X] in
theorem range_coordinates : Set.range (coordinates (X := X)) =
    {p | (∀ x, p.1 (p.2 x) = x) ∧ (∀ x, p.2 (p.1 x) = x)} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.apply_symm_apply, g.symm_apply_apply⟩
  · rintro ⟨hfg,hgf⟩
    exact ⟨⟨p.1,p.2,hgf,hfg⟩,rfl⟩

theorem isClosed_range_coordinates : IsClosed (Set.range (coordinates (X := X))) := by
  rw [range_coordinates]
  have hf (x : X) : IsClosed {p : (X → X) × (X → X) | p.1 (p.2 x) = x} :=
    isClosed_eq
      ((continuous_eval (X := X)).comp (continuous_fst.prodMk ((_root_.continuous_apply x).comp continuous_snd)))
      continuous_const
  have hg (x : X) : IsClosed {p : (X → X) × (X → X) | p.2 (p.1 x) = x} :=
    isClosed_eq
      ((continuous_eval (X := X)).comp (continuous_snd.prodMk ((_root_.continuous_apply x).comp continuous_fst)))
      continuous_const
  convert (isClosed_iInter hf).inter (isClosed_iInter hg) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

 

theorem isCompact_of_finite_images (S : Set (Equiv.Perm X)) (hS : IsClosed S)
    (hf : ∀ x, ((fun g : Equiv.Perm X => g x) '' S).Finite)
    (hg : ∀ x, ((fun g : Equiv.Perm X => g.symm x) '' S).Finite) :
    IsCompact S := by
  have he : Topology.IsClosedEmbedding (coordinates (X := X)) :=
    ⟨isEmbedding_coordinates, isClosed_range_coordinates⟩
  apply he.isEmbedding.isCompact_iff.mpr
  apply ((isCompact_pi_infinite fun x => (hf x).isCompact).prod
    (isCompact_pi_infinite fun x => (hg x).isCompact)).of_isClosed_subset
      (he.isClosedMap S hS)
  rintro _ ⟨g,hgS,rfl⟩
  exact ⟨fun x => ⟨g,hgS,rfl⟩, fun x => ⟨g,hgS,rfl⟩⟩

theorem isClosed_fixed (x y : X) : IsClosed {g : Equiv.Perm X | g x = y} :=
  isClosed_eq (continuous_apply x) continuous_const

end PointwisePerm
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_Haar
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar-measure transport for graph automorphism actions. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory
open scoped ENNReal
universe u v w



section HaarAction
attribute [local instance] Classical.propDecidable Classical.decEq
variable {H : Type w} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
variable {V : Type u} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable [MulAction H V]

 
def actionStabilizer (x : V) : Set H := {g | g • x = x}

 
def actionOrbit (x : V) : Set V := {y | ∃ g : H, g • x = y}

variable {ι : Type*} [Fintype ι]

 

noncomputable def inverseStabilizerWeight (μ : Measure H) (root : ι → V) (i : ι) : ℝ :=
  (μ.real (actionStabilizer (H := H) (root i)))⁻¹ /
    ∑ j, (μ.real (actionStabilizer (H := H) (root j)))⁻¹

end HaarAction
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical boundedness of the percolation operator under unimodularity and simple edge indexing. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology

 
noncomputable def criticalApproach (q : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ)),by
    have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hq := q.2
    have hp := Real.exp_pos (-(n:ℝ))
    constructor <;> nlinarith only [he,hq.1,hq.2,hp]⟩

universe u v

end Percolation





end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Subdivision_Coupling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupling percolation on a graph with percolation on its subdivision. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
open scoped ENNReal

def seriesOpen (ν : Set (E × Bool)) : Set E := {e | ∀ b, (e,b) ∈ ν}


noncomputable def squareParameter : unitInterval ≃o unitInterval where
  toFun q := q^2
  invFun p := ⟨Real.sqrt p,Real.sqrt_nonneg _,Real.sqrt_le_one.mpr p.2.2⟩
  left_inv q := by
    apply Subtype.ext
    change Real.sqrt ((q:ℝ)^2) = (q:ℝ)
    exact Real.sqrt_sq q.2.1
  right_inv p := by
    apply Subtype.ext
    change Real.sqrt (p:ℝ)^2 = (p:ℝ)
    exact Real.sq_sqrt p.2.1
  map_rel_iff' := by
    intro p q
    change (p:ℝ)^2 ≤ (q:ℝ)^2 ↔ (p:ℝ) ≤ (q:ℝ)
    exact sq_le_sq₀ p.2.1 q.2.1



end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Subdivision_Operator
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Operator bounds transferred through graph subdivision. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal

theorem sum_inl_extend_le (f : Hilbert V) (s : Finset (V ⊕ E)) :
    ∑ z ∈ s, ‖Sum.elim (fun x => f x) (fun _ : E => (0:ℂ)) z‖ ^ (2:ℝ≥0∞).toReal ≤
      ‖f‖ ^ (2:ℝ≥0∞).toReal := by
  classical
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  simp only [Sum.elim_inl,Sum.elim_inr,norm_zero,ENNReal.toReal_ofNat,Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0),
    Finset.sum_const_zero,add_zero]
  exact lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) f s.toLeft

noncomputable def hilbertInlValue (f : Hilbert V) : Hilbert (V ⊕ E) :=
  ⟨Sum.elim (fun x => f x) (fun _ => 0),memℓp_gen' (sum_inl_extend_le f)⟩

theorem norm_hilbertInlValue_le (f : Hilbert V) : ‖hilbertInlValue (E:=E) f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg f) (sum_inl_extend_le f)

noncomputable def hilbertInl : Hilbert V →L[ℂ] Hilbert (V ⊕ E) :=
  LinearMap.mkContinuous
    { toFun := hilbertInlValue
      map_add' := by
        intro f g
        apply lp.ext
        funext z
        cases z with
        | inl x => rfl
        | inr e => change (0:ℂ) = 0+0; simp
      map_smul' := by
        intro c f
        apply lp.ext
        funext z
        cases z with
        | inl x => rfl
        | inr e => change (0:ℂ) = c • 0; simp }
    1 (fun f => by simpa using norm_hilbertInlValue_le (E:=E) f)

@[simp] theorem hilbertInl_apply_inl (f : Hilbert V) (x : V) :
    hilbertInl (E:=E) f (.inl x) = f x := rfl
@[simp] theorem hilbertInl_apply_inr (f : Hilbert V) (e : E) :
    hilbertInl (E:=E) f (.inr e) = 0 := rfl

theorem sum_inl_restrict_le (f : Hilbert (V ⊕ E)) (s : Finset V) :
    ∑ x ∈ s, ‖f (.inl x)‖ ^ (2:ℝ≥0∞).toReal ≤ ‖f‖ ^ (2:ℝ≥0∞).toReal := by
  classical
  rw [←Finset.sum_image (f := fun z => ‖f z‖ ^ (2:ℝ≥0∞).toReal) Sum.inl_injective.injOn]
  exact lp.sum_rpow_le_norm_rpow (by norm_num) f _

noncomputable def hilbertRestrictInlValue (f : Hilbert (V ⊕ E)) : Hilbert V :=
  ⟨fun x => f (.inl x),memℓp_gen' (sum_inl_restrict_le f)⟩

theorem norm_hilbertRestrictInlValue_le (f : Hilbert (V ⊕ E)) :
    ‖hilbertRestrictInlValue f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg f) (sum_inl_restrict_le f)

noncomputable def hilbertRestrictInl : Hilbert (V ⊕ E) →L[ℂ] Hilbert V :=
  LinearMap.mkContinuous
    { toFun := hilbertRestrictInlValue
      map_add' := by intro f g; apply lp.ext; rfl
      map_smul' := by intro c f; apply lp.ext; rfl }
    1 (fun f => by simpa using norm_hilbertRestrictInlValue_le f)

@[simp] theorem hilbertRestrictInl_apply (f : Hilbert (V ⊕ E)) (x : V) :
    hilbertRestrictInl f x = f (.inl x) := rfl

@[simp] theorem hilbertInl_single [DecidableEq V] [DecidableEq E] (x : V) (c : ℂ) :
    hilbertInl (E:=E) (lp.single 2 x c) = lp.single 2 (.inl x) c := by
  apply lp.ext
  funext z
  cases z <;> simp [lp.single_apply,Pi.single_apply]


end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_Cayley
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

def cayleyLeftIso (S : Finset Λ) (a : Λ) :
    SimpleGraph.mulCayley (S : Set Λ) ≃g SimpleGraph.mulCayley (S : Set Λ) where
  toEquiv := Equiv.mulLeft a
  map_rel_iff' := SimpleGraph.mulCayley_adj_mul_iff_right

def CayleyFolnerInput (Λ : Type u) [Group Λ] : Prop :=
  ¬ FolnerAmenable Λ → ∀ S : Finset Λ, (∀ s ∈ S, s⁻¹ ∈ S) →
    Subgroup.closure (S : Set Λ) = ⊤ → 0 < hV (cayleyBond S)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CayleyInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

noncomputable def rightDefect (A : Finset Λ) (g : Λ) : ℕ :=
  ((A.image (fun x => x * g)) \ A).card

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteOrbitStationary
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology BigOperators

namespace Percolation.BenjaminiSchramm
variable {ι : Type*} [Fintype ι]

def orbitChainStep (K : ι → ι → ℝ) (μ : ι → ℝ) (y : ι) : ℝ := ∑ x, μ x * K x y

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostFan
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V : Type*} {H : SimpleGraph V}

def GhostFan (H : SimpleGraph V) (A B : Set V) (x : V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∃ p : H.Walk x a, ∃ q : H.Walk x b, p.edges.Disjoint q.edges

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostField
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

def ghostHits {V : Type*} (S : Set V) : Set (Set V) := {m | ∃ v ∈ S, v ∈ m}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_HitValue
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open scoped Classical

variable {V : Type*}

noncomputable def hitValue (A U : Set V) : ℝ := if (U ∩ A).Nonempty then 1 else 0
noncomputable def jointHitValue (A T U : Set V) : ℝ :=
  if (U ∩ A).Nonempty ∧ (U ∩ T).Nonempty then 1 else 0

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteMarkovAvg
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]

noncomputable def avg (μ : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, μ x * f x

noncomputable def step (K : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ := avg (K x) f

noncomputable def remainder (K : X → X → ℝ) (a : ℝ) (z x y : X) : ℝ := by
  classical
  exact K x y - if y = z then a else 0

end CriticalPercolation.FiniteMarkov

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Link
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

def link (s b u v : V) : Prop :=
  H.Reachable u v ∨ (H.Reachable u s ∧ H.Reachable b v) ∨
    (H.Reachable u b ∧ H.Reachable s v)

end Wiring
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_FiberValue
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

noncomputable def fiberValue (f : X → Y) (g : X → ℝ) (y : Y) : ℝ :=
  if h : ∃ x, f x = y then g h.choose else 0

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Associated
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
open Filter
open scoped Topology

variable {X : Type*} [Fintype X] [Preorder X]

def Associated (μ : X → ℝ) : Prop :=
  ∀ f g : X → ℝ, Monotone f → Monotone g →
    avg μ f * avg μ g ≤ avg μ (fun x => f x * g x)

noncomputable def compose (K L : X → X → ℝ) (x z : X) : ℝ :=
  ∑ y, K x y * L y z

end CriticalPercolation.FiniteMarkov

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ClosedThin
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def closedThin (w : E → Prop → ℝ) (t : ℝ) (e : E) (b : Prop) : ℝ :=
  (1-t)*w e b + if b then 0 else t

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def Fresh (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) : Prop :=
  ∀ e ∉ read, w e False = 1-p ∧ w e True = p

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedFresh
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

def ClosedFresh (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E) : Prop :=
  ∀ e ∉ used, r e False = (if e ∈ C then 1 else 1-p) ∧
    r e True = (if e ∈ C then 0 else p)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ExposureLaw
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def exposureLaw (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (e : E) (b : A) : ℝ := if e ∈ D then (if b = σ e then 1 else 0) else w e b

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ForceClosed
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*}

noncomputable def forceClosed (w : E → Prop → ℝ) (C : Set E) (e : E) (b : Prop) : ℝ :=
  if e ∈ C then (if b then 0 else 1) else w e b

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

noncomputable def freeze (D : Set E) (σ ω : E → A) : E → A :=
  fun e => if e ∈ D then σ e else ω e

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Divergence
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

noncomputable def divergence (P R : X → ℝ) : ℝ :=
  ∑ x, P x * Real.log (P x / R x)

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

noncomputable def binaryDivergence (r p : ℝ) : ℝ :=
  r * Real.log (r / p) + (1-r) * Real.log ((1-r)/(1-p))

noncomputable def binaryRemainder (p r : ℝ) : ℝ :=
  r * Real.log r + (1-r) * Real.log (1-r) -
    r * Real.log p - (1-r)*Real.log (1-p) - 2*(r-p)^2

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Visits
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation
universe u v w

inductive MarkedTree (E : Type u) (A : Type v) : Type (max u v) where
  | stop : MarkedTree E A
  | ask (e : E) (tag : A) (left right : MarkedTree E A) : MarkedTree E A

namespace MarkedTree
variable {E : Type u} {A : Type v} {B : Type w}

def trace : MarkedTree E A → (E → Bool) → List (E × A)
  | .stop, _ => []
  | .ask e a l r, ω => (e,a) :: if ω e then r.trace ω else l.trace ω

def append : MarkedTree E A → MarkedTree E A → MarkedTree E A
  | .stop, s => s
  | .ask e a l r, s => .ask e a (l.append s) (r.append s)

def sequence : List (MarkedTree E A) → MarkedTree E A
  | [] => .stop
  | t :: ts => t.append (sequence ts)

variable [DecidableEq E]

abbrev Cache (E : Type u) := E → Option Bool

def Compatible (σ : Cache E) (ω : E → Bool) : Prop :=
  ∀ e b, σ e = some b → ω e = b

def cached : MarkedTree E A → Cache E → MarkedTree E A
  | .stop, _ => .stop
  | .ask e a l r, σ =>
    match σ e with
    | some false => l.cached σ
    | some true => r.cached σ
    | none => .ask e a
        (l.cached (Function.update σ e (some false)))
        (r.cached (Function.update σ e (some true)))

def fresh (ω : E → Bool) : Cache E → List (E × A) → List (E × A)
  | _, [] => []
  | σ, x :: xs =>
    let rest := fresh ω (Function.update σ x.1 (some (ω x.1))) xs
    if (σ x.1).isNone then x :: rest else rest

variable [Fintype E]

noncomputable def domain (σ : Cache E) : Finset E :=
  Finset.univ.filter (fun e => (σ e).isSome)

end MarkedTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Select
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree
variable {E A : Type*} [DecidableEq E] [Fintype E]

def select : Finset E → List (E × A) → List (E × A)
  | _, [] => []
  | S, x :: xs =>
      if x.1 ∈ S then select S xs else x :: select (insert x.1 S) xs

end CriticalPercolation.MarkedTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Tagged
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree

variable {E A : Type*}

def Tagged (coord : A → E) : MarkedTree E A → Prop
  | .stop => True
  | .ask e a l r => e = coord a ∧ l.Tagged coord ∧ r.Tagged coord

end CriticalPercolation.MarkedTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_EndpointKernel
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.FiniteEntropy

def endpointKernel (t : ℝ) : ℝ := 16 - 120*t + 240*t^2 - 140*t^3

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Uniform01
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

variable {I : Type*} [Fintype I]

noncomputable def split (i : I) : (I → ℝ) ≃ᵐ (ℝ × ({j : I // j ≠ i} → ℝ)) where
  toEquiv := Equiv.funSplitAt i ℝ
  measurable_toFun := (measurable_pi_apply i).prodMk
    (Measurable.of_eval (fun coordinate => measurable_pi_apply coordinate.val))
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    by_cases h : j = i
    · subst j
      simpa [Equiv.funSplitAt, Equiv.piSplitAt] using measurable_fst
    · simpa [Equiv.funSplitAt, Equiv.piSplitAt, h, Function.comp_def] using
        (measurable_pi_apply (⟨j,h⟩ : {j : I // j ≠ i})).comp measurable_snd

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_FreshSet
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

def freshSet (i : I) (S : Finset {j : I // j ≠ i}) : Set (I → ℝ) :=
  {u | ∀ j ∈ S, u i < u j.val}

end CriticalPercolation.Priority

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

noncomputable def enumeration : List I := Finset.univ.toList

abbrev Order (I : Type*) [Fintype I] := {l : List I // l.Perm (enumeration (I := I))}

noncomputable instance instFintypeOrder : Fintype (Order I) :=
  Fintype.subtype ((enumeration (I := I)).permutations.toFinset) (by
    intro l
    simp [List.mem_permutations])

lemma order_nodup (o : Order I) : o.val.Nodup := by
  exact o.property.nodup_iff.mpr (Finset.nodup_toList _)

lemma mem_order (o : Order I) (i : I) : i ∈ o.val := by
  rw [o.property.mem_iff]
  simp [enumeration]

def cell (o : Order I) : Set (I → ℝ) :=
  {u | o.val.Pairwise fun i j => u i < u j}

lemma order_split (o : Order I) (i : I) :
    ∃ pre post : List I, o.val = pre++i::post ∧ i ∉ pre ∧ i ∉ post := by
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp (mem_order o i)
  refine ⟨pre,post,he,?_,?_⟩
  all_goals
    have hn := order_nodup o
    rw [he, List.nodup_append, List.nodup_cons] at hn
  · exact fun hi => hn.2.2 i hi i (by simp) rfl
  · exact hn.2.1.1

end CriticalPercolation.Priority

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_OrderMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
open FiniteEntropy

variable {I : Type*} [Fintype I]

noncomputable def priorList (o : Order I) (i : I) : List I := (order_split o i).choose
noncomputable def suffix (o : Order I) (i : I) : List I := (order_split o i).choose_spec.choose

def First (o : Order I) (i : I) (S : Finset {j : I // j ≠ i}) : Prop :=
  ∀ j ∈ S, j.val ∉ priorList o i

end CriticalPercolation.Priority

open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_InputMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def bitValue (ω : E → Bool) (e : E) : ℝ := if ω e then 1 else 0

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InterpolationUniform
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation

def interpolationConstant (c ε : ℝ) : ℝ :=
  (4*(16/(2*ε*ε))+6)*(1+Real.log 8+max 0 (Real.log (1/c))) +
    (2*(16/(2*ε*ε))+5)*Real.log 4

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CappedDiscrepancy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

def cappedMass (s m : ℕ) : ℝ := min ((m:ℝ)/s) 1

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceSearch
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch

structure State (E : Type*) where
  opened : Finset E
  read : Finset E

variable {V E : Type*} [DecidableEq E]

 def State.closed (st : State E) (e : E) : State E := ⟨st.opened,insert e st.read⟩
 def State.open (st : State E) (e : E) : State E := ⟨insert e st.opened,insert e st.read⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceIdentity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

 def readSum (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e ∈ st.read, if e∈ω then 1-p else -p

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Relay

def selectedSign (u : ℝ) : ℝ := if 0 ≤ u then -1 else 1

end CriticalPercolation.Relay
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_Weight
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness
open FiniteProduct

variable {E A : Type*} [Fintype E]

def weight (p : ℝ) (b : Prop) : ℝ := if b then p else 1 - p

def closedPivot (F : Set E → Prop) (e : E) (ω : E → Prop) : Prop :=
  ¬ω e ∧ ¬F ω ∧ F (Function.update ω e True)

def pivotal (F : Set E → Prop) (e : E) (ω : Set E) : Prop :=
  F (Function.update ω e True) ∧ ¬ F (Function.update ω e False)

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Link2
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

def link (s b u v : V) : Prop :=
  H.Reachable u v ∨ (H.Reachable u s ∧ H.Reachable b v) ∨
    (H.Reachable u b ∧ H.Reachable s v)

end Wiring

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LevelContactMeasurability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

def finiteSetChoice {E : Type*} (S : Set E) : Finset E :=
  if h : S.Finite then h.toFinset else ∅

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterMassInfinite
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*}

def coefficient (p : ℝ) (ω : Set E) (e : E) : ℝ := if e ∈ ω then -(1-p)/p else 1

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedIncidenceSearch
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

def weightedRead (a : E → ℝ) (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e∈st.read, if e∈ω then a e*(1-p) else -a e*p

def quadraticRead (a : E → ℝ) (st : State E) : ℝ := ∑ e∈st.read, (a e)^2

end CriticalPercolation.IncidenceSearch
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LayerExpectation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

def vertexCount {V : Type*} (S : Set V) : ℝ≥0∞ := ∑' x : V, if x∈S then 1 else 0

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BandScale
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation

def bandScale (L j : ℕ) : ℕ := L ^ (2 ^ j)

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_HonestChoice
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical

namespace CriticalPercolation
variable {Ω I : Type*} [MeasurableSpace Ω]

def firstTest (P : ℕ → Ω → Prop) (ω : Ω) : ℕ :=
  if h : ∃ n, P n ω then Nat.find h else 0

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorScaleChoice
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Classical

namespace CriticalPercolation.Corridor.ScaleChoice

def J : ℝ := 30000
def L : ℕ := 1000000
def contour : ℝ := 1/16
def epsilon : ℝ := contour^4
def delta : ℝ := epsilon/4
def kappa : ℝ := epsilon*delta/(8*(L+1))
def e : ℝ := 1/(200*(L+3))
def eta : ℝ := kappa^2/(32*(Real.log (4/kappa)+1))

end CriticalPercolation.Corridor.ScaleChoice
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DiskWinding
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.DiskWinding

def increment (a b : Real.Angle) : ℝ := (b-a).toReal

end CriticalPercolation.DiskWinding
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EuclideanEllipse
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def diagonal (a b : ℝ) (z : ℂ) : ℂ := ⟨a*z.re,b*z.im⟩

def normalize (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal (1/R) (1/W) ((c : ℂ)⁻¹*z)

def expand (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal R W ((c : ℂ)⁻¹*z)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseMesh
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def diskRadius (W U : ℝ) (p : ℝ×ℝ) : ℝ := W+(U-W)*p.1

def diskNormalize (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  normalize (diskRadius W U p) W (Circle.exp p.2)

def diskExpand (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  expand (diskRadius W U p) W (Circle.exp p.2)

def parameterDisk : Set (ℝ×ℝ) := Set.Icc (0,0) (1,Real.pi)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseAngles
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

def lineAngle (c : Circle) : Real.Angle := ((2*(c : ℂ).arg : ℝ) : Real.Angle)

def boundaryError (phi : ℝ) (c : Circle) : ℝ :=
  (lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)).toReal

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseGrid
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

def gridPoint (N K i k : ℕ) : ℝ×ℝ := ((i : ℝ)/N,(k : ℝ)*Real.pi/K)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_IntegerBoxes
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

def integerPairBox (k : ℕ) : Set (Multiplicative (ℤ×ℤ)) :=
  {t | |(t.toAdd.1 : ℝ)|≤(k:ℝ) ∧ |(t.toAdd.2 : ℝ)|≤(k:ℝ)}

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_FiniteCyclicConstruction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

inductive FiniteCyclicConstruction : (G : Type u) → [Group G] → ℕ → Prop
  | finite (G : Type u) [Group G] [Finite G] : FiniteCyclicConstruction G 0
  | cyclic (G : Type u) [Group G] (e : G ≃* Multiplicative ℤ) :
      FiniteCyclicConstruction G 1
  | extension {G Q : Type u} [Group G] [Group Q] (f : G →* Q)
      (hf : Surjective f) {n m : ℕ}
      (hker : FiniteCyclicConstruction f.ker n)
      (hquot : FiniteCyclicConstruction Q m) : FiniteCyclicConstruction G (n+m)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_LowerCentralFG
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

def lowerFactor (n : ℕ) : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) :=
  ((⊤ : Subgroup G).lowerCentralSeries n).map
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1)))

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ClassTwoRankOne
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G A : Type*} [Group G] [Group A]

def centralCommHom (hc : commutator G≤Subgroup.center G) (a : G) :
    G →* commutator G where
  toFun b := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) (by trivial)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' b d := by
    apply Subtype.ext
    change ⁅a,b*d⁆=⁅a,b⁆*⁅a,d⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := ⊤) (by trivial) (by trivial) : ⁅a,d⁆∈commutator G)
    calc
      ⁅a,b⁆*b*⁅a,d⁆*b⁻¹ = ⁅a,b⁆*(b*⁅a,d⁆)*b⁻¹ := by group
      _ = ⁅a,b⁆*(⁅a,d⁆*b)*b⁻¹ := by rw [Subgroup.mem_center_iff.mp hd b]
      _ = _ := by group

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

variable (Γ : SimpleGraph X)

def coordinates (g : Γ ≃g Γ) : (X → X) × (X → X) := (g,g.symm)

@[instance_reducible] def autTopology : TopologicalSpace (Γ ≃g Γ) :=
  TopologicalSpace.induced (coordinates Γ) inferInstance

local instance instTopologicalSpaceIso_solutions : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def reachBall (o : X) (r : ℕ) : Set X :=
  {x | ∃ p : Γ.Walk o x, p.length ≤ r}

lemma reachBall_add {o x y : X} {r s : ℕ} (hx : x∈reachBall Γ o r)
    (hy : y∈reachBall Γ x s) : y∈reachBall Γ o (r+s) := by
  obtain ⟨p,hp⟩ := hx
  obtain ⟨q,hq⟩ := hy
  exact ⟨p.append q,by simpa using Nat.add_le_add hp hq⟩

lemma reachBall_finite (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    (reachBall Γ o r).Finite := by
  induction r generalizing o with
  | zero =>
    apply (Set.finite_singleton o).subset
    rintro x ⟨p,hp⟩
    cases p with
    | nil => exact Set.mem_singleton o
    | cons h p => simp at hp
  | succ r ih =>
    apply ((Set.finite_singleton o).union ((hl o).biUnion fun x _ => ih x)).subset
    rintro x ⟨p,hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | @cons a b c h p =>
      right
      exact Set.mem_iUnion₂.mpr ⟨b,h,p,by simpa using hp⟩

lemma iso_reachBall (g : Γ ≃g Γ) {o x : X} {r : ℕ}
    (h : x∈reachBall Γ o r) : g x∈reachBall Γ (g o) r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.map g.toHom,by simpa using hp⟩

variable [TopologicalSpace X] [DiscreteTopology X]
local instance instTopologicalSpaceIso_solutions_1 : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def displacement (o : X) (r : ℕ) : Set (Γ ≃g Γ) :=
  {g | g o∈reachBall Γ o r}

lemma reachBall_mono (o : X) : Monotone (reachBall Γ o) := by
  intro r s hrs x hx
  obtain ⟨p,hp⟩ := hx
  exact ⟨p,hp.trans hrs⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_TopologicalClassificationBoundary
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal Pointwise

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def HasCompactOpenVirtuallyNilpotentQuotient : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal,
    let _ := hn
    IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      ∃ N : Subgroup ((Γ ≃g Γ) ⧸ H), Group.IsNilpotent N ∧ N.index≠0

def HasUniformCompactApproximatePowers (K : ℝ) : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ S : Set (Γ ≃g Γ), IsCompact S ∧ IsOpen S ∧ (1 : Γ ≃g Γ)∈S ∧
    S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∀ R : ℕ, ∃ n≥R, IsCompact (S^n) ∧ IsOpen (S^n) ∧
      IsApproximateSubgroup K (S^n)

end GraphTopology
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetBallIndex
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Pointwise

namespace CriticalPercolation.CosetGrowth
variable {A : Type*} [Group A]

def ball (S : Set A) (L : Subgroup A) (n : ℕ) : Set (A ⧸ L) :=
  (QuotientGroup.mk : A → A ⧸ L) '' (S^n)

end CriticalPercolation.CosetGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphQuotientPolynomial
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation
namespace CompactQuotient

def HasSparsePolynomialWordGrowth (A : Type*) [Group A] : Prop :=
  ∃ S : Set A, S.Finite ∧ (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∃ d : ℕ, ∀ R : ℕ, ∃ n≥R, (S^n).ncard≤n^d

end CompactQuotient
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_PolynomialGrowthDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

def HasDegree (S : Finset A) (d : ℕ) : Prop :=
  ∃ C : ℕ, ∀ R : ℕ, ∃ n ≥ R, (S ^ n).card ≤ C * n ^ d

lemma exists_mem_pow (S : Finset A) (hsym : S⁻¹=S)
    {a : A} (ha : a ∈ Subgroup.closure (S : Set A)) : ∃ n : ℕ, a ∈ S^n := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact ⟨1,by simpa using hx⟩
  | one => exact ⟨0,by simp⟩
  | mul x y hx hy ix iy =>
    obtain ⟨m,hm⟩ := ix
    obtain ⟨n,hn⟩ := iy
    refine ⟨m+n,?_⟩
    rw [pow_add]
    exact Finset.mul_mem_mul hm hn
  | inv x hx ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨n,?_⟩
    have hh : x⁻¹ ∈ (S^n)⁻¹ := Finset.inv_mem_inv hn
    simpa only [← inv_pow,hsym] using hh

def HasPolynomialDegree (A : Type*) [Group A] (d : ℕ) : Prop :=
  ∃ S : Set A, S.Finite ∧ (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (S^n).ncard ≤ C*n^d

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_NormalClosureGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

def binaryProducts (g : ℕ → A) : ℕ → Finset A
  | 0 => {1}
  | n+1 => binaryProducts g n ∪ (binaryProducts g n).image (fun x => g n*x)

def boundedConjugates (S F : Finset A) (n : ℕ) : Finset A :=
  (S^n).biUnion (fun g => F.image (MulAut.conj g))

def conjugateStage (S F : Finset A) (n : ℕ) : Subgroup A :=
  Subgroup.closure (boundedConjugates S F n : Set A)

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ConjugationMatrixGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def latticeCharacter (w : ι → ℂ) : Multiplicative (ι → ℤ) →* Multiplicative ℂ where
  toFun x := Multiplicative.ofAdd (w ⬝ᵥ fun i => ((Multiplicative.toAdd x i : ℤ) : ℂ))
  map_one' := by change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0; congr 1; simp
  map_mul' x y := by
    change Multiplicative.ofAdd (w ⬝ᵥ fun i => (((Multiplicative.toAdd x i +
      Multiplicative.toAdd y i) : ℤ) : ℂ)) = Multiplicative.ofAdd (_+_)
    congr 1
    simp [dotProduct,Finset.sum_add_distrib,mul_add]

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CharacteristicNilpotentCore
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in

def powerSubgroup (A : Type*) [Group A] (k : ℕ) : Subgroup A :=
  Subgroup.closure (Set.range (fun x : A => x^k))

omit [DecidableEq A] [DecidableEq B] in
instance powerSubgroup_characteristic (k : ℕ) : (powerSubgroup A k).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro f
  rw [powerSubgroup,MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  exact ⟨f x,map_pow f x k |>.symm⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_WordLengthGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

structure WordGeometry (A : Type*) [Group A] where
  generators : Finset A
  one_mem : (1:A)∈generators
  inv_eq : generators⁻¹=generators
  generates : Subgroup.closure (generators:Set A)=⊤

namespace WordGeometry
variable (W : WordGeometry A)
abbrev ball (n : ℕ) := W.generators^n

lemma exists_mem_ball (a : A) : ∃ n, a∈W.ball n :=
  SparseGrowth.exists_mem_pow W.generators W.inv_eq (by rw [W.generates]; trivial)

def length (a : A) : ℕ := Nat.find (W.exists_mem_ball a)

lemma mem_ball_length (a : A) : a∈W.ball (W.length a) := Nat.find_spec (W.exists_mem_ball a)

lemma length_le_iff {a : A} {n : ℕ} : W.length a≤n ↔ a∈W.ball n := by
  constructor
  · intro h
    exact Finset.pow_subset_pow_right W.one_mem h (W.mem_ball_length a)
  · intro h; exact Nat.find_min' (W.exists_mem_ball a) h

lemma length_mul_le (a b : A) : W.length (a*b)≤W.length a+W.length b := by
  apply W.length_le_iff.mpr
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a,W.mem_ball_length a,b,W.mem_ball_length b,rfl⟩

lemma length_inv (a : A) : W.length a⁻¹=W.length a := by
  have hl (b : A) : W.length b⁻¹≤W.length b := by
    apply W.length_le_iff.mpr
    have hh := Finset.inv_mem_inv (W.mem_ball_length b)
    simpa [ball,←inv_pow,W.inv_eq] using hh
  exact le_antisymm (hl a) (by simpa using hl a⁻¹)

def cutoff (R : ℕ) (a : A) : ℝ := max 0 (2*(R:ℝ)-(W.length a:ℝ))

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_CayleyPoincare
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A] [DecidableEq A]

def energy (S F : Finset A) (u : A → ℝ) : ℝ :=
  ∑ x∈F, ∑ s∈S, (u (x*s)-u x)^2

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_HarmonicFunctionSpace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {X : Type*}

def vanishingSubspace (D : Submodule ℝ (X → ℝ)) (F : Set X) : Submodule ℝ D where
  carrier := {u | ∀ x∈F, (u:X → ℝ) x=0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by intro u v hu hv x hx; change u.val x+v.val x=0; rw [hu x hx,hv x hx,add_zero]
  smul_mem' := by intro a u hu x hx; change a*u.val x=0; rw [hu x hx,mul_zero]

def squareMass (F : Finset X) (u : X → ℝ) : ℝ := ∑ x∈F, (u x)^2

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_CayleyCaccioppoli
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

namespace WordGeometry
variable (W : WordGeometry A)

def IsHarmonic (u : A → ℝ) : Prop := ∀ x, (∑ s∈W.generators, (u x-u (x*s)))=0

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_LazyWalkHilbert
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]
abbrev RegularHilbert (A : Type*) := lp (fun _ : A => ℝ) 2

lemma translate_mem (a : A) (f : RegularHilbert A) :
    Memℓp (fun x => f (a*x)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mpr
  have hf : Summable (fun x : A => ‖f x‖ ^ (2:ENNReal).toReal) :=
    (lp.memℓp f).summable (by norm_num)
  exact (Equiv.mulLeft a).summable_iff.mpr hf

def translateVector (a : A) (f : RegularHilbert A) : RegularHilbert A :=
  ⟨fun x => f (a*x), translate_mem a f⟩

def regularLinearEquiv (a : A) : RegularHilbert A ≃ₗ[ℝ] RegularHilbert A where
  toFun := translateVector a⁻¹
  invFun := translateVector a
  left_inv f := by
    apply Subtype.ext
    funext x
    change f (a⁻¹*(a*x))=f x
    rw [inv_mul_cancel_left]
  right_inv f := by
    apply Subtype.ext
    funext x
    change f (a*(a⁻¹*x))=f x
    rw [mul_inv_cancel_left]
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

def regular (a : A) : RegularHilbert A ≃ₗᵢ[ℝ] RegularHilbert A :=
  (regularLinearEquiv a).isometryOfInner (by
    intro f g
    change (∑' x, inner ℝ (f (a⁻¹*x)) (g (a⁻¹*x))) = ∑' x, inner ℝ (f x) (g x)
    exact (Equiv.mulLeft a⁻¹).tsum_eq (fun x : A => inner ℝ (f x) (g x)))

@[simp] lemma regular_apply (a : A) (f : RegularHilbert A) (x : A) :
    regular a f x=f (a⁻¹*x) := rfl
@[simp] lemma regular_one (f : RegularHilbert A) : regular 1 f=f := by ext x; simp
@[simp] lemma regular_mul (a b : A) (f : RegularHilbert A) :
    regular (a*b) f=regular a (regular b f) := by ext x; simp [mul_assoc]

namespace WordGeometry
variable (W : WordGeometry A)
def walkAverage : RegularHilbert A →ₗ[ℝ] RegularHilbert A :=
  (W.generators.card:ℝ)⁻¹ • ∑ s∈W.generators, (regular s).toLinearEquiv.toLinearMap

def lazyWalk : RegularHilbert A →ₗ[ℝ] RegularHilbert A :=
  (1/2:ℝ) • (LinearMap.id+W.walkAverage)

def walkEnergy (f : RegularHilbert A) : ℝ := inner ℝ f (f-W.lazyWalk f)

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_LazyWalkProbability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def walkState (n : ℕ) : RegularHilbert A :=
  (W.lazyWalk^n) (lp.single 2 (1:A) (1:ℝ))

@[simp] lemma walkState_zero : W.walkState 0=lp.single 2 (1:A) (1:ℝ) := rfl

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_ProjectedWalkFunctions
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def projectedFunction (f : RegularHilbert A) (t : A) (x : A) : ℝ :=
  inner ℝ (regular x f-f) (regular t f-f) / (4*(W.generators.card:ℝ)*W.walkEnergy f)

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_WordBallPacking
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def around (a : A) (r : ℕ) : Finset A := (W.ball r).image (fun x => a*x)

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GeneralizedGramSpectrum
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix InnerProductSpace

namespace CriticalPercolation.HarmonicAnalysis
variable {ι : Type*} [Fintype ι]

def matrixQuadratic (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ M *ᵥ v

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_FunctionGramMatrix
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {ι X : Type*} [Fintype ι]

def functionGram (F : Finset X) (v : ι → X → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ x∈F, v i x*v j x

def functionCombination (v : ι → X → ℝ) (a : ι → ℝ) : X → ℝ :=
  fun x => ∑ i, a i*v i x

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_PolynomialHarmonicSpace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def harmonicSpace : Submodule ℝ (A → ℝ) where
  carrier := {u | W.IsHarmonic u}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro u v hu hv x
    change (∑ s∈W.generators, ((u x+v x)-(u (x*s)+v (x*s))))=0
    simp_rw [show ∀ s:A, (u x+v x)-(u (x*s)+v (x*s))=(u x-u (x*s))+(v x-v (x*s)) by intro s; ring]
    rw [Finset.sum_add_distrib,hu x,hv x,add_zero]
  smul_mem' := by
    intro c u hu x
    change (∑ s∈W.generators, (c*u x-c*u (x*s)))=0
    simp_rw [←mul_sub]
    rw [←Finset.mul_sum,hu x,mul_zero]

def HasPolynomialGrowth (k : ℕ) (u : A → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x∈W.ball n, |u x| ≤ C*((n:ℝ)+1)^k

def polynomialGrowthSpace (k : ℕ) : Submodule ℝ (A → ℝ) where
  carrier := {u | W.HasPolynomialGrowth k u}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro u v ⟨C,hC,hu⟩ ⟨D,hD,hv⟩
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro n x hx
    change |u x+v x| ≤ _
    calc
      _ ≤ |u x|+|v x| := abs_add_le _ _
      _ ≤ C*((n:ℝ)+1)^k+D*((n:ℝ)+1)^k := add_le_add (hu n x hx) (hv n x hx)
      _ = _ := by ring
  smul_mem' := by
    rintro c u ⟨C,hC,hu⟩
    refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,?_⟩
    intro n x hx
    change |c*u x| ≤ _
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu n x hx) (abs_nonneg _)

def polynomialHarmonicSpace (k : ℕ) : Submodule ℝ (A → ℝ) :=
  W.harmonicSpace ⊓ W.polynomialGrowthSpace k

lemma polynomial_growth_iff_length (k : ℕ) (u : A → ℝ) :
    W.HasPolynomialGrowth k u ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |u x| ≤ C*((W.length x:ℝ)+1)^k := by
  constructor
  · rintro ⟨C,hC,hu⟩
    exact ⟨C,hC,fun x => hu _ _ (W.mem_ball_length x)⟩
  · rintro ⟨C,hC,hu⟩
    refine ⟨C,hC,?_⟩
    intro n x hx
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (W.length_le_iff.mpr hx) 1

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_HarmonicLinearQuotient
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
universe u
variable {A : Type u} [Group A] (W : WordGeometry A)

def translateFunction (a : A) (u : A → ℝ) : A → ℝ := fun x => u (a⁻¹*x)

lemma translate_harmonic (a : A) {u : A → ℝ} (hu : W.IsHarmonic u) :
    W.IsHarmonic (translateFunction a u) := by
  intro x
  simpa only [translateFunction,mul_assoc] using hu (a⁻¹*x)

lemma translate_polynomial_growth (a : A) (k : ℕ) {u : A → ℝ}
    (hu : W.HasPolynomialGrowth k u) : W.HasPolynomialGrowth k (translateFunction a u) := by
  obtain ⟨C,hC,hu⟩ := (W.polynomial_growth_iff_length k u).mp hu
  apply (W.polynomial_growth_iff_length k _).mpr
  refine ⟨C*((W.length a:ℝ)+1)^k,by positivity,?_⟩
  intro x
  have hl := W.length_mul_le a⁻¹ x
  rw [W.length_inv] at hl
  have hl' : (W.length (a⁻¹*x):ℝ)≤(W.length a:ℝ)+(W.length x:ℝ) := by exact_mod_cast hl
  change |u (a⁻¹*x)|≤_
  calc
    _ ≤ C*((W.length (a⁻¹*x):ℝ)+1)^k := hu _
    _ ≤ C*(((W.length a:ℝ)+1)*((W.length x:ℝ)+1))^k := by
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) (W.length a),Nat.cast_nonneg (α:=ℝ) (W.length x)]
    _ = _ := by rw [mul_pow]; ring

def harmonicTranslation (k : ℕ) (a : A) :
    W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k where
  toFun u := ⟨translateFunction a u, W.translate_harmonic a u.property.1,
    W.translate_polynomial_growth a k u.property.2⟩
  invFun u := ⟨translateFunction a⁻¹ u, W.translate_harmonic a⁻¹ u.property.1,
    W.translate_polynomial_growth a⁻¹ k u.property.2⟩
  left_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  right_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  map_add' u v := rfl
  map_smul' c u := rfl

@[simp] lemma harmonicTranslation_apply (k : ℕ) (a : A) (u : W.polynomialHarmonicSpace k) (x : A) :
    (W.harmonicTranslation k a u:A → ℝ) x=(u:A → ℝ) (a⁻¹*x) := rfl

def harmonicRepresentation (k : ℕ) : A →*
    (W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k) where
  toFun := W.harmonicTranslation k
  map_one' := by ext u x; simp
  map_mul' a b := by ext u x; simp [mul_assoc]

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_InvariantBlockSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def subspaceRepresentation (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) : G →* (W ≃ₗ[K] W) where
  toFun g := (ρ g).ofSubmodules W W (hW g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def quotientRepresentation (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) : G →* ((V ⧸ W) ≃ₗ[K] (V ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (ρ g) (hW g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp

@[simp] lemma subspaceRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) (g : G) (w : W) :
    (subspaceRepresentation ρ W hW g w : V)=ρ g w := rfl

@[simp] lemma quotientRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) (g : G) (v : V) :
    quotientRepresentation ρ W hW g (Submodule.Quotient.mk v)=Submodule.Quotient.mk (ρ g v) := rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FiniteSubspaceOrbit
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

@[instance_reducible] def subspaceAction (ρ : G →* (V ≃ₗ[K] V)) : MulAction G (Submodule K V) where
  smul g W := W.map (ρ g).toLinearMap
  one_smul W := by
    change W.map (ρ 1).toLinearMap=W
    rw [map_one]
    exact W.map_id
  mul_smul g h W := by
    change W.map (ρ (g*h)).toLinearMap=(W.map (ρ h).toLinearMap).map (ρ g).toLinearMap
    rw [map_mul]
    exact (Submodule.map_comp _ _ W)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_LocalProjectiveTopology
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable (K V : Type*) [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

abbrev NZ := {v : V // v≠0}

instance nzMulAction : MulAction Kˣ (NZ V) where
  smul a v := ⟨(a:K) • (v:V),smul_ne_zero a.ne_zero v.property⟩
  one_smul v := Subtype.ext (one_smul K (v:V))
  mul_smul a b v := Subtype.ext (mul_smul (a:K) (b:K) (v:V))

instance nzContinuousConstSMul : ContinuousConstSMul Kˣ (NZ V) :=
  ⟨fun _ => (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

abbrev Space := Quotient (MulAction.orbitRel Kˣ (NZ V))
def point (v : NZ V) : Space K V := Quotient.mk _ v

lemma point_surjective : Surjective (point K V) := Quotient.mk_surjective

variable {K V}

variable (K V)

instance spaceSecondCountable [ProperSpace K] [FiniteDimensional K V] :
    SecondCountableTopology (Space K V) := by
  let : ProperSpace V := FiniteDimensional.proper K V
  exact ContinuousConstSMul.secondCountableTopology

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_CompactInvariantMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Finset MeasureTheory
open scoped Classical Topology BigOperators Pointwise ENNReal NNReal BoundedContinuousFunction

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

lemma orbit_wordBall_nonempty (S : Finset G) (h1 : (1:G)∈S) (n : ℕ) : (S^n).Nonempty :=
  ⟨1,Finset.one_mem_pow h1⟩

def orbitAverage (T : Finset G) (hT : T.Nonempty) (x : X) : ProbabilityMeasure X :=
  ⟨((T.card:ℝ≥0∞)⁻¹) • ∑ g∈T, Measure.dirac (g • x), by
    constructor
    simp only [Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),
      Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Finset.card_ne_zero.mpr hT)) (by simp)⟩

end CriticalPercolation.SparseGrowth

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

def integralInvariantSubgroup (μ : ProbabilityMeasure X) : Subgroup G where
  carrier := {g | ∀ f : X →ᵇ ℝ, (∫ y, f (g • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X)}
  one_mem' := by intro f; simp
  mul_mem' := by
    intro a b ha hb f
    let fa : X →ᵇ ℝ := f.compContinuous ⟨fun y => a • y,continuous_const_smul a⟩
    calc
      _ = ∫ y, fa (b • y) ∂(μ:Measure X) := by simp only [fa,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,mul_smul]
      _ = ∫ y, fa y ∂(μ:Measure X) := hb fa
      _ = ∫ y, f y ∂(μ:Measure X) := ha f
  inv_mem' := by
    intro a ha f
    let fi : X →ᵇ ℝ := f.compContinuous ⟨fun y => a⁻¹ • y,continuous_const_smul _⟩
    have hh := ha fi
    simpa only [fi,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,inv_smul_smul] using hh.symm

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_LocalProjectiveAction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

def nzImage (a : V ≃L[K] V) (v : NZ V) : NZ V :=
  ⟨a v,fun he => v.property (a.injective (he.trans a.map_zero.symm))⟩

def action (a : V ≃L[K] V) : Space K V → Space K V :=
  Quotient.map (nzImage a) (by
    intro v w h
    obtain ⟨c,hc⟩ := h
    refine ⟨c,Subtype.ext ?_⟩
    change (c:K) • a (w:V)=a (v:V)
    rw [←map_smul]
    exact congrArg a (congrArg Subtype.val hc))

@[simp] lemma action_point (a : V ≃L[K] V) (v : NZ V) :
    action a (point K V v)=point K V (nzImage a v) := rfl

@[simp] lemma action_one (q : Space K V) : action (1:V ≃L[K] V) q=q := by
  obtain ⟨v,rfl⟩ := point_surjective K V q
  rfl

lemma action_mul (a b : V ≃L[K] V) (q : Space K V) :
    action (a*b) q=action a (action b q) := by
  obtain ⟨v,rfl⟩ := point_surjective K V q
  rfl

variable {G : Type*} [Group G]
@[instance_reducible]
def mulAction (ρ : G →* (V ≃L[K] V)) : MulAction G (Space K V) where
  smul g q := action (ρ g) q
  one_smul q := by change action (ρ 1) q=q; rw [map_one,action_one]
  mul_smul g h q := by change action (ρ (g*h)) q=action (ρ g) (action (ρ h) q); rw [map_mul,action_mul]

instance spaceMeasurable : MeasurableSpace (Space K V) := borel _
instance spaceBorel : BorelSpace (Space K V) := ⟨rfl⟩

def subspace (W : Submodule K V) : Set (Space K V) :=
  point K V '' {v : NZ V | (v:V)∈W}

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_LocalFurstenbergBound
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module Metric TopologicalSpace
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

lemma equiv_operator_ne_zero [Nontrivial V] (a : V ≃L[K] V) :
    a.toContinuousLinearMap≠0 := by
  intro he
  obtain ⟨x,hx⟩ := exists_ne (0:V)
  apply hx
  apply a.injective
  have hh := congrArg (fun f : V →L[K] V => f x) he
  exact hh.trans a.map_zero.symm

variable (t : K) (ht : 1<‖t‖)
include ht
lemma exists_shell_scalar {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : ∃ c : K, c≠0 ∧ 1/‖t‖≤‖c • x‖ ∧ ‖c • x‖≤1 := by
  obtain ⟨c,hc,hlt,hle,_⟩ := rescale_to_shell ht zero_lt_one hx
  exact ⟨c,hc,hle,hlt.le⟩

noncomputable def shellScalar {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : K := Classical.choose (exists_shell_scalar t ht x hx)

variable [Nontrivial V]
def normalized (a : V ≃L[K] V) : V →L[K] V :=
  shellScalar t ht a.toContinuousLinearMap (equiv_operator_ne_zero a) • a.toContinuousLinearMap

def shell (U : Type*) [NormedAddCommGroup U] : Set U := {x | 1/‖t‖≤‖x‖ ∧ ‖x‖≤1}

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FullSpanAlternative
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def FullSpan (ρ : G →* (V ≃ₗ[K] V)) : Prop :=
  Submodule.span K (Set.range (fun g => (ρ g).toLinearMap))=⊤

def StrongFullSpan (ρ : G →* (V ≃ₗ[K] V)) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → FullSpan (ρ.comp H.subtype)

end CriticalPercolation.LinearGrowth
namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V]
variable [NormedSpace K V] [ProperSpace K] [FiniteDimensional K V] [Group G]

def continuousRepresentation (ρ : G →* (V ≃ₗ[K] V)) : G →* (V ≃L[K] V) where
  toFun g := (ρ g).toContinuousLinearEquiv
  map_one' := by ext x; change ρ 1 x=x; rw [map_one]; rfl
  map_mul' g h := by ext x; change ρ (g*h) x=ρ g (ρ h x); rw [map_mul]; rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FgMatrixRing
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable (ρ : G →* GL n R) (D : Subalgebra ℤ R) (hD : ∀ g i j, ρ g i j∈D)

def liftMatrix (g : G) : Matrix n n D := fun i j => ⟨ρ g i j,hD g i j⟩

@[simp] lemma liftMatrix_map (g : G) :
    (D.val.toRingHom.mapMatrix) (liftMatrix ρ D hD g)=(ρ g).val := rfl

lemma liftMatrix_one : liftMatrix ρ D hD 1=1 := by
  apply Matrix.map_injective (f := D.val) Subtype.val_injective
  change D.val.toRingHom.mapMatrix (liftMatrix ρ D hD 1)=D.val.toRingHom.mapMatrix 1
  rw [map_one]
  change (ρ 1).val=1
  rw [map_one]
  rfl

lemma liftMatrix_mul (g h : G) : liftMatrix ρ D hD (g*h)=liftMatrix ρ D hD g*liftMatrix ρ D hD h := by
  apply Matrix.map_injective (f := D.val) Subtype.val_injective
  change D.val.toRingHom.mapMatrix (liftMatrix ρ D hD (g*h))=D.val.toRingHom.mapMatrix _
  rw [map_mul]
  change (ρ (g*h)).val=(ρ g).val*(ρ h).val
  rw [map_mul]
  rfl

def liftMatrixGroup : G →* GL n D where
  toFun g := ⟨liftMatrix ρ D hD g,liftMatrix ρ D hD g⁻¹,
    by rw [←liftMatrix_mul,mul_inv_cancel,liftMatrix_one],
    by rw [←liftMatrix_mul,inv_mul_cancel,liftMatrix_one]⟩
  map_one' := Units.ext (liftMatrix_one ρ D hD)
  map_mul' g h := Units.ext (liftMatrix_mul ρ D hD g h)

@[simp] lemma liftMatrixGroup_map (g : G) :
    Matrix.GeneralLinearGroup.map D.val.toRingHom (liftMatrixGroup ρ D hD g)=ρ g := by
  apply Units.ext
  rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ProjectivelyPeriodicSchur
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Group G]

def linearMatrixEquiv : (V ≃ₗ[K] V) ≃* GL (Fin (finrank K V)) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toMulEquiv)

def conjugationRepresentation (ρ : G →* (V ≃ₗ[K] V)) : G →* (End K V ≃ₗ[K] End K V) where
  toFun g := (ρ g).conj
  map_one' := by ext f x; simp only [map_one]; rfl
  map_mul' g h := by ext f x; simp only [map_mul]; rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ProjectivePeriodicity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module

namespace CriticalPercolation.LinearGrowth
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def continuousEndAlgEquiv : End ℂ V ≃ₐ[ℂ] (V →L[ℂ] V) :=
  AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap rfl (fun _ _ => rfl)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_AbsoluteMatrixSpan
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K L T G n : Type*} [Field K] [Field L] [Field T] [Group G]
variable [Fintype n] [DecidableEq n]

def matrixRepresentation (ρ : G →* GL n K) : G →* ((n → K) ≃ₗ[K] (n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp] lemma matrixRepresentation_apply (ρ : G →* GL n K) (g : G) (v : n → K) :
    matrixRepresentation ρ g v=(ρ g).val.mulVec v := rfl

def matrixFlatten : Matrix n n K ≃ₗ[K] (n × n → K) where
  toFun M p := M p.1 p.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def FullMatrixSpan (ρ : G →* GL n K) : Prop :=
  Submodule.span K (Set.range (fun g (p : n×n) => ρ g p.1 p.2))=⊤

def StrongFullMatrixSpan (ρ : G →* GL n K) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → FullMatrixSpan (ρ.comp H.subtype)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetSparseGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def ball (K : Subgroup A) (S : Set A) (n : ℕ) : Set (A ⧸ K) :=
  (QuotientGroup.mk : A → A ⧸ K) '' S^n

def HasDegree (K : Subgroup A) (S : Set A) (d : ℕ) : Prop :=
  (∀ n, (ball K S n).Finite) ∧ ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (ball K S n).ncard≤C*n^d

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetBounded
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def Bounded (S T : Set A) : Prop := ∃ n : ℕ, T⊆S^n

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetNormalClosure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def boundedConjugates (S F : Set A) (n : ℕ) : Set A :=
  {x | ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x}

def conjugateStage (S F : Set A) (n : ℕ) : Subgroup A :=
  Subgroup.closure (boundedConjugates S F n : Set A)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetTransfer
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def subgroupCosetEmbedding (K H : Subgroup A) : H ⧸ K.subgroupOf H ↪ A ⧸ K where
  toFun := Quotient.map' Subtype.val (by
    intro a b h
    simpa only [QuotientGroup.leftRel_apply,Subgroup.mem_subgroupOf,Subgroup.coe_mul,Subgroup.coe_inv] using h)
  inj' := Quotient.ind₂' (by
    intro a b h
    change (QuotientGroup.mk a.val : A ⧸ K)=QuotientGroup.mk b.val at h
    apply QuotientGroup.eq.mpr
    change a.val⁻¹*b.val∈K
    exact QuotientGroup.eq.mp h)
@[simp] lemma subgroupCosetEmbedding_mk (K H : Subgroup A) (h : H) :
    subgroupCosetEmbedding K H (QuotientGroup.mk h)=QuotientGroup.mk h.val := rfl

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
structure Geometry (X : Type*) where
  graph : SimpleGraph X
  connected : graph.Connected
  locallyFinite : ∀ x, (graph.neighborSet x).Finite
  transitive : ∀ x y, ∃ g : graph ≃g graph, g x=y
  root : X

namespace Geometry
variable {X : Type*} (W : Geometry X)
abbrev Aut := W.graph ≃g W.graph

def around (x : X) (r : ℕ) : Finset X := (GraphTopology.reachBall_finite W.graph W.locallyFinite x r).toFinset
abbrev ball (r : ℕ) := W.around W.root r

@[simp] lemma mem_around {x y : X} {r : ℕ} :
    y∈W.around x r ↔ y∈GraphTopology.reachBall W.graph x r := (GraphTopology.reachBall_finite W.graph W.locallyFinite x r).mem_toFinset

lemma around_mono (x : X) : Monotone (W.around x) := by
  intro r s h y hy
  exact W.mem_around.mpr (GraphTopology.reachBall_mono W.graph x h (W.mem_around.mp hy))
lemma ball_mono : Monotone W.ball := W.around_mono W.root

lemma mem_around_add {x y z : X} {r s : ℕ} (hy : y∈W.around x r) (hz : z∈W.around y s) :
    z∈W.around x (r+s) :=
  W.mem_around.mpr (GraphTopology.reachBall_add W.graph (W.mem_around.mp hy) (W.mem_around.mp hz))

lemma aut_around_image (g : W.Aut) (x : X) (r : ℕ) :
    (W.around x r).image g=W.around (g x) r := by
  ext y
  constructor
  · intro hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact W.mem_around.mpr (GraphTopology.iso_reachBall W.graph g (W.mem_around.mp hz))
  · intro hy
    refine Finset.mem_image.mpr ⟨g.symm y,?_,g.apply_symm_apply y⟩
    apply W.mem_around.mpr
    simpa using GraphTopology.iso_reachBall W.graph g.symm (W.mem_around.mp hy)

def length (x : X) : ℕ := W.graph.dist W.root x
lemma mem_ball_length (x : X) : x∈W.ball (W.length x) := by
  obtain ⟨p,_,hp⟩ := W.connected.exists_path_of_dist W.root x
  exact W.mem_around.mpr ⟨p,hp.le⟩
lemma length_le_iff {x : X} {n : ℕ} : W.length x≤n ↔ x∈W.ball n := by
  constructor
  · intro h; exact W.ball_mono h (W.mem_ball_length x)
  · intro h
    obtain ⟨p,hp⟩ := W.mem_around.mp h
    exact (SimpleGraph.dist_le p).trans hp

lemma aut_length_le (g : W.Aut) (x : X) : W.length (g x)≤W.length (g W.root)+W.length x := by
  apply W.length_le_iff.mpr
  apply W.mem_around_add (W.mem_ball_length (g W.root))
  rw [←W.aut_around_image]
  exact Finset.mem_image.mpr ⟨x,W.mem_ball_length x,rfl⟩

def neighbors (x : X) : Finset X := (W.locallyFinite x).toFinset
@[simp] lemma mem_neighbors {x y : X} : y∈W.neighbors x ↔ W.graph.Adj x y := (W.locallyFinite x).mem_toFinset
lemma neighbors_image (g : W.Aut) (x : X) : (W.neighbors x).image g=W.neighbors (g x) := by
  ext y
  simp only [Finset.mem_image,W.mem_neighbors]
  constructor
  · rintro ⟨z,hz,rfl⟩; exact g.map_adj_iff.mpr hz
  · intro h; exact ⟨g.symm y,by simpa using g.symm.map_adj_iff.mpr h,g.apply_symm_apply y⟩
abbrev degree := (W.neighbors W.root).card

def energy (F : Finset X) (u : X → ℝ) := ∑ x∈F, ∑ y∈W.neighbors x, (u y-u x)^2

def IsHarmonic (u : X → ℝ) : Prop := ∀ x, (∑ y∈W.neighbors x, (u x-u y))=0

def cutoff (R : ℕ) (x : X) : ℝ := max 0 (2*(R:ℝ)-(W.length x:ℝ))

end Geometry
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteActionAverage
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

def restrictedPermutation (B : Set X) (hB : ∀ g : G, ∀ x∈B, g • x∈B) (g : G) : Equiv.Perm B where
  toFun x := ⟨g • x.val,hB g x.val x.property⟩
  invFun x := ⟨g⁻¹ • x.val,hB g⁻¹ x.val x.property⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

def restrictionHom (B : Set X) (hB : ∀ g : G, ∀ x∈B, g • x∈B) : G →* Equiv.Perm B where
  toFun := restrictedPermutation B hB
  map_one' := by ext x; exact one_smul G x.val
  map_mul' g h := by ext x; exact mul_smul g h x.val

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousAverage
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry

variable {X : Type*} (W : Geometry X)

abbrev Stab := MulAction.stabilizer W.Aut W.root

def frame (x : X) : W.Aut := (W.transitive W.root x).choose
lemma action_transitive : ∀ x y : X, ∃ g : W.Aut, g • x=y := W.transitive

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry

variable {X : Type*} (W : Geometry X)

def HasDegree (d : ℕ) : Prop := ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (W.ball n).card≤C*n^d

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

structure Presentation (A : Type*) [Group A] where
  K : Subgroup A
  S : Set A
  one_mem : (1:A)∈S
  inv_eq : S⁻¹=S
  generates : Subgroup.closure S=⊤
  left_stable : (K:Set A)*S⊆S

namespace Presentation
variable (P : Presentation A)
abbrev X := A ⧸ P.K
abbrev projection (a : A) : P.X := QuotientGroup.mk a
abbrev root : P.X := P.projection 1

def graph : SimpleGraph P.X where
  Adj x y := x≠y ∧ ∃ g : A, ∃ s∈P.S, P.projection g=x ∧ P.projection (g*s)=y
  symm := ⟨by
    rintro x y ⟨hne,g,s,hs,rfl,rfl⟩
    refine ⟨hne.symm,g*s,s⁻¹,?_,rfl,?_⟩
    · rw [←P.inv_eq]; exact Set.inv_mem_inv.mpr hs
    · simp⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma adj_mk_iff (g : A) (y : P.X) :
    P.graph.Adj (P.projection g) y ↔ P.projection g≠y ∧ ∃ s∈P.S, P.projection (g*s)=y := by
  constructor
  · rintro ⟨hne,h,s,hs,hh,he⟩
    have hk : g⁻¹*h∈P.K := QuotientGroup.eq.mp hh.symm
    refine ⟨hne,(g⁻¹*h)*s,P.left_stable (Set.mul_mem_mul hk hs),?_⟩
    simpa only [mul_assoc,mul_inv_cancel_left] using he
  · rintro ⟨hne,s,hs,he⟩; exact ⟨hne,g,s,hs,rfl,he⟩

lemma smul_adj_iff (a : A) (x y : P.X) :
    P.graph.Adj (a • x) (a • y) ↔ P.graph.Adj x y := by
  have hf (b : A) {x y : P.X} (h : P.graph.Adj x y) :
      P.graph.Adj (b • x) (b • y) := by
    obtain ⟨hne,g,s,hs,rfl,rfl⟩ := h
    refine ⟨fun he => hne (smul_left_cancel b he),b*g,s,hs,rfl,?_⟩
    change P.projection ((b*g)*s)=P.projection (b*(g*s))
    rw [mul_assoc]
  constructor
  · intro h; simpa using hf a⁻¹ h
  · exact hf a

def actionAut (a : A) : P.graph ≃g P.graph where
  toEquiv := MulAction.toPerm a
  map_rel_iff' := P.smul_adj_iff a _ _
def actionHom : A →* (P.graph ≃g P.graph) where
  toFun := P.actionAut
  map_one' := by ext x; exact one_smul A x
  map_mul' a b := by ext x; exact mul_smul a b x
@[simp] lemma actionAut_mk (a b : A) : P.actionAut a (P.projection b)=P.projection (a*b) := rfl

lemma reachable_mk (a : A) : P.graph.Reachable P.root (P.projection a) := by
  have ha : a∈Subgroup.closure P.S := P.generates.symm ▸ Subgroup.mem_top a
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    by_cases he : P.root=P.projection a
    · rw [←he]
    · apply SimpleGraph.Adj.reachable
      exact ⟨he,1,a,ha,rfl,by simp⟩
  | one => exact .refl _
  | mul a b _ _ ha hb =>
    have hh := hb.map (P.actionAut a).toHom
    change P.graph.Reachable (P.projection (a*1)) (P.projection (a*b)) at hh
    simp only [mul_one] at hh
    exact ha.trans hh
  | inv a _ ha =>
    have hh := ha.symm.map (P.actionAut a⁻¹).toHom
    change P.graph.Reachable (P.projection (a⁻¹*a)) (P.projection (a⁻¹*1)) at hh
    simpa using hh
lemma connected : P.graph.Connected := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact (P.reachable_mk a).symm.trans (P.reachable_mk b)

lemma neighbors_subset (a : A) : P.graph.neighborSet (P.projection a)⊆
    (fun x : P.X => a • x) '' ball P.K P.S 1 := by
  intro y hy
  obtain ⟨hne,s,hs,rfl⟩ := (P.adj_mk_iff a y).mp hy
  exact ⟨P.projection s,⟨s,by simpa using hs,rfl⟩,rfl⟩
lemma locallyFinite (hf : (ball P.K P.S 1).Finite) : ∀ x, (P.graph.neighborSet x).Finite := by
  intro x
  induction x using Quotient.inductionOn with | _ a =>
    exact (hf.image (fun x : P.X => a • x)).subset (P.neighbors_subset a)
lemma transitive (x y : P.X) : ∃ g : P.graph ≃g P.graph, g x=y := by
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      exact ⟨P.actionAut (b*a⁻¹),by simp⟩
def geometry (hf : (ball P.K P.S 1).Finite) : HomogeneousAnalysis.Geometry P.X :=
  ⟨P.graph,P.connected,P.locallyFinite hf,P.transitive,P.root⟩

end Presentation
end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousPolynomialSpace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {A : Type*} (W : Geometry A)

def harmonicSpace : Submodule ℝ (A → ℝ) where
  carrier := {u | W.IsHarmonic u}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro u v hu hv x
    change (∑ s∈W.neighbors x, ((u x+v x)-(u s+v s)))=0
    simp_rw [show ∀ s:A, (u x+v x)-(u s+v s)=(u x-u s)+(v x-v s) by intro s; ring]
    rw [Finset.sum_add_distrib,hu x,hv x,add_zero]
  smul_mem' := by
    intro c u hu x
    change (∑ s∈W.neighbors x, (c*u x-c*u s))=0
    simp_rw [←mul_sub]
    rw [←Finset.mul_sum,hu x,mul_zero]

def HasPolynomialGrowth (k : ℕ) (u : A → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x∈W.ball n, |u x| ≤ C*((n:ℝ)+1)^k

def polynomialGrowthSpace (k : ℕ) : Submodule ℝ (A → ℝ) where
  carrier := {u | W.HasPolynomialGrowth k u}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro u v ⟨C,hC,hu⟩ ⟨D,hD,hv⟩
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro n x hx
    change |u x+v x| ≤ _
    calc
      _ ≤ |u x|+|v x| := abs_add_le _ _
      _ ≤ C*((n:ℝ)+1)^k+D*((n:ℝ)+1)^k := add_le_add (hu n x hx) (hv n x hx)
      _ = _ := by ring
  smul_mem' := by
    rintro c u ⟨C,hC,hu⟩
    refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,?_⟩
    intro n x hx
    change |c*u x| ≤ _
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu n x hx) (abs_nonneg _)

def polynomialHarmonicSpace (k : ℕ) : Submodule ℝ (A → ℝ) :=
  W.harmonicSpace ⊓ W.polynomialGrowthSpace k

lemma polynomial_growth_iff_length (k : ℕ) (u : A → ℝ) :
    W.HasPolynomialGrowth k u ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |u x| ≤ C*((W.length x:ℝ)+1)^k := by
  constructor
  · rintro ⟨C,hC,hu⟩
    exact ⟨C,hC,fun x => hu _ _ (W.mem_ball_length x)⟩
  · rintro ⟨C,hC,hu⟩
    refine ⟨C,hC,?_⟩
    intro n x hx
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (W.length_le_iff.mpr hx) 1

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_FiniteHilbert
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
open HarmonicAnalysis

variable {X : Type*}

def finiteHilbert : Submodule ℝ (RegularHilbert X) where
  carrier := {f | (Function.support (fun x => f x)).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    apply (hf.union hg).subset
    intro x hx
    by_contra hn
    have hx' : f x+g x≠0 := hx
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hx' (by rw [hn.1,hn.2]; ring)
  smul_mem' := by
    intro c f hf
    apply hf.subset
    intro x hx
    by_contra hn
    have hx' : c*f x≠0 := hx
    simp only [Function.mem_support,not_not] at hn
    exact hx' (by rw [hn,mul_zero])

abbrev FH (X : Type*) := ↥(finiteHilbert (X:=X))
namespace FH
instance instCoeFunForallReal : CoeFun (FH X) (fun _ => X → ℝ) := ⟨fun f => (f.val : X → ℝ)⟩
@[ext] lemma ext {f g : FH X} (h : ∀ x, f x=g x) : f=g :=
  Subtype.ext (by ext x; exact h x)

@[simp] lemma zero_apply (x : X) : (0 : FH X) x=0 := rfl
@[simp] lemma add_apply (f g : FH X) (x : X) : (f+g) x=f x+g x := rfl
@[simp] lemma sub_apply (f g : FH X) (x : X) : (f-g) x=f x-g x := rfl
@[simp] lemma smul_apply (c : ℝ) (f : FH X) (x : X) : (c • f) x=c*f x := rfl

def support (f : FH X) : Finset X := f.property.toFinset
@[simp] lemma mem_support (f : FH X) (x : X) : x∈f.support ↔ f x≠0 :=
  f.property.mem_toFinset

def ofFunction (f : X → ℝ) (hf : (Function.support f).Finite) : FH X :=
  ⟨⟨f,(memℓp_zero_iff.mpr hf).of_exponent_ge (by norm_num)⟩,hf⟩
@[simp] lemma ofFunction_apply (f : X → ℝ) (hf : (Function.support f).Finite) (x : X) :
    ofFunction f hf x=f x := rfl

def delta (x : X) : FH X :=
  ofFunction (Pi.single x 1) ((Set.finite_singleton x).subset (by
    intro y hy
    by_contra hn
    simp only [Set.mem_singleton_iff] at hn
    exact hy (by simp [hn])))
@[simp] lemma delta_apply (x y : X) : delta x y=if y=x then 1 else 0 := by
  simp [delta,Pi.single_apply,eq_comm]

def transportLinear (g : Equiv.Perm X) : FH X ≃ₗ[ℝ] FH X where
  toFun f := ofFunction (fun x => f (g.symm x)) (by
    have he : Function.support (fun x => f (g.symm x))=g '' Function.support (fun x => f x) := by
      ext x; simp [Function.mem_support]
    rw [he]; exact f.property.image g)
  invFun f := ofFunction (fun x => f (g x)) (by
    have he : Function.support (fun x => f (g x))=g.symm '' Function.support (fun x => f x) := by
      ext x; simp [Function.mem_support]
    rw [he]; exact f.property.image g.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

def transport (g : Equiv.Perm X) : FH X ≃ₗᵢ[ℝ] FH X :=
  (transportLinear g).isometryOfInner (by
    intro f h
    change (∑' x, inner ℝ (f (g.symm x)) (h (g.symm x)))=∑' x, inner ℝ (f x) (h x)
    exact g.symm.tsum_eq (fun x => inner ℝ (f x) (h x)))
@[simp] lemma transport_apply (g : Equiv.Perm X) (f : FH X) (x : X) :
    transport g f x=f (g.symm x) := rfl
@[simp] lemma transport_one (f : FH X) : transport 1 f=f := by ext x; rfl
@[simp] lemma transport_mul (a b : Equiv.Perm X) (f : FH X) :
    transport (a*b) f=transport a (transport b f) := by ext x; rfl
@[simp] lemma transport_delta (g : Equiv.Perm X) (x : X) :
    transport g (delta x)=delta (g x) := by
  ext y
  simp only [transport_apply,delta_apply]
  congr 1
  exact propext g.symm_apply_eq

lemma summable (f : FH X) : Summable (fun x => f x) := summable_of_hasFiniteSupport f.property

def mass : FH X →ₗ[ℝ] ℝ where
  toFun f := ∑' x, f x
  map_add' f g := by simp only [add_apply]; exact Summable.tsum_add f.summable g.summable
  map_smul' c f := by simp only [smul_apply,RingHom.id_apply,smul_eq_mul,tsum_mul_left]
@[simp] lemma mass_delta (x : X) : mass (delta x)=1 := by
  change (∑' y, delta x y)=1
  simp only [delta_apply]
  exact tsum_ite_eq _ _

end FH
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphWalkOperator
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma inverse_neighbor_sum (f : FH X) :
    (Function.support (fun y => (W.degree:ℝ)⁻¹*∑ z∈W.neighbors y, f z)).Finite := by
  apply (f.support.biUnion W.neighbors).finite_toSet.subset
  intro y hy
  have hz : (∑ z∈W.neighbors y, f z)≠0 := by
    intro h; apply hy; change (W.degree:ℝ)⁻¹*(∑ z∈W.neighbors y, f z)=0; rw [h,mul_zero]
  obtain ⟨z,hz,hfz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact Finset.mem_biUnion.mpr ⟨z,(f.mem_support z).mpr hfz,
    W.mem_neighbors.mpr (W.mem_neighbors.mp hz).symm⟩

def averaging : FH X →ₗ[ℝ] FH X where
  toFun f := FH.ofFunction (fun x => (W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y)
    (W.inverse_neighbor_sum f)
  map_add' f g := by
    ext x
    simp only [FH.ofFunction_apply,FH.add_apply,Finset.sum_add_distrib,mul_add]
  map_smul' c f := by
    ext x
    simp only [FH.ofFunction_apply,FH.smul_apply,←Finset.mul_sum,RingHom.id_apply]
    ring

def lazyWalk : FH X →ₗ[ℝ] FH X := (1/2:ℝ) • (LinearMap.id+W.averaging)
def walkEnergy (f : FH X) : ℝ := inner ℝ f (f-W.lazyWalk f)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphWalkProbability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def walkFeature (n : ℕ) (x : X) : FH X := (W.lazyWalk^n) (FH.delta x)
abbrev walkState (n : ℕ) := W.walkFeature n W.root
@[simp] lemma walkFeature_zero (x : X) : W.walkFeature 0 x=FH.delta x := rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphProjectedFunctions
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def projectedFunction (n : ℕ) (t x : X) : ℝ :=
  inner ℝ (W.walkFeature n x-W.walkState n) (W.walkFeature n t-W.walkState n) /
    (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n))
end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphHarmonicLinear
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def translateFunction (a : W.Aut) (u : X → ℝ) : X → ℝ := fun x => u (a.symm x)
lemma translate_harmonic (a : W.Aut) {u : X → ℝ} (hu : W.IsHarmonic u) :
    W.IsHarmonic (W.translateFunction a u) := by
  intro x
  have h := hu (a.symm x)
  rw [←W.neighbors_image a.symm x,Finset.sum_image] at h
  · exact h
  · exact fun b hb c hc he => a.symm.injective he
lemma translate_polynomial_growth (a : W.Aut) (k : ℕ) {u : X → ℝ}
    (hu : W.HasPolynomialGrowth k u) : W.HasPolynomialGrowth k (W.translateFunction a u) := by
  obtain ⟨C,hC,hu⟩ := (W.polynomial_growth_iff_length k u).mp hu
  apply (W.polynomial_growth_iff_length k _).mpr
  refine ⟨C*((W.length (a.symm W.root):ℝ)+1)^k,by positivity,?_⟩
  intro x
  have hl := W.aut_length_le a.symm x
  have hl' : (W.length (a.symm x):ℝ)≤(W.length (a.symm W.root):ℝ)+(W.length x:ℝ) := by exact_mod_cast hl
  change |u (a.symm x)|≤_
  calc
    _ ≤ C*((W.length (a.symm x):ℝ)+1)^k := hu _
    _ ≤ C*(((W.length (a.symm W.root):ℝ)+1)*((W.length x:ℝ)+1))^k := by
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) (W.length (a.symm W.root)),Nat.cast_nonneg (α:=ℝ) (W.length x)]
    _ = _ := by rw [mul_pow]; ring

def harmonicTranslation (k : ℕ) (a : W.Aut) :
    W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k where
  toFun u := ⟨W.translateFunction a u,W.translate_harmonic a u.property.1,
    W.translate_polynomial_growth a k u.property.2⟩
  invFun u := ⟨W.translateFunction a.symm u,W.translate_harmonic a.symm u.property.1,
    W.translate_polynomial_growth a.symm k u.property.2⟩
  left_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  right_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  map_add' u v := rfl
  map_smul' c u := rfl
@[simp] lemma harmonicTranslation_apply (k : ℕ) (a : W.Aut) (u : W.polynomialHarmonicSpace k) (x : X) :
    (W.harmonicTranslation k a u:X → ℝ) x=(u:X → ℝ) (a.symm x) := rfl

def harmonicRepresentation (k : ℕ) : W.Aut →*
    (W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k) where
  toFun := W.harmonicTranslation k
  map_one' := by ext u x; rfl
  map_mul' a b := by ext u x; rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_GraphRelativeGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def vertexStabilizer (o : X) : Subgroup (Γ ≃g Γ) where
  carrier := {g | g o=o}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a (b o)=o; rw [hb,ha]
  inv_mem' := by
    intro a ha
    change a.symm o=o
    calc
      a.symm o = a.symm (a o) := congrArg a.symm ha.symm
      _ = o := a.symm_apply_apply o

@[simp] lemma mem_vertexStabilizer (o : X) (a : Γ ≃g Γ) : a∈vertexStabilizer Γ o ↔ a o=o := Iff.rfl

def stabilizerCosetEmbedding (o : X) : ((Γ ≃g Γ) ⧸ vertexStabilizer Γ o) ↪ X where
  toFun := Quotient.lift (s:=QuotientGroup.leftRel (vertexStabilizer Γ o)) (fun g : Γ ≃g Γ => g o) (by
    intro a b hab
    have hab' : a⁻¹*b ∈ vertexStabilizer Γ o := (QuotientGroup.leftRel_apply).mp hab
    change a.symm (b o)=o at hab'
    have hh := congrArg a hab'
    simpa using hh.symm)
  inj' := Quotient.ind₂' (by
    intro a b h
    apply QuotientGroup.eq.mpr
    change a.symm (b o)=o
    change a o=b o at h
    rw [←h]
    exact a.symm_apply_apply o)
@[simp] lemma stabilizerCosetEmbedding_mk (o : X) (g : Γ ≃g Γ) :
    stabilizerCosetEmbedding Γ o (QuotientGroup.mk g)=g o := rfl

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ProbeEntropy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open CriticalPercolation.FiniteEntropy

namespace ProbeEntropy

open ProbeTree

noncomputable def totalQueries (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, weight p h t l * (queries t l : ℝ)

noncomputable def totalMarks (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, weight p h t l * (marks t l : ℝ)

noncomputable def treeDivergence (p q h : ℝ) (t : ProbeTree) : ℝ :=
  divergence (weight p h t) (weight q h t)

@[simp] theorem totalQueries_done (p h : ℝ) (b : Bool) : totalQueries p h (.done b) = 0 := by
  simp [totalQueries,queries]

@[simp] theorem totalMarks_done (p h : ℝ) (b : Bool) : totalMarks p h (.done b) = 0 := by
  simp [totalMarks,marks]

end ProbeEntropy
end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakFiniteEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {E : Type*}

def finiteBondPattern (F : Finset E) (σ : Set E) : Set (Set E) :=
  {ω | ∀ e ∈ F, (e ∈ ω)=(e ∈ σ)}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PrefixMaximumBootstrap
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

def prefixMaximum (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n+1)).sup' ⟨0,by simp⟩ h

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalLayerConvolution
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

def expAbsLayerKernel (a : ℝ) (i : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-a*|(i : ℝ)|))

end Percolation.BenjaminiSchramm

end

end OAI
end


